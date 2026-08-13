import Unifysl.GeneralLogic.ProofTheory.BasicSequentCalculus
import Unifysl.GeneralLogic.ProofTheory.BasicLogicEquiv
import Unifysl.MinimumLogic.ProofTheory.TheoryOfSequentCalculus

/-!
Coq inventory from `MinimumLogic/ProofTheory/Minimum.v`:
- Definition/classes:
  `multi_imp`, `DerivableProvable`, `MinimumAxiomatization`,
  `MinimumSequentCalculus`, `Derivable1Provable`, `ProvableDerivable`,
  `EquivProvable`, `ProvableDerivable1`.
  In the 8.20 branch these are renamed/exposed as
  `DerivableFromProvable`, `Derivable1FromProvable`,
  `ProvableFromDerivable`, `ProvableFromDerivable1`, with generated-style
  field names `__derivable_provable`, `__derivable1_provable`,
  `__provable_derivable`, `__provable_derivable1`,
  `__logic_equiv_provable`; `MinimumDeduction` is also added.
- Axiomatization-derived lemmas:
  `provable_impp_refl`, `provable_impp_refl'`, `aux_minimun_rule00`,
  `aux_minimun_theorem00`, `aux_minimun_rule01`, `aux_minimun_rule02`,
  `aux_minimun_theorem01`, `aux_minimun_theorem02`,
  `aux_minimun_theorem03`, `aux_minimun_theorem04`,
  `provable_impp_arg_switch`, `provable_impp_trans`,
  `solve_impp_trans` (master), `provables_impp_trans` (8.20).
- `multi_imp` lemmas:
  `provable_multi_imp_shrink`, `provable_multi_imp_arg_switch1`,
  `provable_multi_imp_arg_switch2`, `provable_multi_imp_weaken`,
  `provable_multi_imp_split`, `provable_add_multi_imp_left_head`,
  `provable_add_multi_imp_left_tail`, `provable_multi_imp_modus_ponens`.
- Conversions:
  `Axiomatization2SequentCalculus_GammaPD`,
  `Axiomatization2SequentCalculus_fwSC`,
  `Axiomatization2SequentCalculus_minSC`,
  `Axiomatization2SequentCalculus_bSC`,
  `SequentCalculus2Axiomatization_minAX`,
  `SequentCalculus2Axiomatization_GammaDP`,
  `Axiomatization2Deduction_GammaED1`,
  `Deduction2Axiomatization_GammaEP`.
- Sequent rules:
  `deduction_weaken0`, `deduction_impp_elim`, `deduction_theorem`,
  `deduction_theorem_multi_imp`, `derivable_impp_refl`,
  `deduction_left_impp_intros`, `derivable_axiom1`, `derivable_axiom2`,
  `derivable_modus_ponens`, `deduction_impp_trans`,
  `deduction_impp_arg_switch`, `provable_right`.
- Transformations:
  `Provable2Derivable`, `Provable2Derivable_Normal`,
  `Derivable2Provable`, `Derivable2Provable_Normal`,
  `Provable2Derivable1`, `Provable2Derivable1_Normal`,
  `Provable2Equiv`, `Provable2Equiv_Normal`,
  `Derivable12Equiv`, `Derivable12Equiv_Normal`,
  `Derivable12Provable`, `Derivable12Provable_Normal`.
-/

universe u

namespace Unifysl

def multi_imp {L : Language.{u}} [MinimumLanguage L]
    (xs : List (@Language.expr L)) (y : @Language.expr L) : @Language.expr L :=
  xs.foldr impp y

class DerivableProvable (L : Language.{u}) [MinimumLanguage L]
    (GammaP : Provable L) (GammaD : Derivable L) : Prop where
  derivable_provable :
    forall (Phi : context (L := L)) (y : @Language.expr L),
      @Derivable.derivable L GammaD Phi y <->
        exists xs : List (@Language.expr L),
          List.Forall (fun x => Phi x) xs /\
            @Provable.provable L GammaP (multi_imp xs y)

class MinimumAxiomatization (L : Language.{u}) [MinimumLanguage L]
    (Gamma : Provable L) : Prop where
  modus_ponens :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma x ->
          @Provable.provable L Gamma y
  axiom1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (y ⟶ x))
  axiom2 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y ⟶ z) ⟶ (x ⟶ y) ⟶ (x ⟶ z))

class MinimumSequentCalculus (L : Language.{u}) [MinimumLanguage L]
    (Gamma : Derivable L) : Prop where
  deduction_modus_ponens :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L Gamma Phi x ->
        @Derivable.derivable L Gamma Phi (x ⟶ y) ->
          @Derivable.derivable L Gamma Phi y
  deduction_impp_intros :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L Gamma (Phi ;; x) y ->
        @Derivable.derivable L Gamma Phi (x ⟶ y)

class MinimumDeduction (L : Language.{u}) [MinimumLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1s_modus_ponens :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (y ⟶ z) ->
        @Derivable1.derivable1 L GammaD1 x y ->
          @Derivable1.derivable1 L GammaD1 x z
  derivable1s_impp_intros :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x ⟶ y) z ->
        @Derivable1.derivable1 L GammaD1 x (y ⟶ z)
  derivable1_impp_refl :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (y ⟶ y)
  derivable1_axiom1 :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (y ⟶ x)
  derivable1_axiom2 :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ (x ⟶ z))

class Derivable1Provable (L : Language.{u}) [MinimumLanguage L]
    (GammaP : Provable L) (GammaD : Derivable1 L) : Prop where
  derivable1_provable :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD x y <->
        @Provable.provable L GammaP (impp x y)

class ProvableDerivable (L : Language.{u}) (GammaP : Provable L)
    (GammaD : Derivable L) : Prop where
  provable_derivable :
    forall x : @Language.expr L,
      @Provable.provable L GammaP x <->
        @Derivable.derivable L GammaD (empty_context (L := L)) x

class EquivProvable (L : Language.{u}) [MinimumLanguage L]
    (GammaP : Provable L) (GammaL : LogicEquiv L) : Prop where
  logic_equiv_provable :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaL x y <->
        @Provable.provable L GammaP (impp x y) /\
          @Provable.provable L GammaP (impp y x)

class ProvableDerivable1 (L : Language.{u}) [MinimumLanguage L]
    (GammaP : Provable L) (GammaD : Derivable1 L) : Prop where
  provable_derivable1 :
    forall x : @Language.expr L,
      @Provable.provable L GammaP x <->
        @Derivable1.derivable1 L GammaD (impp x x) x

abbrev DerivableFromProvable (L : Language.{u}) [MinimumLanguage L]
    (GammaP : Provable L) (GammaD : Derivable L) : Prop :=
  DerivableProvable L GammaP GammaD

abbrev Derivable1FromProvable (L : Language.{u}) [MinimumLanguage L]
    (GammaP : Provable L) (GammaD : Derivable1 L) : Prop :=
  Derivable1Provable L GammaP GammaD

abbrev ProvableFromDerivable (L : Language.{u}) (GammaP : Provable L)
    (GammaD : Derivable L) : Prop :=
  ProvableDerivable L GammaP GammaD

abbrev ProvableFromDerivable1 (L : Language.{u}) [MinimumLanguage L]
    (GammaP : Provable L) (GammaD : Derivable1 L) : Prop :=
  ProvableDerivable1 L GammaP GammaD

theorem __derivable_provable {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [GammaDP : DerivableFromProvable L GammaP GammaD]
    (Phi : context (L := L)) (y : @Language.expr L) :
    @Derivable.derivable L GammaD Phi y <->
      exists xs : List (@Language.expr L),
        List.Forall (fun x => Phi x) xs /\
          @Provable.provable L GammaP (multi_imp xs y) :=
  DerivableProvable.derivable_provable (L := L) (GammaP := GammaP)
    (GammaD := GammaD) Phi y

theorem __derivable1_provable {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD : Derivable1 L]
    [GammaD1P : Derivable1FromProvable L GammaP GammaD]
    (x y : @Language.expr L) :
    @Derivable1.derivable1 L GammaD x y <->
      @Provable.provable L GammaP (impp x y) :=
  Derivable1Provable.derivable1_provable (L := L) (GammaP := GammaP)
    (GammaD := GammaD) x y

theorem __provable_derivable {L : Language.{u}} [GammaP : Provable L]
    [GammaD : Derivable L] [GammaPD : ProvableFromDerivable L GammaP GammaD]
    (x : @Language.expr L) :
    @Provable.provable L GammaP x <->
      @Derivable.derivable L GammaD (empty_context (L := L)) x :=
  ProvableDerivable.provable_derivable (L := L) (GammaP := GammaP)
    (GammaD := GammaD) x

theorem __logic_equiv_provable {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaE : LogicEquiv L]
    [GammaEP : EquivProvable L GammaP GammaE] (x y : @Language.expr L) :
    @LogicEquiv.logic_equiv L GammaE x y <->
      @Provable.provable L GammaP (impp x y) /\
        @Provable.provable L GammaP (impp y x) :=
  EquivProvable.logic_equiv_provable (L := L) (GammaP := GammaP)
    (GammaL := GammaE) x y

theorem __provable_derivable1 {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD : Derivable1 L]
    [GammaPD1 : ProvableFromDerivable1 L GammaP GammaD]
    (x : @Language.expr L) :
    @Provable.provable L GammaP x <->
      @Derivable1.derivable1 L GammaD (impp x x) x :=
  ProvableDerivable1.provable_derivable1 (L := L) (GammaP := GammaP)
    (GammaD := GammaD) x

theorem provables_modus_ponens {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L] [minAX : MinimumAxiomatization L Gamma]
    (x y : @Language.expr L) :
    @Provable.provable L Gamma (x ⟶ y) ->
      @Provable.provable L Gamma x -> @Provable.provable L Gamma y :=
  MinimumAxiomatization.modus_ponens (Gamma := Gamma) x y

theorem provable_axiom1 {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L] [minAX : MinimumAxiomatization L Gamma]
    (x y : @Language.expr L) :
    @Provable.provable L Gamma (x ⟶ (y ⟶ x)) :=
  MinimumAxiomatization.axiom1 (Gamma := Gamma) x y

theorem provable_axiom2 {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L] [minAX : MinimumAxiomatization L Gamma]
    (x y z : @Language.expr L) :
    @Provable.provable L Gamma ((x ⟶ y ⟶ z) ⟶ (x ⟶ y) ⟶ (x ⟶ z)) :=
  MinimumAxiomatization.axiom2 (Gamma := Gamma) x y z

theorem derivables_modus_ponens {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Derivable L] [minSC : MinimumSequentCalculus L Gamma]
    (Phi : context (L := L)) (x y : @Language.expr L) :
    @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi (x ⟶ y) ->
        @Derivable.derivable L Gamma Phi y :=
  MinimumSequentCalculus.deduction_modus_ponens Phi x y

theorem derivables_impp_intros {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Derivable L] [minSC : MinimumSequentCalculus L Gamma]
    (Phi : context (L := L)) (x y : @Language.expr L) :
    @Derivable.derivable L Gamma (Phi ;; x) y ->
      @Derivable.derivable L Gamma Phi (x ⟶ y) :=
  MinimumSequentCalculus.deduction_impp_intros Phi x y

theorem derivable1s_modus_ponens {L : Language.{u}} [MinimumLanguage L]
    [GammaD1 : Derivable1 L] [minD1 : MinimumDeduction L GammaD1]
    (x y z : @Language.expr L) :
    @Derivable1.derivable1 L GammaD1 x (y ⟶ z) ->
      @Derivable1.derivable1 L GammaD1 x y ->
        @Derivable1.derivable1 L GammaD1 x z :=
  MinimumDeduction.derivable1s_modus_ponens x y z

theorem derivable1s_impp_intros {L : Language.{u}} [MinimumLanguage L]
    [GammaD1 : Derivable1 L] [minD1 : MinimumDeduction L GammaD1]
    (x y z : @Language.expr L) :
    @Derivable1.derivable1 L GammaD1 (x ⟶ y) z ->
      @Derivable1.derivable1 L GammaD1 x (y ⟶ z) :=
  MinimumDeduction.derivable1s_impp_intros x y z

theorem derivable1_impp_refl {L : Language.{u}} [MinimumLanguage L]
    [GammaD1 : Derivable1 L] [minD1 : MinimumDeduction L GammaD1]
    (x y : @Language.expr L) :
    @Derivable1.derivable1 L GammaD1 x (y ⟶ y) :=
  MinimumDeduction.derivable1_impp_refl x y

theorem derivable1_axiom1 {L : Language.{u}} [MinimumLanguage L]
    [GammaD1 : Derivable1 L] [minD1 : MinimumDeduction L GammaD1]
    (x y : @Language.expr L) :
    @Derivable1.derivable1 L GammaD1 x (y ⟶ x) :=
  MinimumDeduction.derivable1_axiom1 x y

theorem derivable1_axiom2 {L : Language.{u}} [MinimumLanguage L]
    [GammaD1 : Derivable1 L] [minD1 : MinimumDeduction L GammaD1]
    (x y z : @Language.expr L) :
    @Derivable1.derivable1 L GammaD1
      (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ (x ⟶ z)) :=
  MinimumDeduction.derivable1_axiom2 x y z

private theorem list_forall_impl {A : Type u} {P Q : A -> Prop}
    (h : forall x, P x -> Q x) :
    forall {xs : List A}, List.Forall P xs -> List.Forall Q xs
  | [], List.Forall.nil => List.Forall.nil
  | _ :: _, List.Forall.cons hx hxs =>
      List.Forall.cons (h _ hx) (list_forall_impl h hxs)

private theorem list_forall_mem_self {A : Type u} :
    forall xs : List A, List.Forall (fun x => x ∈ xs) xs
  | [] => List.Forall.nil
  | x :: xs =>
      List.Forall.cons (List.Mem.head xs)
        (list_forall_impl (fun _ hz => List.Mem.tail x hz)
          (list_forall_mem_self xs))

private theorem list_forall_mem {A : Type u} {P : A -> Prop} :
    forall {xs : List A}, List.Forall P xs -> forall x, x ∈ xs -> P x
  | [], List.Forall.nil, x, hx => by cases hx
  | _ :: _, List.Forall.cons hx hxs, x, hmem => by
      cases hmem with
      | head => exact hx
      | tail _ htail => exact list_forall_mem hxs x htail

section DerivableRulesFromAxiomatization

variable {L : Language.{u}} [MinimumLanguage L]
variable [Gamma : Provable L] [minAX : MinimumAxiomatization L Gamma]

theorem provable_impp_refl :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ x) := by
  intro x
  have h2 := MinimumAxiomatization.axiom2 (Gamma := Gamma) x (x ⟶ x) x
  have h10 := MinimumAxiomatization.axiom1 (Gamma := Gamma) x (x ⟶ x)
  have h11 := MinimumAxiomatization.axiom1 (Gamma := Gamma) x x
  have h :=
    MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h2 h10
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h h11

theorem provable_impp_refl' :
    forall x y : @Language.expr L,
      x = y -> @Provable.provable L Gamma (x ⟶ y) := by
  intro x y h
  subst y
  exact provable_impp_refl x

theorem aux_minimun_rule00 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma x ->
        @Provable.provable L Gamma (y ⟶ x) := by
  intro x y hx
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _
    (MinimumAxiomatization.axiom1 (Gamma := Gamma) x y) hx

theorem aux_minimun_theorem00 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((y ⟶ z) ⟶ (x ⟶ y) ⟶ (x ⟶ z)) := by
  intro x y z
  have h :=
    MinimumAxiomatization.axiom2 (Gamma := Gamma) x y z
  have h0 :=
    aux_minimun_rule00
      ((x ⟶ y ⟶ z) ⟶ (x ⟶ y) ⟶ (x ⟶ z)) (y ⟶ z) h
  have h1 :=
    MinimumAxiomatization.axiom1 (Gamma := Gamma) (y ⟶ z) x
  have h2 :=
    MinimumAxiomatization.axiom2 (Gamma := Gamma)
      (y ⟶ z) (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ (x ⟶ z))
  have h3 := MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h2 h0
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h3 h1

theorem aux_minimun_rule01 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma ((z ⟶ x) ⟶ (z ⟶ y)) := by
  intro x y z h
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _
    (aux_minimun_theorem00 z x y) h

theorem aux_minimun_rule02 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (y ⟶ z) ->
          @Provable.provable L Gamma (x ⟶ z) := by
  intro x y z hxy hyz
  have h := MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _
    (aux_minimun_theorem00 x y z) hyz
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h hxy

theorem aux_minimun_theorem01 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ z) ⟶ (x ⟶ y ⟶ z)) := by
  intro x y z
  exact aux_minimun_rule01 z (y ⟶ z) x
    (MinimumAxiomatization.axiom1 (Gamma := Gamma) z y)

theorem aux_minimun_theorem02 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (x ⟶ y) ⟶ y) := by
  intro x y
  have h := MinimumAxiomatization.axiom2 (Gamma := Gamma) (x ⟶ y) x y
  have hrefl := provable_impp_refl (x ⟶ y)
  have h1 := MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h hrefl
  have h2 := aux_minimun_rule01 ((x ⟶ y) ⟶ x) ((x ⟶ y) ⟶ y) x h1
  have h3 := MinimumAxiomatization.axiom1 (Gamma := Gamma) x (x ⟶ y)
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h2 h3

theorem aux_minimun_theorem03 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (y ⟶ (x ⟶ y ⟶ z) ⟶ (x ⟶ z)) := by
  intro x y z
  exact aux_minimun_rule02 y ((y ⟶ z) ⟶ z)
    ((x ⟶ y ⟶ z) ⟶ (x ⟶ z))
    (aux_minimun_theorem02 y z)
    (aux_minimun_theorem00 x (y ⟶ z) z)

theorem aux_minimun_theorem04 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ x ⟶ y) ⟶ x ⟶ y) := by
  intro x y
  have h := MinimumAxiomatization.axiom2 (Gamma := Gamma) x (x ⟶ y) y
  have h0 := aux_minimun_theorem02 x y
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h h0

theorem provable_impp_arg_switch :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y ⟶ z) ⟶ (y ⟶ x ⟶ z)) := by
  intro x y z
  have hleft : @Provable.provable L Gamma
      ((x ⟶ y ⟶ z) ⟶ (y ⟶ x ⟶ y ⟶ z)) :=
    MinimumAxiomatization.axiom1 (Gamma := Gamma) (x ⟶ y ⟶ z) y
  have hright : @Provable.provable L Gamma
      ((y ⟶ x ⟶ y ⟶ z) ⟶ (y ⟶ x ⟶ z)) := by
    have h := MinimumAxiomatization.axiom2 (Gamma := Gamma)
      y (x ⟶ y ⟶ z) (x ⟶ z)
    exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h
      (aux_minimun_theorem03 x y z)
  exact aux_minimun_rule02 (x ⟶ y ⟶ z) (y ⟶ x ⟶ y ⟶ z)
    (y ⟶ x ⟶ z) hleft hright

theorem provable_impp_trans :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ (y ⟶ z) ⟶ (x ⟶ z)) := by
  intro x y z
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _
    (provable_impp_arg_switch (y ⟶ z) (x ⟶ y) (x ⟶ z))
    (aux_minimun_theorem00 x y z)

theorem solve_impp_trans :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (y ⟶ z) ->
          @Provable.provable L Gamma (x ⟶ z) := by
  intro x y z hxy hyz
  have h := MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _
    (provable_impp_trans x y z) hxy
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ h hyz

theorem provables_impp_trans :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (y ⟶ z) ->
          @Provable.provable L Gamma (x ⟶ z) :=
  solve_impp_trans

end DerivableRulesFromAxiomatization

section DerivableRulesFromMinimumDeduction

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaD1 : Derivable1 L]
variable [bD : BasicDeduction L GammaD1]
variable [minD1 : MinimumDeduction L GammaD1]

theorem aux_minimun_rule10 :
    forall x : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (x ⟶ x ⟶ x) := by
  intro x
  exact derivable1s_impp_intros x x (x ⟶ x) (derivable1_refl (x ⟶ x))

theorem aux_minimun_rule11 :
    forall x : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 ((x ⟶ x) ⟶ x) x := by
  intro x
  exact derivable1s_modus_ponens ((x ⟶ x) ⟶ x) (x ⟶ x) x
    (derivable1_refl ((x ⟶ x) ⟶ x))
    (derivable1_impp_refl ((x ⟶ x) ⟶ x) x)

theorem aux_minimun_rule12 :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (z ⟶ z) (x ⟶ y) ->
        @Derivable1.derivable1 L GammaD1 x y := by
  intro x y z h
  have hxzz : @Derivable1.derivable1 L GammaD1 x (z ⟶ z) :=
    derivable1_impp_refl x z
  have hxy : @Derivable1.derivable1 L GammaD1 x (x ⟶ y) :=
    derivable1_trans x (z ⟶ z) (x ⟶ y) hxzz h
  exact derivable1s_modus_ponens x x y hxy (derivable1_refl x)

end DerivableRulesFromMinimumDeduction

private theorem derivable1_from_self_imp_source
    {L : Language.{u}} [MinimumLanguage L]
    [GammaD1 : Derivable1 L] [bD : BasicDeduction L GammaD1]
    [minD1 : MinimumDeduction L GammaD1]
    (f x : @Language.expr L) :
    @Derivable1.derivable1 L GammaD1 ((f ⟶ f) ⟶ x) x := by
  exact derivable1s_modus_ponens ((f ⟶ f) ⟶ x) (f ⟶ f) x
    (derivable1_refl ((f ⟶ f) ⟶ x))
    (derivable1_impp_refl ((f ⟶ f) ⟶ x) f)

section DeductionToMinimumAxiomatization

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaD1 : Derivable1 L]
variable [GammaPD1 : ProvableFromDerivable1 L GammaP GammaD1]
variable [bD : BasicDeduction L GammaD1]
variable [minD1 : MinimumDeduction L GammaD1]

theorem Deduction2Axiomatization_GammaD1P' :
    Derivable1FromProvable L GammaP GammaD1 := by
  constructor
  intro x y
  constructor
  · intro hxy
    let f : @Language.expr L := x ⟶ y
    refine (ProvableDerivable1.provable_derivable1
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) f).mpr ?_
    have hsrcToIntro : @Derivable1.derivable1 L GammaD1
        ((f ⟶ f) ⟶ x) y := by
      have hsrcToX : @Derivable1.derivable1 L GammaD1 ((f ⟶ f) ⟶ x) x :=
        derivable1_from_self_imp_source f x
      exact derivable1_trans ((f ⟶ f) ⟶ x) x y hsrcToX hxy
    exact derivable1s_impp_intros (f ⟶ f) x y hsrcToIntro
  · intro hprov
    exact aux_minimun_rule12 x y (x ⟶ y)
      ((ProvableDerivable1.provable_derivable1
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x ⟶ y)).mp hprov)

theorem Deduction2Axiomatization_minAX' :
    MinimumAxiomatization L GammaP := by
  letI : Derivable1FromProvable L GammaP GammaD1 :=
    Deduction2Axiomatization_GammaD1P'
  constructor
  · intro x y hxy hx
    have hxyD : @Derivable1.derivable1 L GammaD1 x y :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x y).mpr hxy
    have hsourceToX : @Derivable1.derivable1 L GammaD1 (y ⟶ y) x := by
      have hxx : @Derivable1.derivable1 L GammaD1 (x ⟶ x) x :=
        (ProvableDerivable1.provable_derivable1
          (L := L) (GammaP := GammaP) (GammaD := GammaD1) x).mp hx
      have hsourceToXX : @Derivable1.derivable1 L GammaD1 (y ⟶ y) (x ⟶ x) :=
        derivable1_impp_refl (y ⟶ y) x
      exact derivable1_trans (y ⟶ y) (x ⟶ x) x hsourceToXX hxx
    have hsourceToY : @Derivable1.derivable1 L GammaD1 (y ⟶ y) y :=
      derivable1_trans (y ⟶ y) x y hsourceToX hxyD
    exact (ProvableDerivable1.provable_derivable1
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) y).mpr hsourceToY
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      x (y ⟶ x)).mp (derivable1_axiom1 x y)
  · intro x y z
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ (x ⟶ z))).mp
        (derivable1_axiom2 x y z)

end DeductionToMinimumAxiomatization

section DerivableRulesMultiImpp

variable {L : Language.{u}} [MinimumLanguage L]
variable [Gamma : Provable L] [minAX : MinimumAxiomatization L Gamma]

theorem provable_multi_imp_shrink :
    forall (xs : List (@Language.expr L)) (x y : @Language.expr L),
      @Provable.provable L Gamma ((x ⟶ multi_imp xs (x ⟶ y)) ⟶ multi_imp xs (x ⟶ y)) := by
  intro xs x y
  induction xs with
  | nil =>
      simpa [multi_imp] using aux_minimun_theorem04 x y
  | cons a xs ih =>
      have h1 := provable_impp_arg_switch x a (multi_imp xs (x ⟶ y))
      have h2 := aux_minimun_rule01 (x ⟶ multi_imp xs (x ⟶ y))
        (multi_imp xs (x ⟶ y)) a ih
      exact by
        simpa [multi_imp] using
          (aux_minimun_rule02 (x ⟶ a ⟶ multi_imp xs (x ⟶ y))
            (a ⟶ x ⟶ multi_imp xs (x ⟶ y))
            (a ⟶ multi_imp xs (x ⟶ y)) h1 h2)

theorem provable_multi_imp_arg_switch1 :
    forall (xs : List (@Language.expr L)) (x y : @Language.expr L),
      @Provable.provable L Gamma ((x ⟶ multi_imp xs y) ⟶ multi_imp xs (x ⟶ y)) := by
  intro xs x y
  induction xs with
  | nil =>
      simpa [multi_imp] using provable_impp_refl (x ⟶ y)
  | cons a xs ih =>
      have h1 := provable_impp_arg_switch x a (multi_imp xs y)
      have h2 := aux_minimun_rule01 (x ⟶ multi_imp xs y)
        (multi_imp xs (x ⟶ y)) a ih
      exact by
        simpa [multi_imp] using
          (aux_minimun_rule02 (x ⟶ a ⟶ multi_imp xs y)
            (a ⟶ x ⟶ multi_imp xs y)
            (a ⟶ multi_imp xs (x ⟶ y)) h1 h2)

theorem provable_multi_imp_arg_switch2 :
    forall (xs : List (@Language.expr L)) (x y : @Language.expr L),
      @Provable.provable L Gamma (multi_imp xs (x ⟶ y) ⟶ (x ⟶ multi_imp xs y)) := by
  intro xs x y
  induction xs with
  | nil =>
      simpa [multi_imp] using provable_impp_refl (x ⟶ y)
  | cons a xs ih =>
      have h1 := aux_minimun_rule01 (multi_imp xs (x ⟶ y))
        (x ⟶ multi_imp xs y) a ih
      have h2 := provable_impp_arg_switch a x (multi_imp xs y)
      exact by
        simpa [multi_imp] using
          (aux_minimun_rule02 (a ⟶ multi_imp xs (x ⟶ y))
            (a ⟶ x ⟶ multi_imp xs y)
            (x ⟶ a ⟶ multi_imp xs y) h1 h2)

theorem provable_multi_imp_weaken :
    forall (xs : List (@Language.expr L)) (x y : @Language.expr L),
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (multi_imp xs x ⟶ multi_imp xs y) := by
  intro xs x y h
  induction xs with
  | nil =>
      simpa [multi_imp] using h
  | cons a xs ih =>
      simpa [multi_imp] using
        (aux_minimun_rule01 (multi_imp xs x) (multi_imp xs y) a ih)

theorem provable_multi_imp_split :
    forall (Phi1 Phi2 : context (L := L)) (xs : List (@Language.expr L))
        (y : @Language.expr L),
      List.Forall (Union _ Phi1 Phi2) xs ->
        @Provable.provable L Gamma (multi_imp xs y) ->
          exists xs1 xs2 : List (@Language.expr L),
            List.Forall Phi1 xs1 /\
              List.Forall Phi2 xs2 /\
                @Provable.provable L Gamma (multi_imp xs1 (multi_imp xs2 y)) := by
  intro Phi1 Phi2 xs
  induction xs with
  | nil =>
      intro y hxs hprov
      exact ⟨[], [], List.Forall.nil, List.Forall.nil, by
        simpa [multi_imp] using hprov⟩
  | cons a xs ih =>
      intro y hxs hprov
      cases hxs with
      | cons hx htail =>
      have hswitched : @Provable.provable L Gamma
          (multi_imp xs (a ⟶ y)) := by
        exact MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _
          (by simpa [multi_imp] using
            (provable_multi_imp_arg_switch1 xs a y))
          (by simpa [multi_imp] using hprov)
      rcases ih (a ⟶ y) htail hswitched with
        ⟨xs1, xs2, hxs1, hxs2, hprovTail⟩
      cases hx with
      | inl hPhi1 =>
          refine ⟨a :: xs1, xs2, List.Forall.cons hPhi1 hxs1, hxs2, ?_⟩
          have hstep1 : @Provable.provable L Gamma
              (multi_imp xs1 (multi_imp xs2 (a ⟶ y)) ⟶
                multi_imp xs1 (a ⟶ multi_imp xs2 y)) :=
            provable_multi_imp_weaken xs1
              (multi_imp xs2 (a ⟶ y))
              (a ⟶ multi_imp xs2 y)
              (provable_multi_imp_arg_switch2 xs2 a y)
          have hmid : @Provable.provable L Gamma
              (multi_imp xs1 (a ⟶ multi_imp xs2 y)) :=
            MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ hstep1 hprovTail
          exact by
            simpa [multi_imp] using
              (MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _
                (provable_multi_imp_arg_switch2 xs1 a (multi_imp xs2 y)) hmid)
      | inr hPhi2 =>
          refine ⟨xs1, a :: xs2, hxs1, List.Forall.cons hPhi2 hxs2, ?_⟩
          have hstep : @Provable.provable L Gamma
              (multi_imp xs1 (multi_imp xs2 (a ⟶ y)) ⟶
                multi_imp xs1 (a ⟶ multi_imp xs2 y)) :=
            provable_multi_imp_weaken xs1
              (multi_imp xs2 (a ⟶ y))
              (a ⟶ multi_imp xs2 y)
              (provable_multi_imp_arg_switch2 xs2 a y)
          exact by
            simpa [multi_imp] using
              (MinimumAxiomatization.modus_ponens (Gamma := Gamma) _ _ hstep hprovTail)

theorem provable_add_multi_imp_left_head :
    forall (xs1 xs2 : List (@Language.expr L)) (y : @Language.expr L),
      @Provable.provable L Gamma (multi_imp xs2 y ⟶ multi_imp (xs1 ++ xs2) y) := by
  intro xs1 xs2 y
  induction xs1 with
  | nil =>
      simpa [multi_imp] using provable_impp_refl (multi_imp xs2 y)
  | cons a xs1 ih =>
      have h := MinimumAxiomatization.axiom1 (Gamma := Gamma)
        (multi_imp (xs1 ++ xs2) y) a
      exact by
        simpa [multi_imp] using
          (aux_minimun_rule02 (multi_imp xs2 y)
            (multi_imp (xs1 ++ xs2) y)
            (a ⟶ multi_imp (xs1 ++ xs2) y) ih h)

theorem provable_add_multi_imp_left_tail :
    forall (xs1 xs2 : List (@Language.expr L)) (y : @Language.expr L),
      @Provable.provable L Gamma (multi_imp xs1 y ⟶ multi_imp (xs1 ++ xs2) y) := by
  intro xs1 xs2 y
  induction xs1 with
  | nil =>
      simpa [multi_imp] using provable_add_multi_imp_left_head xs2 [] y
  | cons a xs1 ih =>
      simpa [multi_imp] using
        (aux_minimun_rule01 (multi_imp xs1 y)
          (multi_imp (xs1 ++ xs2) y) a ih)

theorem provable_multi_imp_modus_ponens :
    forall (xs : List (@Language.expr L)) (y z : @Language.expr L),
      @Provable.provable L Gamma
        (multi_imp xs y ⟶ multi_imp xs (y ⟶ z) ⟶ multi_imp xs z) := by
  intro xs y z
  induction xs with
  | nil =>
      simpa [multi_imp] using aux_minimun_theorem02 y z
  | cons a xs ih =>
      simpa [multi_imp] using (by
        apply aux_minimun_rule02
        · apply aux_minimun_rule02
          · apply aux_minimun_rule01
            apply aux_minimun_rule02
            · exact ih
            · apply aux_minimun_rule02
              · exact aux_minimun_theorem00 a (multi_imp xs (y ⟶ z)) (multi_imp xs z)
              · exact provable_impp_arg_switch (a ⟶ multi_imp xs (y ⟶ z)) a
                  (multi_imp xs z)
          · apply aux_minimun_theorem04
        · apply provable_impp_arg_switch)

private theorem provable_multi_imp_singleton_right :
    forall (x y : @Language.expr L) (xs : List (@Language.expr L)),
      List.Forall (Singleton _ x) xs ->
        @Provable.provable L Gamma (multi_imp xs y ⟶ x ⟶ y) := by
  intro x y xs
  induction xs with
  | nil =>
      intro _hxs
      simpa [multi_imp] using
        (MinimumAxiomatization.axiom1 (Gamma := Gamma) y x)
  | cons a xs ih =>
      intro hxs
      cases hxs with
      | cons hsing htail =>
          cases hsing
          have ihTail : @Provable.provable L Gamma (multi_imp xs y ⟶ x ⟶ y) :=
            ih htail
          have hlift : @Provable.provable L Gamma
              ((x ⟶ multi_imp xs y) ⟶ x ⟶ x ⟶ y) := by
            exact aux_minimun_rule01 (multi_imp xs y) (x ⟶ y) x ihTail
          exact by
            simpa [multi_imp] using
              (aux_minimun_rule02 (x ⟶ multi_imp xs y) (x ⟶ x ⟶ y)
                (x ⟶ y) hlift (aux_minimun_theorem04 x y))

end DerivableRulesMultiImpp

section Axiomatization2SequentCalculus

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable L]
variable [GammaDP : DerivableProvable L GammaP GammaD]

theorem Axiomatization2SequentCalculus_GammaPD :
    ProvableDerivable L GammaP GammaD := by
  constructor
  intro x
  constructor
  · intro hprov
    exact (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      (empty_context (L := L)) x).mpr
      ⟨[], List.Forall.nil, by simpa [multi_imp] using hprov⟩
  · intro hder
    rcases (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      (empty_context (L := L)) x).mp hder with ⟨xs, hxs, hprov⟩
    cases xs with
    | nil =>
        simpa [multi_imp] using hprov
    | cons a xs =>
        cases hxs with
        | cons ha _ => cases ha

theorem Axiomatization2SequentCalculus_fwSC :
    FiniteWitnessedSequentCalculus L GammaD := by
  constructor
  intro Phi y hder
  rcases (DerivableProvable.derivable_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD) Phi y).mp hder with
    ⟨xs, hxsPhi, hprov⟩
  exact ⟨xs, hxsPhi,
    (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      (fun x => x ∈ xs) y).mpr
      ⟨xs, list_forall_mem_self xs, hprov⟩⟩

variable [minAX : MinimumAxiomatization L GammaP]

theorem Axiomatization2SequentCalculus_minSC :
    MinimumSequentCalculus L GammaD := by
  constructor
  · intro Phi x y hx hxy
    rcases (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) Phi x).mp hx with
      ⟨xs1, hxs1, hprov1⟩
    rcases (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) Phi (x ⟶ y)).mp hxy with
      ⟨xs2, hxs2, hprov2⟩
    have hleft : @Provable.provable L GammaP (multi_imp (xs1 ++ xs2) x) :=
      MinimumAxiomatization.modus_ponens (Gamma := GammaP) _ _
        (provable_add_multi_imp_left_tail xs1 xs2 x) hprov1
    have hright : @Provable.provable L GammaP (multi_imp (xs1 ++ xs2) (x ⟶ y)) :=
      MinimumAxiomatization.modus_ponens (Gamma := GammaP) _ _
        (provable_add_multi_imp_left_head xs1 xs2 (x ⟶ y)) hprov2
    have hmp := provable_multi_imp_modus_ponens (xs1 ++ xs2) x y
    have hmid := MinimumAxiomatization.modus_ponens (Gamma := GammaP) _ _ hmp hleft
    have hres := MinimumAxiomatization.modus_ponens (Gamma := GammaP) _ _ hmid hright
    exact (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) Phi y).mpr
      ⟨xs1 ++ xs2, (Forall_app_iff (fun z => Phi z) xs1 xs2).mpr ⟨hxs1, hxs2⟩,
        hres⟩
  · intro Phi x y hder
    rcases (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) (Phi ;; x) y).mp hder with
      ⟨xs, hxs, hprov⟩
    rcases provable_multi_imp_split Phi (Singleton _ x) xs y hxs hprov with
      ⟨xs1, xs2, hxs1, hxs2, hprovSplit⟩
    have hxs2_imp :
        @Provable.provable L GammaP (multi_imp xs2 y ⟶ x ⟶ y) :=
      provable_multi_imp_singleton_right x y xs2 hxs2
    have hweaken : @Provable.provable L GammaP
        (multi_imp xs1 (multi_imp xs2 y) ⟶ multi_imp xs1 (x ⟶ y)) :=
      provable_multi_imp_weaken xs1 (multi_imp xs2 y) (x ⟶ y) hxs2_imp
    exact (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) Phi (x ⟶ y)).mpr
      ⟨xs1, hxs1,
        MinimumAxiomatization.modus_ponens (Gamma := GammaP) _ _ hweaken hprovSplit⟩

theorem Axiomatization2SequentCalculus_bSC :
    BasicSequentCalculus L GammaD := by
  have hWeak : DeductionWeaken L GammaD := by
    intro Phi Psi x hInc hDer
    rcases (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) Phi x).mp hDer with
      ⟨xs, hxs, hprov⟩
    exact (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) Psi x).mpr
      ⟨xs, list_forall_impl (fun z hz => hInc z hz) hxs, hprov⟩
  have hFW : DerivableFiniteWitnessed L GammaD := by
    intro Phi y hDer
    exact (Axiomatization2SequentCalculus_fwSC
      (L := L) (GammaP := GammaP) (GammaD := GammaD)).derivable_finite_witnessed
      Phi y hDer
  have hCFW : ContextualDerivableFiniteWitnessed L GammaD :=
    DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed
      hWeak hFW
  have hMinSC : MinimumSequentCalculus L GammaD :=
    Axiomatization2SequentCalculus_minSC
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
  have hSubst1 : DeductionSubst1 L GammaD :=
    DeductionImpIntro_DeductionMP_2_DeductionSubst1
      (by
        intro Phi x y hDer
        exact hMinSC.deduction_impp_intros Phi x y hDer)
      (by
        intro Phi x y hx hxy
        exact hMinSC.deduction_modus_ponens Phi x y hx hxy)
  constructor
  · exact hWeak
  · intro Phi x hx
    exact (DerivableProvable.derivable_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) Phi x).mpr
      ⟨[x], List.Forall.cons hx List.Forall.nil,
        by simpa [multi_imp] using provable_impp_refl x⟩
  · exact DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst
      hWeak hCFW hSubst1

end Axiomatization2SequentCalculus

section DerivableRulesFromSequentCalculus

variable {L : Language.{u}}
variable [GammaD : Derivable L] [bSC : BasicSequentCalculus L GammaD]

theorem deduction_weaken0 [GammaP : Provable L]
    [GammaPD : ProvableDerivable L GammaP GammaD] :
    forall (Phi : context (L := L)) (y : @Language.expr L),
      @Provable.provable L GammaP y ->
        @Derivable.derivable L GammaD Phi y := by
  intro Phi y hprov
  exact deduction_weaken (empty_context (L := L)) Phi y
    (by
      intro z hz
      cases hz)
    ((ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) y).mp hprov)

theorem derivables_weaken0 [GammaP : Provable L]
    [GammaPD : ProvableFromDerivable L GammaP GammaD] :
    forall (Phi : context (L := L)) (y : @Language.expr L),
      @Provable.provable L GammaP y ->
        @Derivable.derivable L GammaD Phi y :=
  deduction_weaken0 (GammaD := GammaD)

variable [MinimumLanguage L] [minSC : MinimumSequentCalculus L GammaD]

theorem deduction_impp_elim :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi (impp x y) ->
        @Derivable.derivable L GammaD (Union _ Phi (Singleton _ x)) y := by
  intro Phi x y h
  exact MinimumSequentCalculus.deduction_modus_ponens
    (Union _ Phi (Singleton _ x)) x y
    (derivable_assum (Union _ Phi (Singleton _ x)) x (Or.inr rfl))
    (deduction_weaken Phi (Union _ Phi (Singleton _ x)) (impp x y)
      (by
        intro z hz
        exact Or.inl hz)
      h)

theorem deduction_theorem :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD (Union _ Phi (Singleton _ x)) y <->
        @Derivable.derivable L GammaD Phi (x ⟶ y) := by
  intro Phi x y
  constructor
  · intro h
    exact MinimumSequentCalculus.deduction_impp_intros Phi x y h
  · intro h
    exact deduction_impp_elim Phi x y h

theorem deduction_theorem_multi_imp :
    forall (Phi : context (L := L)) (xs : List (@Language.expr L))
        (y : @Language.expr L),
      @Derivable.derivable L GammaD (Union _ Phi (fun x => x ∈ xs)) y <->
        @Derivable.derivable L GammaD Phi (multi_imp xs y) := by
  intro Phi xs y
  induction xs generalizing Phi with
  | nil =>
      constructor
      · intro h
        exact deduction_weaken
          (Union _ Phi (fun x => x ∈ ([] : List (@Language.expr L)))) Phi y
          (by
            intro z hz
            cases hz with
            | inl hPhi => exact hPhi
            | inr hmem => cases hmem)
          (by simpa [multi_imp] using h)
      · intro h
        exact by
          simpa [multi_imp] using
            (deduction_weaken Phi
              (Union _ Phi (fun x => x ∈ ([] : List (@Language.expr L)))) y
              (by
                intro z hz
                exact Or.inl hz)
              h)
  | cons a xs ih =>
      constructor
      · intro h
        have hctx : @Derivable.derivable L GammaD
            (Union _ (Phi ;; a) (fun x => x ∈ xs)) y :=
          deduction_weaken (Union _ Phi (fun x => x ∈ a :: xs))
            (Union _ (Phi ;; a) (fun x => x ∈ xs)) y
            (by
              intro z hz
              cases hz with
              | inl hPhi => exact Or.inl (Or.inl hPhi)
              | inr hmem =>
                  cases hmem with
                  | head => exact Or.inl (Or.inr rfl)
                  | tail _ htail => exact Or.inr htail)
            h
        have htail : @Derivable.derivable L GammaD (Phi ;; a) (multi_imp xs y) :=
          (ih (Phi := Phi ;; a)).mp hctx
        exact by
          simpa [multi_imp] using
            (deduction_theorem Phi a (multi_imp xs y)).mp htail
      · intro h
        have htail : @Derivable.derivable L GammaD (Phi ;; a) (multi_imp xs y) :=
          (deduction_theorem Phi a (multi_imp xs y)).mpr
            (by simpa [multi_imp] using h)
        have hctx : @Derivable.derivable L GammaD
            (Union _ (Phi ;; a) (fun x => x ∈ xs)) y :=
          (ih (Phi := Phi ;; a)).mpr htail
        exact deduction_weaken (Union _ (Phi ;; a) (fun x => x ∈ xs))
          (Union _ Phi (fun x => x ∈ a :: xs)) y
          (by
            intro z hz
            cases hz with
            | inl hPhiA =>
                cases hPhiA with
                | inl hPhi => exact Or.inl hPhi
                | inr hSing =>
                    cases hSing
                    exact Or.inr (List.Mem.head xs)
            | inr hmem =>
                exact Or.inr (List.Mem.tail a hmem))
          hctx

theorem derivable_impp_refl :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ x) := by
  intro Phi x
  exact (deduction_theorem Phi x x).mp
    (derivable_assum (Phi ;; x) x (Or.inr rfl))

theorem deduction_left_impp_intros :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi x ->
        @Derivable.derivable L GammaD Phi (y ⟶ x) := by
  intro Phi x y hx
  exact (deduction_theorem Phi y x).mp
    (deduction_weaken Phi (Phi ;; y) x
      (by
        intro z hz
        exact Or.inl hz)
      hx)

theorem derivable_axiom1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ y ⟶ x) := by
  intro Phi x y
  exact (deduction_theorem Phi x (y ⟶ x)).mp
    ((deduction_theorem (Phi ;; x) y x).mp
      (derivable_assum ((Phi ;; x) ;; y) x (Or.inl (Or.inr rfl))))

theorem derivable_axiom2 :
    forall (Phi : context (L := L)) (x y z : @Language.expr L),
      @Derivable.derivable L GammaD Phi ((x ⟶ y ⟶ z) ⟶ (x ⟶ y) ⟶ (x ⟶ z)) := by
  intro Phi x y z
  let A := x ⟶ y ⟶ z
  let B := x ⟶ y
  let C : context (L := L) := ((Phi ;; A) ;; B) ;; x
  have hA : @Derivable.derivable L GammaD C A :=
    derivable_assum C A (Or.inl (Or.inl (Or.inr rfl)))
  have hB : @Derivable.derivable L GammaD C B :=
    derivable_assum C B (Or.inl (Or.inr rfl))
  have hx : @Derivable.derivable L GammaD C x :=
    derivable_assum C x (Or.inr rfl)
  have hyz : @Derivable.derivable L GammaD C (y ⟶ z) :=
    MinimumSequentCalculus.deduction_modus_ponens C x (y ⟶ z) hx hA
  have hy : @Derivable.derivable L GammaD C y :=
    MinimumSequentCalculus.deduction_modus_ponens C x y hx hB
  have hz : @Derivable.derivable L GammaD C z :=
    MinimumSequentCalculus.deduction_modus_ponens C y z hy hyz
  exact (deduction_theorem Phi A (B ⟶ x ⟶ z)).mp
    ((deduction_theorem (Phi ;; A) B (x ⟶ z)).mp
      ((deduction_theorem ((Phi ;; A) ;; B) x z).mp hz))

theorem derivable_modus_ponens :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ (x ⟶ y) ⟶ y) := by
  intro Phi x y
  let C : context (L := L) := (Phi ;; x) ;; (x ⟶ y)
  have hx : @Derivable.derivable L GammaD C x :=
    derivable_assum C x (Or.inl (Or.inr rfl))
  have hxy : @Derivable.derivable L GammaD C (x ⟶ y) :=
    derivable_assum C (x ⟶ y) (Or.inr rfl)
  have hy : @Derivable.derivable L GammaD C y :=
    MinimumSequentCalculus.deduction_modus_ponens C x y hx hxy
  exact (deduction_theorem Phi x ((x ⟶ y) ⟶ y)).mp
    ((deduction_theorem (Phi ;; x) (x ⟶ y) y).mp hy)

theorem deduction_impp_trans :
    forall (Phi : context (L := L)) (x y z : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ y) ->
        @Derivable.derivable L GammaD Phi (y ⟶ z) ->
          @Derivable.derivable L GammaD Phi (x ⟶ z) := by
  intro Phi x y z hxy hyz
  exact (deduction_theorem Phi x z).mp
    (MinimumSequentCalculus.deduction_modus_ponens (Phi ;; x) y z
      (MinimumSequentCalculus.deduction_modus_ponens (Phi ;; x) x y
        (derivable_assum (Phi ;; x) x (Or.inr rfl))
        (deduction_weaken Phi (Phi ;; x) (x ⟶ y)
          (by
            intro w hw
            exact Or.inl hw)
          hxy))
      (deduction_weaken Phi (Phi ;; x) (y ⟶ z)
        (by
          intro w hw
          exact Or.inl hw)
        hyz))

theorem deduction_impp_arg_switch :
    forall (Phi : context (L := L)) (x y z : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ y ⟶ z) ->
        @Derivable.derivable L GammaD Phi (y ⟶ x ⟶ z) := by
  intro Phi x y z h
  let C : context (L := L) := (Phi ;; y) ;; x
  have hy : @Derivable.derivable L GammaD C y :=
    derivable_assum C y (Or.inl (Or.inr rfl))
  have hx : @Derivable.derivable L GammaD C x :=
    derivable_assum C x (Or.inr rfl)
  have hxyz : @Derivable.derivable L GammaD C (x ⟶ y ⟶ z) :=
    deduction_weaken Phi C (x ⟶ y ⟶ z)
      (by
        intro w hw
        exact Or.inl (Or.inl hw))
      h
  have hyz : @Derivable.derivable L GammaD C (y ⟶ z) :=
    MinimumSequentCalculus.deduction_modus_ponens C x (y ⟶ z) hx hxyz
  have hz : @Derivable.derivable L GammaD C z :=
    MinimumSequentCalculus.deduction_modus_ponens C y z hy hyz
  exact (deduction_theorem Phi y (x ⟶ z)).mp
    ((deduction_theorem (Phi ;; y) x z).mp hz)

theorem derivables_impp_elim :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi (impp x y) ->
        @Derivable.derivable L GammaD (Union _ Phi (Singleton _ x)) y :=
  deduction_impp_elim (GammaD := GammaD)

theorem derivables_impp_theorem :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD (Union _ Phi (Singleton _ x)) y <->
        @Derivable.derivable L GammaD Phi (x ⟶ y) :=
  deduction_theorem (GammaD := GammaD)

theorem derivables_multi_impp_theorem :
    forall (Phi : context (L := L)) (xs : List (@Language.expr L))
        (y : @Language.expr L),
      @Derivable.derivable L GammaD (Union _ Phi (fun x => x ∈ xs)) y <->
        @Derivable.derivable L GammaD Phi (multi_imp xs y) :=
  deduction_theorem_multi_imp (GammaD := GammaD)

theorem derivables_impp_intros_l :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi x ->
        @Derivable.derivable L GammaD Phi (y ⟶ x) :=
  deduction_left_impp_intros (GammaD := GammaD)

theorem derivables_impp_trans :
    forall (Phi : context (L := L)) (x y z : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ y) ->
        @Derivable.derivable L GammaD Phi (y ⟶ z) ->
          @Derivable.derivable L GammaD Phi (x ⟶ z) :=
  deduction_impp_trans (GammaD := GammaD)

theorem derivables_impp_arg_switch :
    forall (Phi : context (L := L)) (x y z : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ y ⟶ z) ->
        @Derivable.derivable L GammaD Phi (y ⟶ x ⟶ z) :=
  deduction_impp_arg_switch (GammaD := GammaD)

end DerivableRulesFromSequentCalculus

theorem provable_right
    {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD1 : Derivable1 L]
    [GammaD1P : Derivable1Provable L GammaP GammaD1]
    [minAX : MinimumAxiomatization L GammaP] :
    forall x y : @Language.expr L,
      @Provable.provable L GammaP x ->
        @Derivable1.derivable1 L GammaD1 y x := by
  intro x y hprov
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) y x).mpr
    (aux_minimun_rule00 x y hprov)

theorem provable_derivable_right
    {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD1 : Derivable1 L]
    [GammaD1P : Derivable1FromProvable L GammaP GammaD1]
    [minAX : MinimumAxiomatization L GammaP] :
    forall x y : @Language.expr L,
      @Provable.provable L GammaP x ->
        @Derivable1.derivable1 L GammaD1 y x :=
  provable_right (GammaP := GammaP) (GammaD1 := GammaD1)

section SequentCalculus2Axiomatization

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable L]
variable [GammaPD : ProvableDerivable L GammaP GammaD]
variable [bSC : BasicSequentCalculus L GammaD]
variable [minSC : MinimumSequentCalculus L GammaD]

theorem SequentCalculus2Axiomatization_minAX :
    MinimumAxiomatization L GammaP := by
  constructor
  · intro x y hxy hx
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) y).mpr
      (MinimumSequentCalculus.deduction_modus_ponens
        (empty_context (L := L)) x y
        ((ProvableDerivable.provable_derivable
          (L := L) (GammaP := GammaP) (GammaD := GammaD) x).mp hx)
        ((ProvableDerivable.provable_derivable
          (L := L) (GammaP := GammaP) (GammaD := GammaD) (x ⟶ y)).mp hxy))
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) (x ⟶ y ⟶ x)).mpr
      (derivable_axiom1 (GammaD := GammaD) (empty_context (L := L)) x y)
  · intro x y z
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      ((x ⟶ y ⟶ z) ⟶ (x ⟶ y) ⟶ (x ⟶ z))).mpr
      (derivable_axiom2 (GammaD := GammaD) (empty_context (L := L)) x y z)

theorem SequentCalculus2Axiomatization_GammaDP
    [fwSC : FiniteWitnessedSequentCalculus L GammaD] :
    DerivableProvable L GammaP GammaD := by
  constructor
  intro Phi y
  constructor
  · intro hder
    rcases derivable_finite_witnessed Phi y hder with ⟨xs, hxsPhi, hxsDer⟩
    refine ⟨xs, hxsPhi, ?_⟩
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) (multi_imp xs y)).mpr
      ((deduction_theorem_multi_imp (empty_context (L := L)) xs y).mp
        (deduction_weaken (fun x => x ∈ xs)
          (Union _ (empty_context (L := L)) (fun x => x ∈ xs)) y
          (by
            intro z hz
            exact Or.inr hz)
          hxsDer))
  · intro h
    rcases h with ⟨xs, hxsPhi, hprov⟩
    have hEmpty : @Derivable.derivable L GammaD
        (empty_context (L := L)) (multi_imp xs y) :=
      (ProvableDerivable.provable_derivable
        (L := L) (GammaP := GammaP) (GammaD := GammaD) (multi_imp xs y)).mp hprov
    have hUnionEmpty : @Derivable.derivable L GammaD
        (Union _ (empty_context (L := L)) (fun x => x ∈ xs)) y :=
      (deduction_theorem_multi_imp (empty_context (L := L)) xs y).mpr hEmpty
    exact deduction_weaken
      (Union _ (empty_context (L := L)) (fun x => x ∈ xs)) Phi y
      (by
        intro z hz
        cases hz with
        | inl hEmptySet => cases hEmptySet
        | inr hmem => exact list_forall_mem hxsPhi z hmem)
      hUnionEmpty

end SequentCalculus2Axiomatization

section EquivProvableToEquivDerivable1

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable1 L] [GammaE : LogicEquiv L]
variable [GammaD1P : Derivable1Provable L GammaP GammaD]
variable [GammaEP : EquivProvable L GammaP GammaE]

theorem Axiomatization2Deduction_GammaED1 :
    EquivDerivable1 L GammaD GammaE := by
  constructor
  intro x y
  constructor
  · intro heq
    have hprov := (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaE) x y).mp heq
    exact ⟨
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD) x y).mpr hprov.left,
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD) y x).mpr hprov.right⟩
  · intro hder
    exact (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaE) x y).mpr
      ⟨
        (Derivable1Provable.derivable1_provable
          (L := L) (GammaP := GammaP) (GammaD := GammaD) x y).mp hder.left,
        (Derivable1Provable.derivable1_provable
          (L := L) (GammaP := GammaP) (GammaD := GammaD) y x).mp hder.right⟩

end EquivProvableToEquivDerivable1

section EquivProvable1ToEquivDerivable

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable1 L] [GammaE : LogicEquiv L]
variable [GammaD1P : Derivable1Provable L GammaP GammaD]
variable [GammaED1 : EquivDerivable1 L GammaD GammaE]

theorem Deduction2Axiomatization_GammaEP :
    EquivProvable L GammaP GammaE := by
  constructor
  intro x y
  constructor
  · intro heq
    have hder := (EquivDerivable1.__logic_equiv_derivable1
      (L := L) (GammaD := GammaD) (GammaE := GammaE) x y).mp heq
    exact ⟨
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD) x y).mp hder.left,
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD) y x).mp hder.right⟩
  · intro hprov
    exact (EquivDerivable1.__logic_equiv_derivable1
      (L := L) (GammaD := GammaD) (GammaE := GammaE) x y).mpr
      ⟨
        (Derivable1Provable.derivable1_provable
          (L := L) (GammaP := GammaP) (GammaD := GammaD) x y).mpr hprov.left,
        (Derivable1Provable.derivable1_provable
          (L := L) (GammaP := GammaP) (GammaD := GammaD) y x).mpr hprov.right⟩

end EquivProvable1ToEquivDerivable

section Transformation

variable {L : Language.{u}} [MinimumLanguage L]

def Provable2Derivable [GammaP : Provable L] : Derivable L :=
  { derivable := fun Phi y =>
      exists xs : List (@Language.expr L),
        List.Forall (fun x => Phi x) xs /\
          @Provable.provable L GammaP (multi_imp xs y) }

def Provable2Derivable_Normal [GammaP : Provable L] :
    DerivableProvable L GammaP (Provable2Derivable (L := L)) :=
  { derivable_provable := by
      intro Phi y
      rfl }

def Derivable2Provable [GammaD : Derivable L] : Provable L :=
  { provable := fun x =>
      @Derivable.derivable L GammaD (empty_context (L := L)) x }

def Derivable2Provable_Normal [GammaD : Derivable L] :
    ProvableDerivable L (Derivable2Provable (L := L)) GammaD :=
  { provable_derivable := by
      intro x
      rfl }

def Provable2Derivable1 [GammaP : Provable L] : Derivable1 L :=
  { derivable1 := fun x y =>
      @Provable.provable L GammaP (impp x y) }

def Provable2Derivable1_Normal [GammaP : Provable L] :
    Derivable1Provable L GammaP (Provable2Derivable1 (L := L)) :=
  { derivable1_provable := by
      intro x y
      rfl }

def Provable2Equiv [GammaP : Provable L] : LogicEquiv L :=
  { logic_equiv := fun x y =>
      @Provable.provable L GammaP (impp x y) /\
        @Provable.provable L GammaP (impp y x) }

def Provable2Equiv_Normal [GammaP : Provable L] :
    EquivProvable L GammaP (Provable2Equiv (L := L)) :=
  { logic_equiv_provable := by
      intro x y
      rfl }

def Derivable12Equiv [GammaD1 : Derivable1 L] : LogicEquiv L :=
  { logic_equiv := fun x y =>
      @Derivable1.derivable1 L GammaD1 x y /\
        @Derivable1.derivable1 L GammaD1 y x }

def Derivable12Equiv_Normal [GammaD1 : Derivable1 L] :
    EquivDerivable1 L GammaD1 (Derivable12Equiv (L := L)) :=
  { __logic_equiv_derivable1 := by
      intro x y
      rfl }

def Derivable12Provable [GammaD1 : Derivable1 L] : Provable L :=
  { provable := fun x =>
      @Derivable1.derivable1 L GammaD1 (impp x x) x }

def Derivable12Provable_Normal [GammaD1 : Derivable1 L] :
    ProvableDerivable1 L (Derivable12Provable (L := L)) GammaD1 :=
  { provable_derivable1 := by
      intro x
      rfl }

end Transformation

end Unifysl
