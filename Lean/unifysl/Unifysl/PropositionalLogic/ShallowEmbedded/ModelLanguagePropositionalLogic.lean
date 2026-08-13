/-
Coq inventory from
`unifysl-prp-8.20/PropositionalLogic/ShallowEmbedded/ModelLanguagePropositionalLogic.v`.

Active declarations:
- `Model2Iffp`
- `IffpDefinition_Model`, field `model2iffp`
- `Model2Iffp_Normal`
- `Model2Andp`
- `AndpDefinition_Model`, field `model2andp`
- `Model2Andp_Normal`
- `Model2Orp`
- `OrpDefinition_Model`, field `model2orp`
- `Model2Orp_Normal`
- `Model2Truep`
- `TrueDefinition_Model`, field `model2truep`
- `Model2Truep_Normal`
- `Model2ImpAdjoint`
- `Model2MinD1`
- `Model2AndDeduction`
- `Model2OrDeduction`
- `Model2IffDeduction`
- `Model2TrueDeduction`
- `Model2BasicDeduction`
- `Model2MinumumDeduction'`

Lean keeps these declarations under
`Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic`
to avoid root-name collisions with other model-language builders.
-/

import Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage
import Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic
import Unifysl.PropositionalLogic.Syntax
import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic

universe u

namespace Unifysl
namespace PropositionalLogic
namespace ShallowEmbedded
namespace ModelLanguagePropositionalLogic

abbrev Model_L (M : Model.{u}) : Language.{u} :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model_L M

abbrev Model2Derivable1 (M : Model.{u}) : Derivable1 (Model_L M) :=
  Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model2Derivable1 M

abbrev Model2Impp (M : Model.{u}) : MinimumLanguage (Model_L M) :=
  Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.Model2Impp M

def Model2Iffp (M : Model.{u}) : IffLanguage (Model_L M) where
  iffp := fun x y m => x m ↔ y m

class IffpDefinition_Model {M : Model.{u}}
    (iffpL : IffLanguage (Model_L M)) : Prop where
  model2iffp :
    forall x y : @Language.expr (Model_L M),
      @iffp (Model_L M) iffpL x y = fun m => x m ↔ y m

theorem Model2Iffp_Normal (M : Model.{u}) :
    IffpDefinition_Model (M := M) (Model2Iffp M) := by
  constructor
  intro x y
  rfl

def Model2Andp (M : Model.{u}) : AndLanguage (Model_L M) where
  andp := fun x y m => x m ∧ y m

class AndpDefinition_Model {M : Model.{u}}
    (andpL : AndLanguage (Model_L M)) : Prop where
  model2andp :
    forall x y : @Language.expr (Model_L M),
      @andp (Model_L M) andpL x y = fun m => x m ∧ y m

theorem Model2Andp_Normal (M : Model.{u}) :
    AndpDefinition_Model (M := M) (Model2Andp M) := by
  constructor
  intro x y
  rfl

def Model2Orp (M : Model.{u}) : OrLanguage (Model_L M) where
  orp := fun x y m => x m ∨ y m

class OrpDefinition_Model {M : Model.{u}}
    (orpL : OrLanguage (Model_L M)) : Prop where
  model2orp :
    forall x y : @Language.expr (Model_L M),
      @orp (Model_L M) orpL x y = fun m => x m ∨ y m

theorem Model2Orp_Normal (M : Model.{u}) :
    OrpDefinition_Model (M := M) (Model2Orp M) := by
  constructor
  intro x y
  rfl

def Model2Truep (M : Model.{u}) : TrueLanguage (Model_L M) where
  truep := fun _ => True

class TrueDefinition_Model {M : Model.{u}}
    (truepL : TrueLanguage (Model_L M)) : Prop where
  model2truep :
    forall m : @Model.model M,
      @truep (Model_L M) truepL m = True

theorem Model2Truep_Normal (M : Model.{u}) :
    TrueDefinition_Model (M := M) (Model2Truep M) := by
  constructor
  intro m
  rfl

theorem Model2ImpAdjoint (M : Model.{u}) :
    @ImpAndAdjointDeduction (Model_L M) (Model2Impp M) (Model2Andp M)
      (Model2Derivable1 M) := by
  letI : MinimumLanguage (Model_L M) := Model2Impp M
  letI : AndLanguage (Model_L M) := Model2Andp M
  exact {
    derivable1s_impp_andp_adjoint := by
      intro x y z
      constructor
      · intro h m hxy
        exact h m hxy.left hxy.right
      · intro h m hx hy
        exact h m ⟨hx, hy⟩
  }

theorem Model2MinD1 (M : Model.{u}) :
    @MinimumDeduction (Model_L M) (Model2Impp M) (Model2Derivable1 M) := by
  letI : MinimumLanguage (Model_L M) := Model2Impp M
  exact {
    derivable1s_modus_ponens := by
      intro x y z hyz hy m hx
      exact hyz m hx (hy m hx)
    derivable1s_impp_intros := by
      intro x y z h m hx hy
      exact h m (fun _ => hy)
    derivable1_impp_refl := by
      intro x y m _hx hy
      exact hy
    derivable1_axiom1 := by
      intro x y m hx _hy
      exact hx
    derivable1_axiom2 := by
      intro x y z m h hxy hx
      exact h hx (hxy hx)
  }

theorem Model2AndDeduction (M : Model.{u}) :
    @AndDeduction (Model_L M) (Model2Andp M) (Model2Derivable1 M) := by
  letI : AndLanguage (Model_L M) := Model2Andp M
  exact {
    derivable1s_truep_intros := by
      intro x y z hy hz m hx
      exact ⟨hy m hx, hz m hx⟩
    derivable1_andp_elim1 := by
      intro x y m hxy
      exact hxy.left
    derivable1_andp_elim2 := by
      intro x y m hxy
      exact hxy.right
  }

theorem Model2OrDeduction (M : Model.{u}) :
    @OrDeduction (Model_L M) (Model2Orp M) (Model2Derivable1 M) := by
  letI : OrLanguage (Model_L M) := Model2Orp M
  exact {
    derivable1_orp_intros1 := by
      intro x y m hx
      exact Or.inl hx
    derivable1_orp_intros2 := by
      intro x y m hy
      exact Or.inr hy
    derivable1_orp_elim := by
      intro x y z hxz hyz m hxy
      exact hxy.elim (fun hx => hxz m hx) (fun hy => hyz m hy)
  }

theorem Model2IffDeduction (M : Model.{u}) :
    @IffDeduction (Model_L M) (Model2Impp M) (Model2Iffp M)
      (Model2Derivable1 M) := by
  letI : MinimumLanguage (Model_L M) := Model2Impp M
  letI : IffLanguage (Model_L M) := Model2Iffp M
  exact {
    derivable1_iffp_intros := by
      intro x y m hxy hyx
      exact ⟨hxy, hyx⟩
    derivable1_iffp_elim1 := by
      intro x y m hiff hx
      exact hiff.mp hx
    derivable1_iffp_elim2 := by
      intro x y m hiff hy
      exact hiff.mpr hy
  }

theorem Model2TrueDeduction (M : Model.{u}) :
    @TrueDeduction (Model_L M) (Model2Truep M) (Model2Derivable1 M) := by
  letI : TrueLanguage (Model_L M) := Model2Truep M
  exact {
    derivable1_truep_intros := by
      intro x m _hx
      trivial
  }

theorem Model2BasicDeduction (M : Model.{u}) :
    BasicDeduction (Model_L M) (Model2Derivable1 M) := by
  constructor
  · intro x m hx
    exact hx
  · intro x y z hxy hyz m hx
    exact hyz m (hxy m hx)

theorem Model2MinumumDeduction' (M : Model.{u}) :
    @MinimumDeduction (Model_L M) (Model2Impp M) (Model2Derivable1 M) :=
  Model2MinD1 M

end ModelLanguagePropositionalLogic
end ShallowEmbedded
end PropositionalLogic
end Unifysl
