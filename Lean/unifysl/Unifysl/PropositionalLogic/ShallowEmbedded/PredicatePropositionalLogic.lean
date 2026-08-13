/- Coq inventory: unifysl-prp/PropositionalLogic/ShallowEmbedded/PredicatePropositionalLogic.v
   - Instance Pred_minL
   - Instance Pred_andpL
   - Instance Pred_orpL
   - Instance Pred_falsepL
   - Instance Pred_tminSM
   - Instance Pred_andpSM
   - Instance Pred_orpSM
   - Instance Pred_falsepSM
   - Instance Pred_Gamma
   - Instance Pred_minAX
   - Instance Pred_andpAX
   - Instance Pred_orpAX
   - Instance Pred_falsepAX
   - Instance Pred_kiSM
   - Instance Pred_kminSM
   - Instance Pred_kandpSM
   - Instance Pred_korpSM
   - Instance Pred_kfalsepSM
-/

import Unifysl.GeneralLogic.ShallowEmbedded.PredicateAsLang
import Unifysl.MinimumLogic.ProofTheory.Minimum
import Unifysl.MinimumLogic.Semantics.SemanticEquiv
import Unifysl.MinimumLogic.Sound.Sound_Classical_Trivial
import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic
import Unifysl.PropositionalLogic.Semantics.Kripke
import Unifysl.PropositionalLogic.Semantics.Trivial
import Unifysl.PropositionalLogic.Sound.Sound_Classical_Trivial

universe u

namespace Unifysl

open PropositionalLanguageNotation

private abbrev Pred_MD (A : Type u) : Model.{u} :=
  { model := A }

private abbrev Pred_eqR (A : Type u) : Relation A :=
  { Krelation := fun m n => m = n }

instance Pred_minL (A : Type u) : MinimumLanguage (Pred_L A) where
  impp := Semantics.impp

instance Pred_andpL (A : Type u) : AndLanguage (Pred_L A) where
  andp := Semantics.andp

instance Pred_orpL (A : Type u) : OrLanguage (Pred_L A) where
  orp := Semantics.orp

instance Pred_falsepL (A : Type u) : FalseLanguage (Pred_L A) where
  falsep := Semantics.falsep

instance Pred_tminSM (A : Type u) :
    TrivialMinimumSemantics (Pred_L A) (Pred_MD A) (Pred_SM A) where
  denote_impp := by
    intro x y
    exact Same_set_refl A _

instance Pred_andpSM (A : Type u) :
    AndSemantics (Pred_L A) (Pred_MD A) (Pred_SM A) where
  denote_andp := by
    intro x y
    exact Same_set_refl A _

instance Pred_orpSM (A : Type u) :
    OrSemantics (Pred_L A) (Pred_MD A) (Pred_SM A) where
  denote_orp := by
    intro x y
    exact Same_set_refl A _

instance Pred_falsepSM (A : Type u) :
    FalseSemantics (Pred_L A) (Pred_MD A) (Pred_SM A) where
  denote_falsep := by
    exact Same_set_refl A _

instance (priority := 100) Pred_Gamma (A : Type u) : Provable (Pred_L A) where
  provable := fun x => forall a : A, x a

instance Pred_minAX (A : Type u) :
    MinimumAxiomatization (Pred_L A) (Pred_Gamma A) := by
  constructor
  ·
    intro x y hxy hx a
    exact sound_modus_ponens
      (L := Pred_L A) (MD := Pred_MD A) x y a (hxy a) (hx a)
  ·
    intro x y a
    intro hx _hy
    exact hx
  ·
    intro x y z a
    intro hxyz hxy hx
    exact hxyz hx (hxy hx)

instance Pred_andpAX (A : Type u) :
    AndAxiomatization (Pred_L A) (Pred_Gamma A) where
  provable_andp_intros := by
    intro x y a
    intro hx hy
    exact ⟨hx, hy⟩
  provable_andp_elim1 := by
    intro x y a
    intro hxy
    exact hxy.left
  provable_andp_elim2 := by
    intro x y a
    intro hxy
    exact hxy.right

instance Pred_orpAX (A : Type u) :
    OrAxiomatization (Pred_L A) (Pred_Gamma A) where
  provable_orp_intros1 := by
    intro x y a
    intro hx
    exact Or.inl hx
  provable_orp_intros2 := by
    intro x y a
    intro hy
    exact Or.inr hy
  provable_orp_elim := by
    intro x y z a
    intro hxz hyz hxy
    cases hxy with
    | inl hx => exact hxz hx
    | inr hy => exact hyz hy

instance Pred_falsepAX (A : Type u) :
    FalseAxiomatization (Pred_L A) (Pred_Gamma A) where
  provable_falsep_elim := by
    intro x a
    intro hfalse
    cases hfalse

instance Pred_kiSM (A : Type u) :
    @KripkeIntuitionisticSemantics (Pred_L A) (Pred_MD A)
      (unit_kMD (Pred_MD A)) Unit.unit (Pred_eqR A) (Pred_SM A) :=
  eqR_KripkeIntuitionistic

instance Pred_kminSM (A : Type u) :
    @KripkeMinimumSemantics (Pred_L A) (Pred_minL A)
      (Pred_MD A) (unit_kMD (Pred_MD A)) Unit.unit (Pred_eqR A) (Pred_SM A) :=
  Trivial2Kripke

instance Pred_kandpSM (A : Type u) :
    @KripkeAndSemantics (Pred_L A) (Pred_andpL A)
      (Pred_MD A) (unit_kMD (Pred_MD A)) Unit.unit (Pred_SM A) :=
  @KripkeAndSemantics.mk (Pred_L A) (Pred_andpL A)
    (Pred_MD A) (unit_kMD (Pred_MD A)) Unit.unit (Pred_SM A)
    (by
      intro x y
      exact Same_set_refl A _)

instance Pred_korpSM (A : Type u) :
    @KripkeOrSemantics (Pred_L A) (Pred_orpL A)
      (Pred_MD A) (unit_kMD (Pred_MD A)) Unit.unit (Pred_SM A) :=
  @KripkeOrSemantics.mk (Pred_L A) (Pred_orpL A)
    (Pred_MD A) (unit_kMD (Pred_MD A)) Unit.unit (Pred_SM A)
    (by
      intro x y
      exact Same_set_refl A _)

instance Pred_kfalsepSM (A : Type u) :
    @KripkeFalseSemantics (Pred_L A) (Pred_falsepL A)
      (Pred_MD A) (unit_kMD (Pred_MD A)) Unit.unit (Pred_SM A) :=
  @KripkeFalseSemantics.mk (Pred_L A) (Pred_falsepL A)
    (Pred_MD A) (unit_kMD (Pred_MD A)) Unit.unit (Pred_SM A)
    (by
      exact Same_set_refl A _)

end Unifysl
