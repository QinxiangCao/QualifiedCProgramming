/- Coq inventory: unifysl-prp/GeneralLogic/ShallowEmbedded/PredicateAsLang.v
   - Instance Pred_L
   - Instance Pred_strongGammaP
   - Instance Pred_strongGammaD
   - Instance Pred_SM
-/

import Unifysl.GeneralLogic.Base

universe u

namespace Unifysl

instance Pred_L (A : Type u) : Language.{u} where
  expr := A -> Prop

instance Pred_strongGammaP (A : Type u) : Provable (Pred_L A) where
  provable := fun x => forall a, x a

instance Pred_strongGammaD (A : Type u) : Derivable (Pred_L A) where
  derivable := fun Phi x =>
    forall a, (forall y, Phi y -> y a) -> x a

instance Pred_SM (A : Type u) : Semantics (Pred_L A) ({ model := A } : Model.{u}) where
  denotation := fun x => x

end Unifysl
