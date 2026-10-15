import Flocq.Core.Raux

namespace Flocq.Core.Defs

open Flocq.Core.Zaux Flocq.Core.Raux

/-! Lean migration of `flocq/src/Core/Defs.v` reached by FloatLib. -/

structure float (beta : radix) where
  Fnum : Int
  Fexp : Int

abbrev Float (beta : radix) (Fnum Fexp : Int) : float beta :=
  ⟨Fnum, Fexp⟩

noncomputable def F2R {beta : radix} (f : float beta) : Real :=
  (f.Fnum : Real) * bpow beta f.Fexp

def round_pred_total (P : Real -> Real -> Prop) : Prop :=
  forall x, exists f, P x f

def round_pred_monotone (P : Real -> Real -> Prop) : Prop :=
  forall x y f g, P x f -> P y g -> x <= y -> f <= g

def round_pred (P : Real -> Real -> Prop) : Prop :=
  round_pred_total P /\ round_pred_monotone P

end Flocq.Core.Defs

namespace Flocq.Core
export Defs (float Float F2R round_pred_total round_pred_monotone round_pred)
end Flocq.Core
