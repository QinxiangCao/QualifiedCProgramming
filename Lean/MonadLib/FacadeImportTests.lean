import MonadLib.StateRelMonad.StateRelMonad
import MonadLib.MonadErr.StateRelMonadErr

namespace FacadeImportTests

open AUXLib
open MonadLib
open MonadLib.MonadErr

#check StateRelMonad.Hoare
#check MonadLib.Hoare

example {A : Type} (a : A) :
    StateRelMonad.Hoare (fun _ : Int => True)
      (StateRelMonad.ret a) (fun r _ => r = a) := by
  hoare_auto

example {A : Type} (a : A) :
    Hoare (fun _ : Int => True)
      (MonadErr.ret a) (fun r _ => r = a) := by
  hoare_auto

example {Sigma A : Type} :
    AUXLib.Equivalence (@ProgramPO.equiv Sigma A) := inferInstance

example {Sigma A : Type} :
    AUXLib.Equivalence (@FP.equiv (program Sigma A) _) := inferInstance

example {Sigma A B : Type} (c0 c1 : program Sigma A)
    (k : A -> program Sigma B)
    (h0 : ProgramPO.equiv c0 ProgramPO.bot) :
    ProgramPO.equiv
      (MonadErr.bind (MonadLib.choice c0 c1) k)
      (MonadErr.bind c1 k) := by
  rel_rw [choice_r_equiv c0 c1 h0]
  exact AUXLib.Equivalence.refl _

end FacadeImportTests
