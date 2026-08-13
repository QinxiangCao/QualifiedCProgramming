import SetsClass.SetsClass
import Lean.Elab.Tactic.Location

universe u v

namespace MonadLib

class Monad (M : Type u -> Type v) where
  bind {A B : Type u} : M A -> (A -> M B) -> M B
  ret {A : Type u} : A -> M A

class FMap (M : Type u -> Type v) where
  fmap {A B : Type u} : (A -> B) -> M A -> M B

abbrev bind {M : Type u -> Type v} [m : Monad M] {A B : Type u} :
    M A -> (A -> M B) -> M B :=
  m.bind

abbrev ret {M : Type u -> Type v} [m : Monad M] {A : Type u} : A -> M A :=
  m.ret

abbrev fmap {M : Type u -> Type v} [m : FMap M] {A B : Type u} :
    (A -> B) -> M A -> M B :=
  m.fmap

instance (priority := low) [Monad M] : Bind M where
  bind := MonadLib.bind

instance (priority := low) [Monad M] : Pure M where
  pure := MonadLib.ret

instance (priority := low) [FMap M] : Functor M where
  map := MonadLib.fmap

inductive CntOrBrk (A : Type u) (B : Type v) : Type (max u v) where
  | by_continue (a : A)
  | by_break (b : B)

export CntOrBrk (by_continue by_break)

namespace MonadNotation

scoped infixr:60 " ≫= " => MonadLib.bind
scoped notation "(" m " ≫=.)" => (fun f => MonadLib.bind f m)
scoped notation "(.≫= " f ")" => MonadLib.bind f
scoped notation "(≫=)" => (fun m f => MonadLib.bind f m)
scoped notation:61 x:60 " <- " c1:62 " ;; " c2:61 =>
  MonadLib.bind c1 (fun x => c2)
scoped notation:61 c1:62 " ;; " c2:61 =>
  MonadLib.bind c1 (fun _ => c2)

end MonadNotation

macro "unfold_monad" : tactic =>
  `(tactic| simp only [MonadLib.bind, MonadLib.ret, Monad.bind, Monad.ret])

macro "unfold_monad" " in " loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic| simp only [MonadLib.bind, MonadLib.ret, Monad.bind, Monad.ret] at $loc)

end MonadLib
