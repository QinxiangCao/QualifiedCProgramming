universe u v

namespace AUXLib

class Reflexive {A : Sort u} (R : A -> A -> Prop) : Prop where
  refl : forall x, R x x

class Symmetric {A : Sort u} (R : A -> A -> Prop) : Prop where
  symm : forall x y, R x y -> R y x

class Transitive {A : Sort u} (R : A -> A -> Prop) : Prop where
  trans : forall x y z, R x y -> R y z -> R x z

class Equivalence {A : Sort u} (R : A -> A -> Prop) : Prop where
  refl : forall x, R x x
  symm : forall x y, R x y -> R y x
  trans : forall x y z, R x y -> R y z -> R x z

def respectful {A : Sort u} {B : Sort v}
    (RA : A -> A -> Prop) (RB : B -> B -> Prop) : (A -> B) -> (A -> B) -> Prop :=
  fun f g => forall x y, RA x y -> RB (f x) (g y)

infixr:55 " ==> " => respectful

def dependentPointwise {A : Sort u} {B : A -> Sort v}
    (R : forall x, B x -> B x -> Prop) :
    (forall x, B x) -> (forall x, B x) -> Prop :=
  fun f g => forall x, R x (f x) (g x)

abbrev pointwise_relation (A : Sort u) {B : Sort v}
    (R : B -> B -> Prop) : (A -> B) -> (A -> B) -> Prop :=
  dependentPointwise (fun _ => R)

def flipRel {A : Sort u} (R : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => R y x

abbrev ImplRel (P Q : Prop) : Prop :=
  P -> Q

def implication (P Q : Prop) : Prop :=
  P -> Q

def forallBinder {A : Sort u} (P : A -> Prop) : Prop :=
  forall x, P x

class Proper {A : Sort u} (R : A -> A -> Prop) (x : A) : Prop where
  proper : R x x

class ForwardTransport (R : Prop -> Prop -> Prop) : Prop where
  transport : forall {P Q : Prop}, R P Q -> P -> Q

class BackwardTransport (R : Prop -> Prop -> Prop) : Prop where
  transport : forall {P Q : Prop}, R P Q -> Q -> P

theorem forward_transport {R : Prop -> Prop -> Prop} [ForwardTransport R]
    {P Q : Prop} (hPQ : R P Q) (hP : P) : Q :=
  ForwardTransport.transport hPQ hP

theorem backward_transport {R : Prop -> Prop -> Prop} [BackwardTransport R]
    {P Q : Prop} (hPQ : R P Q) (hQ : Q) : P :=
  BackwardTransport.transport hPQ hQ

instance (priority := low) equivalence_reflexive {A : Sort u} (R : A -> A -> Prop)
    [h : Equivalence R] : Reflexive R where
  refl := h.refl

instance (priority := low) equivalence_symmetric {A : Sort u} (R : A -> A -> Prop)
    [h : Equivalence R] : Symmetric R where
  symm := h.symm

instance (priority := low) equivalence_transitive {A : Sort u} (R : A -> A -> Prop)
    [h : Equivalence R] : Transitive R where
  trans := h.trans

instance (priority := low) flipRel_reflexive {A : Sort u} (R : A -> A -> Prop)
    [h : Reflexive R] : Reflexive (flipRel R) where
  refl := h.refl

instance pointwise_relation_reflexive {A : Sort u} {B : Sort v}
    (R : B -> B -> Prop) [h : Reflexive R] : Reflexive (pointwise_relation A R) where
  refl f x := h.refl (f x)

instance eq_equivalence {A : Sort u} : Equivalence (@Eq A) where
  refl x := Eq.refl x
  symm _ _ h := Eq.symm h
  trans _ _ _ hxy hyz := Eq.trans hxy hyz

instance iff_equivalence : Equivalence Iff where
  refl _ := Iff.rfl
  symm _ _ h := Iff.symm h
  trans _ _ _ hpq hqr := Iff.trans hpq hqr

instance iff_forward_transport : ForwardTransport Iff where
  transport := Iff.mp

instance iff_backward_transport : BackwardTransport Iff where
  transport := Iff.mpr

instance eq_forward_transport : ForwardTransport (@Eq Prop) where
  transport h := h.mp

instance eq_backward_transport : BackwardTransport (@Eq Prop) where
  transport h := h.mpr

instance implRel_forward_transport :
    ForwardTransport ImplRel where
  transport h := h

instance implication_forward_transport :
    ForwardTransport implication where
  transport h := h

instance (priority := low) flipRel_backward_transport (R : Prop -> Prop -> Prop)
    [h : ForwardTransport R] : BackwardTransport (flipRel R) where
  transport hPQ := h.transport hPQ

instance (priority := low) flipRel_forward_transport (R : Prop -> Prop -> Prop)
    [h : BackwardTransport R] : ForwardTransport (flipRel R) where
  transport hPQ := h.transport hPQ

instance implRel_reflexive : Reflexive ImplRel where
  refl _ h := h

instance implication_reflexive : Reflexive implication where
  refl _ h := h

instance proper_eq {A : Sort u} : Proper (Eq ==> Eq ==> Iff) (@Eq A) where
  proper _ _ hxy _ _ huv := by
    subst hxy
    subst huv
    rfl

instance proper_iff : Proper (Iff ==> Iff ==> Iff) Iff where
  proper p p' hp q q' hq := by
    constructor <;> intro h
    · constructor
      · intro hp'
        exact hq.mp (h.mp (hp.mpr hp'))
      · intro hq'
        exact hp.mp (h.mpr (hq.mpr hq'))
    · constructor
      · intro hp0
        exact hq.mpr (h.mp (hp.mp hp0))
      · intro hq0
        exact hp.mpr (h.mpr (hq.mp hq0))

instance and_proper_iff : Proper (Iff ==> Iff ==> Iff) And where
  proper _ _ hp _ _ hq := and_congr hp hq

instance and_proper_flipped_iff :
    Proper (flipRel Iff ==> flipRel Iff ==> flipRel Iff) And where
  proper _ _ hp _ _ hq := and_congr hp hq

instance or_proper_iff : Proper (Iff ==> Iff ==> Iff) Or where
  proper _ _ hp _ _ hq := or_congr hp hq

instance or_proper_flipped_iff :
    Proper (flipRel Iff ==> flipRel Iff ==> flipRel Iff) Or where
  proper _ _ hp _ _ hq := or_congr hp hq

instance implication_proper_eq : Proper (Eq ==> Eq ==> Eq) implication where
  proper _ _ hp _ _ hq := by
    subst hp
    subst hq
    rfl

instance implication_proper_iff : Proper (Iff ==> Iff ==> Iff) implication where
  proper p p' hp q q' hq := by
    constructor
    · intro h hp'
      exact hq.mp (h (hp.mpr hp'))
    · intro h hp0
      exact hq.mpr (h (hp.mp hp0))

instance implication_proper_impl :
    Proper (flipRel implication ==> implication ==> implication) implication where
  proper _ _ hp _ _ hq hImp hp0 :=
    hq (hImp (hp hp0))

instance (priority := low) implication_proper_transport
    (R : Prop -> Prop -> Prop) [ForwardTransport R] :
    Proper (flipRel R ==> R ==> ImplRel) implication where
  proper _ _ hp _ _ hq hImp hp0 :=
    forward_transport hq (hImp (forward_transport hp hp0))

instance forallBinder_proper_eq {A : Sort u} :
    Proper (pointwise_relation A Eq ==> Eq) (@forallBinder A) where
  proper p q hp := by
    apply congrArg forallBinder
    funext x
    exact hp x

instance forallBinder_proper_iff {A : Sort u} :
    Proper (pointwise_relation A Iff ==> Iff) (@forallBinder A) where
  proper p q hp := by
    constructor
    · intro hall x
      exact (hp x).mp (hall x)
    · intro hall x
      exact (hp x).mpr (hall x)

instance forallBinder_proper_impl {A : Sort u} :
    Proper (pointwise_relation A implication ==> implication) (@forallBinder A) where
  proper _ _ hp hall x := hp x (hall x)

instance (priority := low) forallBinder_proper_transport {A : Sort u}
    (R : Prop -> Prop -> Prop) [ForwardTransport R] :
    Proper (pointwise_relation A R ==> ImplRel) (@forallBinder A) where
  proper _ _ hp hall x := forward_transport (hp x) (hall x)

instance exists_proper_eq {A : Sort u} :
    Proper (pointwise_relation A Eq ==> Eq) (@Exists A) where
  proper p q hp := by
    apply congrArg Exists
    funext x
    exact hp x

instance exists_proper_iff {A : Sort u} :
    Proper (pointwise_relation A Iff ==> Iff) (@Exists A) where
  proper p q hp := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (hp x).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (hp x).mpr hx⟩

instance exists_proper_impl {A : Sort u} :
    Proper (pointwise_relation A implication ==> implication) (@Exists A) where
  proper _ _ hp := by
    rintro ⟨x, hx⟩
    exact ⟨x, hp x hx⟩

instance (priority := low) exists_proper_transport {A : Sort u}
    (R : Prop -> Prop -> Prop) [ForwardTransport R] :
    Proper (pointwise_relation A R ==> ImplRel) (@Exists A) where
  proper _ _ hp := by
    rintro ⟨x, hx⟩
    exact ⟨x, forward_transport (hp x) hx⟩

set_option synthInstance.checkSynthOrder false in
instance (priority := low) proper_apply
    {A : Sort u} {B : Sort v} {RA : A -> A -> Prop} {RB : B -> B -> Prop}
    (f : A -> B) (x : A) [hf : Proper (RA ==> RB) f] [hr : Reflexive RA] :
    Proper RB (f x) where
  proper := hf.proper x x (hr.refl x)

end AUXLib
