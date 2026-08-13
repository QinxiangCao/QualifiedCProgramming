import Std.Tactic
import AUXLib.Morphisms
import FP.BourbakiWitt
import SetsClass.RelsDomain

namespace AUXLib

def is_lb {A : Type} [Order A] (X : A -> Prop) (a : A) : Prop :=
  forall a', X a' -> order_rel a a'

def is_ub {A : Type} [Order A] (X : A -> Prop) (a : A) : Prop :=
  forall a', X a' -> order_rel a' a

def is_omega_lb {A : Type} [Order A] (l : Nat -> A) (a : A) : Prop :=
  forall n, order_rel a (l n)

def is_omega_ub {A : Type} [Order A] (l : Nat -> A) (a : A) : Prop :=
  forall n, order_rel (l n) a

def is_omega_lub {A : Type} [Order A] (l : Nat -> A) (a : A) : Prop :=
  is_omega_ub l a /\ is_lb (is_omega_ub l) a

theorem is_omega_lub_sound {A : Type} [Order A] {l : Nat -> A} {a : A}
    (h : is_omega_lub l a) : is_omega_ub l a := h.1

theorem is_omega_lub_tight {A : Type} [Order A] {l : Nat -> A} {a : A}
    (h : is_omega_lub l a) : is_lb (is_omega_ub l) a := h.2

class Reflexive_Setoid (A : Type) [Order A] [Equiv A] : Prop where
  reflexivity_setoid : forall a b : A, equiv a b -> order_rel a b

class AntiSymmetric_Setoid (A : Type) [Order A] [Equiv A] : Prop where
  antisymmetricity_setoid : forall a b : A,
    order_rel a b -> order_rel b a -> equiv a b

class PartialOrder_Setoid (A : Type) [Order A] [Equiv A] : Prop where
  PO_Reflexive_Setoid : Reflexive_Setoid A
  PO_Transitive : Transitive (@order_rel A _)
  PO_AntiSymmetric_Setoid : AntiSymmetric_Setoid A

instance relationsReflexiveSetoid (A : Type) [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] : Reflexive_Setoid A := p.PO_Reflexive_Setoid

instance relationsTransitive (A : Type) [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] : Transitive (@order_rel A _) := p.PO_Transitive

instance relationsAntiSymmetric (A : Type) [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] : AntiSymmetric_Setoid A := p.PO_AntiSymmetric_Setoid

instance PartialOrder_Setoid_Proper {A : Type} [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] [e : Equivalence (@equiv A _)] :
    Proper (@equiv A _ ==> @equiv A _ ==> Iff) (@order_rel A _) where
  proper x x' hxx y y' hyy := by
    constructor
    · intro hxy
      exact p.PO_Transitive.trans _ x _
        (p.PO_Reflexive_Setoid.reflexivity_setoid _ _ (e.symm _ _ hxx))
        (p.PO_Transitive.trans _ y _ hxy
          (p.PO_Reflexive_Setoid.reflexivity_setoid _ _ hyy))
    · intro hxy
      exact p.PO_Transitive.trans _ x' _
        (p.PO_Reflexive_Setoid.reflexivity_setoid _ _ hxx)
        (p.PO_Transitive.trans _ y' _ hxy
          (p.PO_Reflexive_Setoid.reflexivity_setoid _ _ (e.symm _ _ hyy)))

theorem same_omega_ub_same_omega_lub {A : Type} [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] (l1 l2 : Nat -> A) (a1 a2 : A)
    (hubs : Sets.equiv (is_omega_ub l1) (is_omega_ub l2))
    (h1 : is_omega_lub l1 a1) (h2 : is_omega_lub l2 a2) : equiv a1 a2 := by
  apply p.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
  · exact h1.2 a2 ((hubs a2).mpr h2.1)
  · exact h2.2 a1 ((hubs a1).mp h1.1)

class OmegaLub (A : Type) where
  omega_lub : (Nat -> A) -> A

class Bot (A : Type) where
  bot : A

abbrev omega_lub {A : Type} [o : OmegaLub A] : (Nat -> A) -> A := o.omega_lub
abbrev bot {A : Type} [b : Bot A] : A := b.bot

def increasing {A : Type} [Order A] (l : Nat -> A) : Prop :=
  forall n, order_rel (l n) (l (n + 1))

def is_least {A : Type} [Order A] (a : A) : Prop := forall a', order_rel a a'

class OmegaCompletePartialOrder_Setoid (A : Type) [Order A] [Equiv A]
    [OmegaLub A] [Bot A] : Prop where
  oCPO_PartialOrder : PartialOrder_Setoid A
  oCPO_completeness : forall T : Nat -> A,
    increasing T -> is_omega_lub T (omega_lub T)
  bot_is_least : @is_least A _ (@bot A _)

instance omegaCpoPartialOrder (A : Type) [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : OmegaCompletePartialOrder_Setoid A] : PartialOrder_Setoid A :=
  c.oCPO_PartialOrder

theorem same_omega_ub_same_omega_lub' {A : Type} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [c : OmegaCompletePartialOrder_Setoid A]
    (l1 l2 : Nat -> A)
    (hubs : Sets.equiv (is_omega_ub l1) (is_omega_ub l2))
    (h1 : increasing l1) (h2 : increasing l2) :
    equiv (omega_lub l1) (omega_lub l2) :=
  same_omega_ub_same_omega_lub l1 l2 _ _ hubs
    (c.oCPO_completeness l1 h1) (c.oCPO_completeness l2 h2)

def mono {A B : Type} [Order A] [Equiv A] [PartialOrder_Setoid A]
    [Order B] [Equiv B] [PartialOrder_Setoid B] (f : A -> B) : Prop :=
  forall a1 a2, order_rel a1 a2 -> order_rel (f a1) (f a2)

def continuous {A B : Type} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [OmegaCompletePartialOrder_Setoid A]
    [Order B] [Equiv B] [OmegaLub B] [Bot B]
    [OmegaCompletePartialOrder_Setoid B] (f : A -> B) : Prop :=
  forall l : Nat -> A, increasing l ->
    equiv (f (omega_lub l)) (omega_lub (fun n => f (l n)))

theorem id_mono {A : Type} [Order A] [Equiv A] [PartialOrder_Setoid A] :
    mono (fun x : A => x) := by intro _ _ h; exact h

theorem compose_mono {A B C : Type}
    [Order A] [Equiv A] [PartialOrder_Setoid A]
    [Order B] [Equiv B] [PartialOrder_Setoid B]
    [Order C] [Equiv C] [PartialOrder_Setoid C]
    (f : A -> B) (g : B -> C) (hf : mono f) (hg : mono g) :
    mono (fun x => g (f x)) := by intro a b h; exact hg _ _ (hf _ _ h)

theorem id_continuous {A : Type} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [OmegaCompletePartialOrder_Setoid A] [e : Equivalence (@equiv A _)] :
    continuous (fun x : A => x) := by intro _ _; exact e.refl _

theorem increasing_mono_increasing {A B : Type}
    [Order A] [Equiv A] [PartialOrder_Setoid A]
    [Order B] [Equiv B] [PartialOrder_Setoid B]
    (f : A -> B) (l : Nat -> A) (hl : increasing l) (hf : mono f) :
    increasing (fun n => f (l n)) := fun n => hf _ _ (hl n)

theorem mono_equiv_congr {A B : Type}
    [Order A] [Equiv A] [pA : PartialOrder_Setoid A]
    [Order B] [Equiv B] [pB : PartialOrder_Setoid B]
    [eA : Equivalence (@equiv A _)] (f : A -> B) (hf : mono f) :
    Proper (@equiv A _ ==> @equiv B _) f where
  proper x y hxy := by
    apply pB.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
    · exact hf _ _ (pA.PO_Reflexive_Setoid.reflexivity_setoid _ _ hxy)
    · exact hf _ _ (pA.PO_Reflexive_Setoid.reflexivity_setoid _ _ (eA.symm _ _ hxy))

theorem compose_continuous {A B C : Type}
    [Order A] [Equiv A] [OmegaLub A] [Bot A] [OmegaCompletePartialOrder_Setoid A]
    [Order B] [Equiv B] [OmegaLub B] [Bot B] [OmegaCompletePartialOrder_Setoid B]
    [Order C] [Equiv C] [OmegaLub C] [Bot C] [OmegaCompletePartialOrder_Setoid C]
    [eB : Equivalence (@equiv B _)] [eC : Equivalence (@equiv C _)]
    (f : A -> B) (g : B -> C) (hf : mono f) (hg : mono g)
    (hfc : continuous f) (hgc : continuous g) :
    continuous (fun x => g (f x)) := by
  intro l hl
  exact eC.trans _ _ _
    (mono_equiv_congr g hg |>.proper _ _ (hfc l hl))
    (hgc (fun n => f (l n)) (increasing_mono_increasing f l hl hf))

theorem iter_bot_increasing {A : Type} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : OmegaCompletePartialOrder_Setoid A] (f : A -> A) (hf : mono f) :
    increasing (fun n => FP.nat_iter n f bot) := by
  intro n
  induction n with
  | zero => exact c.bot_is_least (f bot)
  | succ n ih => simpa [FP.nat_iter] using hf _ _ ih

theorem iter_S_bot_increasing {A : Type} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [OmegaCompletePartialOrder_Setoid A] (f : A -> A) (hf : mono f) :
    increasing (fun n => f (FP.nat_iter n f bot)) :=
  increasing_mono_increasing f _ (iter_bot_increasing f hf) hf

def BW_LFix {A : Type} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [OmegaCompletePartialOrder_Setoid A] (f : A -> A) : A :=
  omega_lub (fun n => FP.nat_iter n f bot)

theorem BW_LFix_is_fix {A : Type} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : OmegaCompletePartialOrder_Setoid A] [e : Equivalence (@equiv A _)]
    (f : A -> A) (hf : mono f) (hcont : continuous f) :
    equiv (f (BW_LFix f)) (BW_LFix f) := by
  have hTail := hcont _ (iter_bot_increasing f hf)
  apply e.trans _ _ _ hTail
  apply same_omega_ub_same_omega_lub' _ _
  · intro a
    constructor
    · intro h n
      cases n with
      | zero => exact c.bot_is_least a
      | succ n => exact h n
    · intro h n; exact h (n + 1)
  · exact iter_S_bot_increasing f hf
  · exact iter_bot_increasing f hf

theorem BW_LFix_is_least_fix {A : Type} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : OmegaCompletePartialOrder_Setoid A] [e : Equivalence (@equiv A _)]
    (f : A -> A) (a : A) (hf : mono f) (_ : continuous f)
    (hfix : equiv (f a) a) : order_rel (BW_LFix f) a := by
  exact (c.oCPO_completeness _ (iter_bot_increasing f hf)).2 a (by
    intro n
    induction n with
    | zero => exact c.bot_is_least a
    | succ n ih =>
        exact c.oCPO_PartialOrder.PO_Transitive.trans _ (f a) _ (hf _ _ ih)
          (c.oCPO_PartialOrder.PO_Reflexive_Setoid.reflexivity_setoid _ _ hfix))

private def predOrder (P : Type) : Order P := ⟨fun _ _ => False⟩

instance R_while_err (A : Type) : Order (A -> Prop) := ⟨fun P Q => forall a, P a -> Q a⟩
instance Equiv_while_err (A : Type) : Equiv (A -> Prop) := ⟨fun P Q => forall a, P a <-> Q a⟩

instance PO_while_err (A : Type) : PartialOrder_Setoid (A -> Prop) where
  PO_Reflexive_Setoid := ⟨by intro P Q h a; exact (h a).mp⟩
  PO_Transitive := ⟨by intro P Q R hPQ hQR a hP; exact hQR a (hPQ a hP)⟩
  PO_AntiSymmetric_Setoid := ⟨by intro P Q hPQ hQP a; exact ⟨hPQ a, hQP a⟩⟩

instance oLub_while_err (A : Type) : OmegaLub (A -> Prop) :=
  ⟨fun T a => exists n, T n a⟩
instance Bot_while_err (A : Type) : Bot (A -> Prop) := ⟨fun _ => False⟩

instance oCPO_while_err (A : Type) : OmegaCompletePartialOrder_Setoid (A -> Prop) where
  oCPO_PartialOrder := PO_while_err A
  oCPO_completeness := by
    intro T _
    constructor
    · intro n a h; exact ⟨n, h⟩
    · intro bnd hbnd a
      rintro ⟨n, hn⟩
      exact hbnd n a hn
  bot_is_least := by intro _ _ h; exact h.elim

instance R_while_fin (A B : Type) : Order (A -> B -> Prop) :=
  ⟨fun P Q => forall a b, P a b -> Q a b⟩
instance Equiv_while_fin (A B : Type) : Equiv (A -> B -> Prop) :=
  ⟨fun P Q => forall a b, P a b <-> Q a b⟩

instance PO_while_fin (A B : Type) : PartialOrder_Setoid (A -> B -> Prop) where
  PO_Reflexive_Setoid := ⟨by intro P Q h a b; exact (h a b).mp⟩
  PO_Transitive := ⟨by intro P Q R hPQ hQR a b hP; exact hQR a b (hPQ a b hP)⟩
  PO_AntiSymmetric_Setoid := ⟨by intro P Q hPQ hQP a b; exact ⟨hPQ a b, hQP a b⟩⟩

instance oLub_while_fin (A B : Type) : OmegaLub (A -> B -> Prop) :=
  ⟨fun T a b => exists n, T n a b⟩
instance Bot_while_fin (A B : Type) : Bot (A -> B -> Prop) := ⟨fun _ _ => False⟩

instance oCPO_while_fin (A B : Type) : OmegaCompletePartialOrder_Setoid (A -> B -> Prop) where
  oCPO_PartialOrder := PO_while_fin A B
  oCPO_completeness := by
    intro T _
    constructor
    · intro n a b h; exact ⟨n, h⟩
    · intro bnd hbnd a b
      rintro ⟨n, hn⟩
      exact hbnd n a b hn
  bot_is_least := by intro _ _ _ h; exact h.elim

instance Equiv_equiv_while_fin (A B : Type) :
    Equivalence (@equiv (A -> B -> Prop) (Equiv_while_fin A B)) where
  refl P _ _ := Iff.rfl
  symm P Q h a b := (h a b).symm
  trans P Q R hPQ hQR a b := (hPQ a b).trans (hQR a b)

theorem BinRel_concat_left_mono (A B C : Type) (Y : A -> B -> Prop) :
    mono (fun X : B -> C -> Prop => (Rels.concat Y X : A -> C -> Prop)) := by
  intro X X' hX a c
  rintro ⟨b, hY, h⟩
  exact ⟨b, hY, hX b c h⟩

theorem BinRel_concat_omega_union_distr_l {A B C : Type}
    (R1 : A -> B -> Prop) (R2 : Nat -> B -> C -> Prop) :
    @equiv (A -> C -> Prop) (Equiv_while_fin A C)
      (Rels.concat R1 (fun b c => exists n, R2 n b c) : A -> C -> Prop)
      (fun a c => exists n, (Rels.concat R1 (R2 n) : A -> C -> Prop) a c) := by
  intro a c
  constructor
  · rintro ⟨b, hab, n, hbc⟩
    exact ⟨n, b, hab, hbc⟩
  · rintro ⟨n, b, hab, hbc⟩
    exact ⟨b, hab, n, hbc⟩

theorem BinRel_concat_left_continuous (A B C : Type) (Y : A -> B -> Prop) :
    continuous (fun X : B -> C -> Prop => (Rels.concat Y X : A -> C -> Prop)) := by
  intro l _
  exact BinRel_concat_omega_union_distr_l Y l

theorem BinRel_concat_left_mono_and_continuous (A B C : Type)
    (Y : A -> B -> Prop) (f : (B -> C -> Prop) -> B -> C -> Prop)
    (h : mono f /\ continuous f) :
    mono (fun X : B -> C -> Prop => (Rels.concat Y (f X) : A -> C -> Prop)) /\
      continuous (fun X : B -> C -> Prop => (Rels.concat Y (f X) : A -> C -> Prop)) :=
  ⟨compose_mono f _ h.1 (BinRel_concat_left_mono A B C Y),
    compose_continuous f _ h.1 (BinRel_concat_left_mono A B C Y) h.2
      (BinRel_concat_left_continuous A B C Y)⟩

theorem union_right2_mono (A B : Type) (Y : A -> B -> Prop) :
    mono (fun X : A -> B -> Prop => fun a b => X a b \/ Y a b) := by
  intro X X' h a b
  exact Or.imp (h a b) id

theorem union_right2_continuous (A B : Type) (Y : A -> B -> Prop) :
    continuous (fun X : A -> B -> Prop => fun a b => X a b \/ Y a b) := by
  intro l _ a b
  constructor
  · intro h
    rcases h with ⟨n, hn⟩ | hY
    · exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hY⟩
  · rintro ⟨n, hn | hY⟩
    · exact Or.inl ⟨n, hn⟩
    · exact Or.inr hY

theorem union_right2_mono_and_continuous (A B : Type) (Y : A -> B -> Prop)
    (f : (A -> B -> Prop) -> A -> B -> Prop) (h : mono f /\ continuous f) :
    mono (fun X : A -> B -> Prop => fun a b => f X a b \/ Y a b) /\
      continuous (fun X : A -> B -> Prop => fun a b => f X a b \/ Y a b) :=
  ⟨compose_mono f _ h.1 (union_right2_mono A B Y),
    compose_continuous f _ h.1 (union_right2_mono A B Y) h.2
      (union_right2_continuous A B Y)⟩

instance R_func (A B C : Type) : Order (A -> B -> C -> Prop) :=
  ⟨fun P Q => forall a b c, P a b c -> Q a b c⟩
instance Equiv_func (A B C : Type) : Equiv (A -> B -> C -> Prop) :=
  ⟨fun P Q => forall a b c, P a b c <-> Q a b c⟩

instance PO_func (A B C : Type) : PartialOrder_Setoid (A -> B -> C -> Prop) where
  PO_Reflexive_Setoid := ⟨by intro P Q h a b c; exact (h a b c).mp⟩
  PO_Transitive := ⟨by intro P Q R hPQ hQR a b c hP; exact hQR a b c (hPQ a b c hP)⟩
  PO_AntiSymmetric_Setoid := ⟨by intro P Q hPQ hQP a b c; exact ⟨hPQ a b c, hQP a b c⟩⟩

instance oLub_func (A B C : Type) : OmegaLub (A -> B -> C -> Prop) :=
  ⟨fun T a b c => exists n, T n a b c⟩
instance Bot_func (A B C : Type) : Bot (A -> B -> C -> Prop) :=
  ⟨fun _ _ _ => False⟩
instance oCPO_func (A B C : Type) :
    OmegaCompletePartialOrder_Setoid (A -> B -> C -> Prop) where
  oCPO_PartialOrder := PO_func A B C
  oCPO_completeness := by
    intro T _
    exact ⟨fun n a b c h => ⟨n, h⟩, fun _ hb a b c h => by
      rcases h with ⟨n, hn⟩; exact hb n a b c hn⟩
  bot_is_least := by intro _ _ _ _ h; exact h.elim

instance Equivalence_func (A B C : Type) :
    Equivalence (@equiv (A -> B -> C -> Prop) (Equiv_func A B C)) where
  refl _ _ _ _ := Iff.rfl
  symm _ _ h a b c := (h a b c).symm
  trans _ _ _ h1 h2 a b c := (h1 a b c).trans (h2 a b c)

instance R_whileret (A B C D : Type) : Order (A -> B -> C -> D -> Prop) :=
  ⟨fun P Q => forall a b c d, P a b c d -> Q a b c d⟩
instance Equiv_whileret (A B C D : Type) : Equiv (A -> B -> C -> D -> Prop) :=
  ⟨fun P Q => forall a b c d, P a b c d <-> Q a b c d⟩

instance PO_whileret (A B C D : Type) : PartialOrder_Setoid (A -> B -> C -> D -> Prop) where
  PO_Reflexive_Setoid := ⟨by intro P Q h a b c d; exact (h a b c d).mp⟩
  PO_Transitive := ⟨by intro P Q R h1 h2 a b c d h; exact h2 a b c d (h1 a b c d h)⟩
  PO_AntiSymmetric_Setoid := ⟨by intro P Q h1 h2 a b c d; exact ⟨h1 a b c d, h2 a b c d⟩⟩

instance oLub_whileret (A B C D : Type) : OmegaLub (A -> B -> C -> D -> Prop) :=
  ⟨fun T a b c d => exists n, T n a b c d⟩
instance Bot_whileret (A B C D : Type) : Bot (A -> B -> C -> D -> Prop) :=
  ⟨fun _ _ _ _ => False⟩
instance oCPO_whileret (A B C D : Type) :
    OmegaCompletePartialOrder_Setoid (A -> B -> C -> D -> Prop) where
  oCPO_PartialOrder := PO_whileret A B C D
  oCPO_completeness := by
    intro T _
    exact ⟨fun n a b c d h => ⟨n, h⟩, fun _ hb a b c d h => by
      rcases h with ⟨n, hn⟩; exact hb n a b c d hn⟩
  bot_is_least := by intro _ _ _ _ _ h; exact h.elim

instance Equivalence_whileret (A B C D : Type) :
    Equivalence (@equiv (A -> B -> C -> D -> Prop) (Equiv_whileret A B C D)) where
  refl _ _ _ _ _ := Iff.rfl
  symm _ _ h a b c d := (h a b c d).symm
  trans _ _ _ h1 h2 a b c d := (h1 a b c d).trans (h2 a b c d)

end AUXLib
