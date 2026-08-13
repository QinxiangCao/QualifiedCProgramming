import Std.Tactic
import AUXLib.Morphisms
import SetsClass.SetElement

universe u

open AUXLib

namespace Sets

class SETS (T : Type u) where
  full : T
  empty : T
  prop_inj : Prop -> T
  complement : T -> T
  intersect : T -> T -> T
  union : T -> T -> T
  indexed_intersect : {I : Type u} -> (I -> T) -> T
  indexed_union : {I : Type u} -> (I -> T) -> T
  equiv : T -> T -> Prop
  included : T -> T -> Prop
  Taux : Type u -> Type u
  Qaux : {T0 : Type u} -> (T0 -> Prop) -> Taux T0
  Paux : {T0 : Type u} -> (T0 -> T) -> Taux T0
  conj_aux : {T0 : Type u} -> Taux T0 -> Taux T0 -> Taux T0
  imply_aux : {T0 : Type u} -> Taux T0 -> Taux T0 -> Taux T0
  forall_aux : {T0 : Type u} -> Taux T0 -> T
  exists_aux : {T0 : Type u} -> Taux T0 -> T
  inj_aux : {T0 : Type u} -> T -> Taux T0
  derives_aux : {T0 : Type u} -> Taux T0 -> Taux T0 -> T0 -> Prop

abbrev full {T : Type u} [sets : SETS T] : T := sets.full

abbrev empty {T : Type u} [sets : SETS T] : T := sets.empty

abbrev prop_inj {T : Type u} [sets : SETS T] (P : Prop) : T := sets.prop_inj P

abbrev complement {T : Type u} [sets : SETS T] (x : T) : T := sets.complement x

abbrev intersect {T : Type u} [sets : SETS T] (x y : T) : T := sets.intersect x y

abbrev union {T : Type u} [sets : SETS T] (x y : T) : T := sets.union x y

abbrev indexed_intersect {I T : Type u} [sets : SETS T]
    (xs : I -> T) : T := sets.indexed_intersect xs

abbrev indexed_union {I T : Type u} [sets : SETS T]
    (xs : I -> T) : T := sets.indexed_union xs

abbrev equiv {T : Type u} [sets : SETS T] (x y : T) : Prop := sets.equiv x y

abbrev included {T : Type u} [sets : SETS T] (x y : T) : Prop := sets.included x y

abbrev Taux {T : Type u} [sets : SETS T] (T0 : Type u) : Type u := sets.Taux T0

abbrev Qaux {T T0 : Type u} [sets : SETS T] (P : T0 -> Prop) : sets.Taux T0 :=
  sets.Qaux P

abbrev Paux {T T0 : Type u} [sets : SETS T] (P : T0 -> T) : sets.Taux T0 :=
  sets.Paux P

abbrev conj_aux {T T0 : Type u} [sets : SETS T]
    (x y : sets.Taux T0) : sets.Taux T0 :=
  sets.conj_aux x y

abbrev imply_aux {T T0 : Type u} [sets : SETS T]
    (x y : sets.Taux T0) : sets.Taux T0 :=
  sets.imply_aux x y

abbrev forall_aux {T T0 : Type u} [sets : SETS T] (x : sets.Taux T0) : T :=
  sets.forall_aux x

abbrev exists_aux {T T0 : Type u} [sets : SETS T] (x : sets.Taux T0) : T :=
  sets.exists_aux x

abbrev inj_aux {T T0 : Type u} [sets : SETS T] (x : T) : sets.Taux T0 :=
  sets.inj_aux x

abbrev derives_aux {T T0 : Type u} [sets : SETS T]
    (x y : sets.Taux T0) (t0 : T0) : Prop := sets.derives_aux x y t0

def general_union {T : Type u} [SETS T] (P : T -> Prop) : T :=
  exists_aux (conj_aux (Qaux P) (Paux fun x => x))

def general_intersect {T : Type u} [SETS T] (P : T -> Prop) : T :=
  forall_aux (imply_aux (Qaux P) (Paux fun x => x))

def singleton {A : Type u} (a : A) : A -> Prop := fun x => a = x

def test1 {A B : Type u} [SETS B] (P : A -> Prop) : A -> B :=
  fun a => prop_inj (P a)

def lift1 {A B : Type u} [SETS B] (x : B) : A -> B := fun _ => x

def filter1 {A B : Type u} [SETS B] (P : A -> Prop) (x : A -> B) : A -> B :=
  fun a => intersect (test1 P a) (x a)

def projB {A B : Type u} (s : A × B -> Prop) : B -> Prop :=
  fun b => exists a, s (a, b)

instance Prop_SETS : SETS Prop where
  full := True
  empty := False
  prop_inj := id
  complement := Not
  intersect := And
  union := Or
  indexed_intersect := fun xs => forall i, xs i
  indexed_union := fun xs => exists i, xs i
  equiv := Iff
  included := fun P Q => P -> Q
  Taux := fun T0 => T0 -> Prop
  Qaux := fun P a => P a
  Paux := fun P a => P a
  conj_aux := fun x y a => x a ∧ y a
  imply_aux := fun x y a => x a -> y a
  forall_aux := fun P => forall x, P x
  exists_aux := fun P => exists x, P x
  inj_aux := fun P _ => P
  derives_aux := fun x y t0 => x t0 -> y t0

instance lift_SETS (A B : Type u) [sets : SETS B] : SETS (A -> B) where
  full := fun _ => full
  empty := fun _ => empty
  prop_inj := fun P _ => prop_inj P
  complement := fun x a => complement (x a)
  intersect := fun x y a => intersect (x a) (y a)
  union := fun x y a => union (x a) (y a)
  indexed_intersect := fun xs a => indexed_intersect (fun i => xs i a)
  indexed_union := fun xs a => indexed_union (fun i => xs i a)
  equiv := fun x y => forall a, equiv (x a) (y a)
  included := fun x y => forall a, included (x a) (y a)
  Taux := fun T0 => A -> Taux T0
  Qaux := fun P _ => Qaux P
  Paux := fun P a => Paux (fun t => P t a)
  conj_aux := fun x y a => conj_aux (x a) (y a)
  imply_aux := fun x y a => imply_aux (x a) (y a)
  forall_aux := fun x a => forall_aux (x a)
  exists_aux := fun x a => exists_aux (x a)
  inj_aux := fun x a => inj_aux (x a)
  derives_aux := fun x y t0 => forall a, derives_aux (x a) (y a) t0

end Sets

class SETS_Properties (T : Type u) [Sets.SETS T] : Prop where
  Sets_included_refl : Reflexive (@Sets.included T _)
  Sets_included_trans : Transitive (@Sets.included T _)
  Sets_equiv_Sets_included : forall x y : T,
    Sets.equiv x y <-> (Sets.included x y /\ Sets.included y x)
  Sets_empty_included : forall x : T, Sets.included Sets.empty x
  Sets_included_full : forall x : T, Sets.included x Sets.full
  Sets_prop_inj_included : forall (P : Prop) (x y : T),
    (P -> Sets.included x y) ->
      Sets.included (Sets.intersect (Sets.prop_inj P) x) y
  Sets_included_prop_inj : forall (P : Prop) (x : T),
    P -> Sets.included x (Sets.prop_inj P)
  Sets_complement_fact : forall x y : T,
    Sets.included x (Sets.complement y) <->
      Sets.equiv (Sets.intersect x y) Sets.empty
  Sets_intersect_included1 : forall x y : T,
    Sets.included (Sets.intersect x y) x
  Sets_intersect_included2 : forall x y : T,
    Sets.included (Sets.intersect x y) y
  Sets_included_intersect : forall x y z : T,
    Sets.included x y -> Sets.included x z ->
      Sets.included x (Sets.intersect y z)
  Sets_included_union1 : forall x y : T,
    Sets.included x (Sets.union x y)
  Sets_included_union2 : forall x y : T,
    Sets.included y (Sets.union x y)
  Sets_union_included_strong2 : forall x y z u : T,
    Sets.included (Sets.intersect x u) z ->
    Sets.included (Sets.intersect y u) z ->
      Sets.included (Sets.intersect (Sets.union x y) u) z
  Sets_indexed_union_included_strong2 : forall {I : Type u}
      (xs : I -> T) (z u : T),
    (forall i, Sets.included (Sets.intersect (xs i) u) z) ->
      Sets.included (Sets.intersect (Sets.indexed_union xs) u) z
  Sets_included_indexed_union : forall {I : Type u} (n : I) (xs : I -> T),
    Sets.included (xs n) (Sets.indexed_union xs)
  Sets_indexed_union_included : forall {I : Type u} (xs : I -> T) (y : T),
    (forall n, Sets.included (xs n) y) ->
      Sets.included (Sets.indexed_union xs) y
  Sets_indexed_intersect_included : forall {I : Type u} (n : I) (xs : I -> T),
    Sets.included (Sets.indexed_intersect xs) (xs n)
  Sets_included_indexed_intersect : forall {I : Type u} (xs : I -> T) (y : T),
    (forall n, Sets.included y (xs n)) ->
      Sets.included y (Sets.indexed_intersect xs)
  Sets_included_derives_aux : forall {T0 : Type u}
      (x y : T) (t0 : T0),
    Sets.included x y ->
      Sets.derives_aux (Sets.inj_aux x) (Sets.inj_aux y) t0
  Sets_derives_aux_trans : forall {T0 : Type u} (t0 : T0),
    Transitive (fun x y : @Sets.Taux T _ T0 => Sets.derives_aux x y t0)
  Sets_Qaux_right : forall {T0 : Type u} (t0 : T0)
      (Pr : T0 -> Prop) (P : @Sets.Taux T _ T0),
    Pr t0 -> Sets.derives_aux P (Sets.Qaux Pr) t0
  Sets_Paux_left : forall {T0 : Type u} (t0 : T0) (inj : T0 -> T),
    Sets.derives_aux (Sets.Paux inj) (Sets.inj_aux (inj t0)) t0
  Sets_Paux_right : forall {T0 : Type u} (t0 : T0) (inj : T0 -> T),
    Sets.derives_aux (Sets.inj_aux (inj t0)) (Sets.Paux inj) t0
  Sets_Qaux_left_extract : forall {T0 : Type u} (t0 : T0)
      (Pr : T0 -> Prop) (Q1 Q2 : @Sets.Taux T _ T0),
    (Pr t0 -> Sets.derives_aux Q1 Q2 t0) ->
      Sets.derives_aux (Sets.conj_aux (Sets.Qaux Pr) Q1) Q2 t0
  Sets_Qaux_right_extract : forall {T0 : Type u} (t0 : T0)
      (Pr : T0 -> Prop) (Q1 Q2 : @Sets.Taux T _ T0),
    (Pr t0 -> Sets.derives_aux Q1 Q2 t0) ->
      Sets.derives_aux Q1 (Sets.imply_aux (Sets.Qaux Pr) Q2) t0
  Sets_Qaux_implies_left : forall {T0 : Type u} (t0 : T0)
      (Pr : T0 -> Prop) (Q1 Q2 : @Sets.Taux T _ T0),
    Pr t0 -> Sets.derives_aux Q1 Q2 t0 ->
      Sets.derives_aux (Sets.imply_aux (Sets.Qaux Pr) Q1) Q2 t0
  Sets_conj_aux_right : forall {T0 : Type u} (t0 : T0)
      (P Q1 Q2 : @Sets.Taux T _ T0),
    Sets.derives_aux P Q1 t0 -> Sets.derives_aux P Q2 t0 ->
      Sets.derives_aux P (Sets.conj_aux Q1 Q2) t0
  Sets_exists_aux_left : forall {T0 : Type u} (P : T)
      (Q : @Sets.Taux T _ T0),
    (forall t0, Sets.derives_aux Q (Sets.inj_aux P) t0) ->
      Sets.included (Sets.exists_aux Q) P
  Sets_exists_aux_right : forall {T0 : Type u} (t0 : T0)
      (P : T) (Q : @Sets.Taux T _ T0),
    Sets.derives_aux (Sets.inj_aux P) Q t0 ->
      Sets.included P (Sets.exists_aux Q)
  Sets_forall_aux_left : forall {T0 : Type u} (t0 : T0)
      (P : T) (Q : @Sets.Taux T _ T0),
    Sets.derives_aux Q (Sets.inj_aux P) t0 ->
      Sets.included (Sets.forall_aux Q) P
  Sets_forall_aux_right : forall {T0 : Type u} (P : T)
      (Q : @Sets.Taux T _ T0),
    (forall t0, Sets.derives_aux (Sets.inj_aux P) Q t0) ->
      Sets.included P (Sets.forall_aux Q)

instance Sets_included_refl {T : Type u} [Sets.SETS T] [p : SETS_Properties T] :
    Reflexive (@Sets.included T _) := p.Sets_included_refl

instance Sets_included_trans {T : Type u} [Sets.SETS T] [p : SETS_Properties T] :
    Transitive (@Sets.included T _) := p.Sets_included_trans

instance Prop_SETS_Properties : SETS_Properties Prop where
  Sets_included_refl := ⟨by intro P h; exact h⟩
  Sets_included_trans := ⟨by intro P Q R hPQ hQR hP; exact hQR (hPQ hP)⟩
  Sets_equiv_Sets_included := by
    intro P Q
    change (P <-> Q) <-> ((P -> Q) /\ (Q -> P))
    constructor
    · intro h; exact ⟨h.mp, h.mpr⟩
    · rintro ⟨hPQ, hQP⟩; exact ⟨hPQ, hQP⟩
  Sets_empty_included := by intro _ h; exact h.elim
  Sets_included_full := by intro _ _; trivial
  Sets_prop_inj_included := by
    intro P X Y h hPX
    exact h hPX.1 hPX.2
  Sets_included_prop_inj := by intro P _ hP _; exact hP
  Sets_complement_fact := by
    intro P Q
    change (P -> Not Q) <-> ((P /\ Q) <-> False)
    constructor
    · intro h
      constructor
      · rintro ⟨hP, hQ⟩; exact h hP hQ
      · intro hFalse; exact hFalse.elim
    · intro h hP hQ
      exact h.mp ⟨hP, hQ⟩
  Sets_intersect_included1 := by intro _ _ h; exact h.1
  Sets_intersect_included2 := by intro _ _ h; exact h.2
  Sets_included_intersect := by
    intro X Y Z hXY hXZ hX
    exact ⟨hXY hX, hXZ hX⟩
  Sets_included_union1 := by intro _ _ h; exact Or.inl h
  Sets_included_union2 := by intro _ _ h; exact Or.inr h
  Sets_union_included_strong2 := by
    intro X Y Z U hX hY h
    exact h.1.elim (fun hx => hX ⟨hx, h.2⟩) (fun hy => hY ⟨hy, h.2⟩)
  Sets_indexed_union_included_strong2 := by
    intro I xs Z U h hxu
    rcases hxu.1 with ⟨i, hi⟩
    exact h i ⟨hi, hxu.2⟩
  Sets_included_indexed_union := by intro I n xs h; exact ⟨n, h⟩
  Sets_indexed_union_included := by
    intro I xs Y h
    rintro ⟨i, hi⟩
    exact h i hi
  Sets_indexed_intersect_included := by intro I n xs h; exact h n
  Sets_included_indexed_intersect := by intro I xs Y h hY n; exact h n hY
  Sets_included_derives_aux := by intro T0 X Y t h hX; exact h hX
  Sets_derives_aux_trans := by
    intro T0 t
    exact ⟨by intro X Y Z hXY hYZ hX; exact hYZ (hXY hX)⟩
  Sets_Qaux_right := by intro T0 t Pr P hPr _; exact hPr
  Sets_Paux_left := by intro T0 t inj h; exact h
  Sets_Paux_right := by intro T0 t inj h; exact h
  Sets_Qaux_left_extract := by intro T0 t Pr Q1 Q2 h hq; exact h hq.1 hq.2
  Sets_Qaux_right_extract := by intro T0 t Pr Q1 Q2 h hq hPr; exact h hPr hq
  Sets_Qaux_implies_left := by intro T0 t Pr Q1 Q2 hPr h hImp; exact h (hImp hPr)
  Sets_conj_aux_right := by intro T0 t P Q1 Q2 h1 h2 hP; exact ⟨h1 hP, h2 hP⟩
  Sets_exists_aux_left := by
    intro T0 P Q h
    rintro ⟨t, hQt⟩
    exact h t hQt
  Sets_exists_aux_right := by intro T0 t P Q h hP; exact ⟨t, h hP⟩
  Sets_forall_aux_left := by intro T0 t P Q h hQ; exact h (hQ t)
  Sets_forall_aux_right := by intro T0 P Q h hP t; exact h t hP

instance lift_SETS_Properties (A B : Type u) [Sets.SETS B]
    [p : SETS_Properties B] : SETS_Properties (A -> B) where
  Sets_included_refl := ⟨by intro X a; exact p.Sets_included_refl.refl (X a)⟩
  Sets_included_trans := ⟨by
    intro X Y Z hXY hYZ a
    exact p.Sets_included_trans.trans _ _ _ (hXY a) (hYZ a)⟩
  Sets_equiv_Sets_included := by
    intro X Y
    constructor
    · intro h
      constructor
      · intro a; exact (p.Sets_equiv_Sets_included _ _).mp (h a) |>.1
      · intro a; exact (p.Sets_equiv_Sets_included _ _).mp (h a) |>.2
    · rintro ⟨hXY, hYX⟩ a
      exact (p.Sets_equiv_Sets_included _ _).mpr ⟨hXY a, hYX a⟩
  Sets_empty_included := by intro X a; exact p.Sets_empty_included (X a)
  Sets_included_full := by intro X a; exact p.Sets_included_full (X a)
  Sets_prop_inj_included := by
    intro P X Y h a
    exact p.Sets_prop_inj_included P (X a) (Y a) (fun hP => h hP a)
  Sets_included_prop_inj := by
    intro P X hP a
    exact p.Sets_included_prop_inj P (X a) hP
  Sets_complement_fact := by
    intro X Y
    constructor
    · intro h a; exact (p.Sets_complement_fact (X a) (Y a)).mp (h a)
    · intro h a; exact (p.Sets_complement_fact (X a) (Y a)).mpr (h a)
  Sets_intersect_included1 := by
    intro X Y a; exact p.Sets_intersect_included1 (X a) (Y a)
  Sets_intersect_included2 := by
    intro X Y a; exact p.Sets_intersect_included2 (X a) (Y a)
  Sets_included_intersect := by
    intro X Y Z hXY hXZ a
    exact p.Sets_included_intersect (X a) (Y a) (Z a) (hXY a) (hXZ a)
  Sets_included_union1 := by intro X Y a; exact p.Sets_included_union1 (X a) (Y a)
  Sets_included_union2 := by intro X Y a; exact p.Sets_included_union2 (X a) (Y a)
  Sets_union_included_strong2 := by
    intro X Y Z U hX hY a
    exact p.Sets_union_included_strong2 (X a) (Y a) (Z a) (U a) (hX a) (hY a)
  Sets_indexed_union_included_strong2 := by
    intro I xs Z U h a
    exact p.Sets_indexed_union_included_strong2 (fun i => xs i a) (Z a) (U a)
      (fun i => h i a)
  Sets_included_indexed_union := by
    intro I n xs a
    exact p.Sets_included_indexed_union n (fun i => xs i a)
  Sets_indexed_union_included := by
    intro I xs Y h a
    exact p.Sets_indexed_union_included (fun i => xs i a) (Y a) (fun i => h i a)
  Sets_indexed_intersect_included := by
    intro I n xs a
    exact p.Sets_indexed_intersect_included n (fun i => xs i a)
  Sets_included_indexed_intersect := by
    intro I xs Y h a
    exact p.Sets_included_indexed_intersect (fun i => xs i a) (Y a) (fun i => h i a)
  Sets_included_derives_aux := by
    intro T0 X Y t h a
    exact p.Sets_included_derives_aux (X a) (Y a) t (h a)
  Sets_derives_aux_trans := by
    intro T0 t
    exact ⟨by
      intro X Y Z hXY hYZ a
      exact (p.Sets_derives_aux_trans t).trans _ _ _ (hXY a) (hYZ a)⟩
  Sets_Qaux_right := by
    intro T0 t Pr P hPr a
    exact p.Sets_Qaux_right t Pr (P a) hPr
  Sets_Paux_left := by intro T0 t inj a; exact p.Sets_Paux_left t (fun x => inj x a)
  Sets_Paux_right := by intro T0 t inj a; exact p.Sets_Paux_right t (fun x => inj x a)
  Sets_Qaux_left_extract := by
    intro T0 t Pr Q1 Q2 h a
    exact p.Sets_Qaux_left_extract t Pr (Q1 a) (Q2 a) (fun hPr => h hPr a)
  Sets_Qaux_right_extract := by
    intro T0 t Pr Q1 Q2 h a
    exact p.Sets_Qaux_right_extract t Pr (Q1 a) (Q2 a) (fun hPr => h hPr a)
  Sets_Qaux_implies_left := by
    intro T0 t Pr Q1 Q2 hPr h a
    exact p.Sets_Qaux_implies_left t Pr (Q1 a) (Q2 a) hPr (h a)
  Sets_conj_aux_right := by
    intro T0 t P Q1 Q2 h1 h2 a
    exact p.Sets_conj_aux_right t (P a) (Q1 a) (Q2 a) (h1 a) (h2 a)
  Sets_exists_aux_left := by
    intro T0 P Q h a
    exact p.Sets_exists_aux_left (P a) (Q a) (fun t => h t a)
  Sets_exists_aux_right := by
    intro T0 t P Q h a
    exact p.Sets_exists_aux_right t (P a) (Q a) (h a)
  Sets_forall_aux_left := by
    intro T0 t P Q h a
    exact p.Sets_forall_aux_left t (P a) (Q a) (h a)
  Sets_forall_aux_right := by
    intro T0 P Q h a
    exact p.Sets_forall_aux_right (P a) (Q a) (fun t => h t a)

class SETS_Algebra_Properties (T : Type u) [Sets.SETS T] : Prop where
  equiv_refl : forall x : T, Sets.equiv x x
  equiv_symm : forall x y : T, Sets.equiv x y -> Sets.equiv y x
  equiv_trans : forall x y z : T, Sets.equiv x y -> Sets.equiv y z -> Sets.equiv x z
  union_comm : forall x y : T, Sets.equiv (Sets.union x y) (Sets.union y x)
  union_assoc : forall x y z : T,
    Sets.equiv (Sets.union (Sets.union x y) z) (Sets.union x (Sets.union y z))
  intersect_comm : forall x y : T, Sets.equiv (Sets.intersect x y) (Sets.intersect y x)
  intersect_assoc : forall x y z : T,
    Sets.equiv (Sets.intersect (Sets.intersect x y) z)
      (Sets.intersect x (Sets.intersect y z))
  intersect_union_distr_r : forall x y z : T,
    Sets.equiv (Sets.intersect (Sets.union x y) z)
      (Sets.union (Sets.intersect x z) (Sets.intersect y z))
  intersect_union_distr_l : forall x y z : T,
    Sets.equiv (Sets.intersect x (Sets.union y z))
      (Sets.union (Sets.intersect x y) (Sets.intersect x z))
  union_intersect_distr_r : forall x y z : T,
    Sets.equiv (Sets.union (Sets.intersect x y) z)
      (Sets.intersect (Sets.union x z) (Sets.union y z))
  union_intersect_distr_l : forall x y z : T,
    Sets.equiv (Sets.union x (Sets.intersect y z))
      (Sets.intersect (Sets.union x y) (Sets.union x z))
  union_empty_r : forall x : T, Sets.equiv (Sets.union x Sets.empty) x
  union_empty_l : forall x : T, Sets.equiv (Sets.union Sets.empty x) x
  intersect_empty_r : forall x : T, Sets.equiv (Sets.intersect x Sets.empty) Sets.empty
  intersect_empty_l : forall x : T, Sets.equiv (Sets.intersect Sets.empty x) Sets.empty
  intersect_full_r : forall x : T, Sets.equiv (Sets.intersect x Sets.full) x
  intersect_full_l : forall x : T, Sets.equiv (Sets.intersect Sets.full x) x
  complement_self_intersect : forall x : T,
    Sets.equiv (Sets.intersect (Sets.complement x) x) Sets.empty
  complement_union : forall x y : T,
    Sets.equiv (Sets.complement (Sets.union x y))
      (Sets.intersect (Sets.complement x) (Sets.complement y))

instance Prop_SETS_Algebra_Properties : SETS_Algebra_Properties Prop where
  equiv_refl := by intro P; change P ↔ P; rfl
  equiv_symm := by
    intro P Q h
    change P ↔ Q at h
    change Q ↔ P
    exact h.symm
  equiv_trans := by
    intro P Q R hPQ hQR
    change P ↔ Q at hPQ
    change Q ↔ R at hQR
    change P ↔ R
    exact hPQ.trans hQR
  union_comm := by
    intro P Q
    change P ∨ Q ↔ Q ∨ P
    exact or_comm
  union_assoc := by
    intro P Q R
    change (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R
    exact or_assoc
  intersect_comm := by
    intro P Q
    change P ∧ Q ↔ Q ∧ P
    exact and_comm
  intersect_assoc := by
    intro P Q R
    change (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R
    exact and_assoc
  intersect_union_distr_r := by
    intro P Q R
    change (P ∨ Q) ∧ R ↔ P ∧ R ∨ Q ∧ R
    exact or_and_right
  intersect_union_distr_l := by
    intro P Q R
    change P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
    exact and_or_left
  union_intersect_distr_r := by
    intro P Q R
    change P ∧ Q ∨ R ↔ (P ∨ R) ∧ (Q ∨ R)
    exact and_or_right
  union_intersect_distr_l := by
    intro P Q R
    change P ∨ Q ∧ R ↔ (P ∨ Q) ∧ (P ∨ R)
    exact or_and_left
  union_empty_r := by intro P; change P ∨ False ↔ P; simp
  union_empty_l := by intro P; change False ∨ P ↔ P; simp
  intersect_empty_r := by intro P; change P ∧ False ↔ False; simp
  intersect_empty_l := by intro P; change False ∧ P ↔ False; simp
  intersect_full_r := by intro P; change P ∧ True ↔ P; simp
  intersect_full_l := by intro P; change True ∧ P ↔ P; simp
  complement_self_intersect := by
    intro P
    change (Not P ∧ P) ↔ False
    simp
  complement_union := by
    intro P Q
    change Not (P ∨ Q) ↔ Not P ∧ Not Q
    exact not_or

instance lift_SETS_Algebra_Properties (A B : Type u)
    [Sets.SETS B] [SETS_Algebra_Properties B] : SETS_Algebra_Properties (A -> B) where
  equiv_refl := by intro x a; exact SETS_Algebra_Properties.equiv_refl (x a)
  equiv_symm := by intro x y h a; exact SETS_Algebra_Properties.equiv_symm _ _ (h a)
  equiv_trans := by
    intro x y z hxy hyz a
    exact SETS_Algebra_Properties.equiv_trans _ _ _ (hxy a) (hyz a)
  union_comm := by intro x y a; exact SETS_Algebra_Properties.union_comm (x a) (y a)
  union_assoc := by intro x y z a; exact SETS_Algebra_Properties.union_assoc (x a) (y a) (z a)
  intersect_comm := by intro x y a; exact SETS_Algebra_Properties.intersect_comm (x a) (y a)
  intersect_assoc := by
    intro x y z a
    exact SETS_Algebra_Properties.intersect_assoc (x a) (y a) (z a)
  intersect_union_distr_r := by
    intro x y z a
    exact SETS_Algebra_Properties.intersect_union_distr_r (x a) (y a) (z a)
  intersect_union_distr_l := by
    intro x y z a
    exact SETS_Algebra_Properties.intersect_union_distr_l (x a) (y a) (z a)
  union_intersect_distr_r := by
    intro x y z a
    exact SETS_Algebra_Properties.union_intersect_distr_r (x a) (y a) (z a)
  union_intersect_distr_l := by
    intro x y z a
    exact SETS_Algebra_Properties.union_intersect_distr_l (x a) (y a) (z a)
  union_empty_r := by intro x a; exact SETS_Algebra_Properties.union_empty_r (x a)
  union_empty_l := by intro x a; exact SETS_Algebra_Properties.union_empty_l (x a)
  intersect_empty_r := by intro x a; exact SETS_Algebra_Properties.intersect_empty_r (x a)
  intersect_empty_l := by intro x a; exact SETS_Algebra_Properties.intersect_empty_l (x a)
  intersect_full_r := by intro x a; exact SETS_Algebra_Properties.intersect_full_r (x a)
  intersect_full_l := by intro x a; exact SETS_Algebra_Properties.intersect_full_l (x a)
  complement_self_intersect := by
    intro x a
    exact SETS_Algebra_Properties.complement_self_intersect (x a)
  complement_union := by
    intro x y a
    exact SETS_Algebra_Properties.complement_union (x a) (y a)

theorem Sets_equiv_Sets_included {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y : T) :
    Sets.equiv x y <-> (Sets.included x y /\ Sets.included y x) :=
  p.Sets_equiv_Sets_included x y

theorem Sets_empty_included {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x : T) : Sets.included Sets.empty x :=
  p.Sets_empty_included x

theorem Sets_included_full {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x : T) : Sets.included x Sets.full :=
  p.Sets_included_full x

theorem Sets_prop_inj_included {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (P : Prop) (x y : T)
    (h : P -> Sets.included x y) :
    Sets.included (Sets.intersect (Sets.prop_inj P) x) y :=
  p.Sets_prop_inj_included P x y h

theorem Sets_included_prop_inj {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (P : Prop) (x : T) (hP : P) :
    Sets.included x (Sets.prop_inj P) :=
  p.Sets_included_prop_inj P x hP

theorem Sets_complement_fact {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y : T) :
    Sets.included x (Sets.complement y) <->
      Sets.equiv (Sets.intersect x y) Sets.empty :=
  p.Sets_complement_fact x y

theorem Sets_intersect_included1 {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y : T) :
    Sets.included (Sets.intersect x y) x :=
  p.Sets_intersect_included1 x y

theorem Sets_intersect_included2 {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y : T) :
    Sets.included (Sets.intersect x y) y :=
  p.Sets_intersect_included2 x y

theorem Sets_included_intersect {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y z : T)
    (hxy : Sets.included x y) (hxz : Sets.included x z) :
    Sets.included x (Sets.intersect y z) :=
  p.Sets_included_intersect x y z hxy hxz

theorem Sets_included_union1 {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y : T) :
    Sets.included x (Sets.union x y) :=
  p.Sets_included_union1 x y

theorem Sets_included_union2 {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y : T) :
    Sets.included y (Sets.union x y) :=
  p.Sets_included_union2 x y

theorem Sets_union_included_strong2 {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (x y z u : T)
    (hx : Sets.included (Sets.intersect x u) z)
    (hy : Sets.included (Sets.intersect y u) z) :
    Sets.included (Sets.intersect (Sets.union x y) u) z :=
  p.Sets_union_included_strong2 x y z u hx hy

theorem Sets_indexed_union_included_strong2 {I T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (xs : I -> T) (z u : T)
    (h : forall i, Sets.included (Sets.intersect (xs i) u) z) :
    Sets.included (Sets.intersect (Sets.indexed_union xs) u) z :=
  p.Sets_indexed_union_included_strong2 xs z u h

theorem Sets_included_indexed_union {I T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (n : I) (xs : I -> T) :
    Sets.included (xs n) (Sets.indexed_union xs) :=
  p.Sets_included_indexed_union n xs

theorem Sets_indexed_union_included {I T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (xs : I -> T) (y : T)
    (h : forall n, Sets.included (xs n) y) :
    Sets.included (Sets.indexed_union xs) y :=
  p.Sets_indexed_union_included xs y h

theorem Sets_indexed_intersect_included {I T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (n : I) (xs : I -> T) :
    Sets.included (Sets.indexed_intersect xs) (xs n) :=
  p.Sets_indexed_intersect_included n xs

theorem Sets_included_indexed_intersect {I T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (xs : I -> T) (y : T)
    (h : forall n, Sets.included y (xs n)) :
    Sets.included y (Sets.indexed_intersect xs) :=
  p.Sets_included_indexed_intersect xs y h

theorem Sets_included_general_union {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (xs : T -> Prop) (x : T) (hx : xs x) :
    Sets.included x (Sets.general_union xs) := by
  apply p.Sets_exists_aux_right x x
  apply p.Sets_conj_aux_right x
  · exact p.Sets_Qaux_right x xs (Sets.inj_aux x) hx
  · exact p.Sets_Paux_right x (fun y : T => y)

theorem Sets_general_union_included {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (xs : T -> Prop) (y : T)
    (h : forall x, xs x -> Sets.included x y) :
    Sets.included (Sets.general_union xs) y := by
  apply p.Sets_exists_aux_left y
  intro x
  apply p.Sets_Qaux_left_extract x xs
  intro hx
  exact (p.Sets_derives_aux_trans x).trans _ (Sets.inj_aux x) _
    (p.Sets_Paux_left x (fun z : T => z))
    (p.Sets_included_derives_aux x y x (h x hx))

theorem Sets_general_intersect_included {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (xs : T -> Prop) (x : T) (hx : xs x) :
    Sets.included (Sets.general_intersect xs) x := by
  apply p.Sets_forall_aux_left x x
  exact p.Sets_Qaux_implies_left x xs (Sets.Paux fun z : T => z)
    (Sets.inj_aux x) hx (p.Sets_Paux_left x (fun z : T => z))

theorem Sets_included_general_intersect {T : Type u} [Sets.SETS T]
    [p : SETS_Properties T] (xs : T -> Prop) (y : T)
    (h : forall x, xs x -> Sets.included y x) :
    Sets.included y (Sets.general_intersect xs) := by
  apply p.Sets_forall_aux_right y
  intro x
  apply p.Sets_Qaux_right_extract x xs
  intro hx
  exact (p.Sets_derives_aux_trans x).trans _ (Sets.inj_aux x) _
    (p.Sets_included_derives_aux y x x (h x hx))
    (p.Sets_Paux_right x (fun z : T => z))

private theorem source_equiv_of_included {T : Type u} [Sets.SETS T]
    [SETS_Properties T] {x y : T}
    (hxy : Sets.included x y) (hyx : Sets.included y x) : Sets.equiv x y :=
  (Sets_equiv_Sets_included x y).mpr ⟨hxy, hyx⟩

private theorem source_union_included {T : Type u} [Sets.SETS T]
    [SETS_Properties T] {x y z : T}
    (hx : Sets.included x z) (hy : Sets.included y z) :
    Sets.included (Sets.union x y) z := by
  apply Sets_included_trans.trans _ (Sets.intersect (Sets.union x y) Sets.full) _
  · exact Sets_included_intersect _ _ _ (Sets_included_refl.refl _) (Sets_included_full _)
  · apply Sets_union_included_strong2
    · exact Sets_included_trans.trans _ x _ (Sets_intersect_included1 _ _) hx
    · exact Sets_included_trans.trans _ y _ (Sets_intersect_included1 _ _) hy

theorem Sets_equiv_refl {T : Type u} [Sets.SETS T] [SETS_Properties T] (x : T) :
    Sets.equiv x x :=
  source_equiv_of_included (Sets_included_refl.refl x) (Sets_included_refl.refl x)

theorem Sets_equiv_symm {T : Type u} [Sets.SETS T] [SETS_Properties T]
    {x y : T} (h : Sets.equiv x y) : Sets.equiv y x := by
  rcases (Sets_equiv_Sets_included x y).mp h with ⟨hxy, hyx⟩
  exact source_equiv_of_included hyx hxy

instance Sets_equiv_sym {T : Type u} [Sets.SETS T] [SETS_Properties T] :
    Symmetric (@Sets.equiv T _) := ⟨by intro x y; exact Sets_equiv_symm⟩

theorem Sets_equiv_trans {T : Type u} [Sets.SETS T] [SETS_Properties T]
    {x y z : T} (hxy : Sets.equiv x y) (hyz : Sets.equiv y z) : Sets.equiv x z := by
  rcases (Sets_equiv_Sets_included x y).mp hxy with ⟨hxy, hyx⟩
  rcases (Sets_equiv_Sets_included y z).mp hyz with ⟨hyz, hzy⟩
  exact source_equiv_of_included
    (Sets_included_trans.trans _ _ _ hxy hyz)
    (Sets_included_trans.trans _ _ _ hzy hyx)

instance Sets_equiv_equiv {T : Type u} [Sets.SETS T] [SETS_Properties T] :
    AUXLib.Equivalence (@Sets.equiv T _) where
  refl := Sets_equiv_refl
  symm := by intro _ _; exact Sets_equiv_symm
  trans := by intro _ _ _; exact Sets_equiv_trans

theorem Sets_union_comm {T : Type u} [Sets.SETS T] [SETS_Properties T] (x y : T) :
    Sets.equiv (Sets.union x y) (Sets.union y x) :=
  source_equiv_of_included
    (source_union_included
      (Sets_included_union2 y x) (Sets_included_union1 y x))
    (source_union_included
      (Sets_included_union2 x y) (Sets_included_union1 x y))

theorem Sets_union_assoc {T : Type u} [Sets.SETS T] [SETS_Properties T] (x y z : T) :
    Sets.equiv (Sets.union (Sets.union x y) z) (Sets.union x (Sets.union y z)) := by
  apply source_equiv_of_included
  · apply source_union_included
    · apply source_union_included
      · exact Sets_included_union1 x (Sets.union y z)
      · exact Sets_included_trans.trans _ (Sets.union y z) _
          (Sets_included_union1 y z) (Sets_included_union2 x (Sets.union y z))
    · exact Sets_included_trans.trans _ (Sets.union y z) _
        (Sets_included_union2 y z) (Sets_included_union2 x (Sets.union y z))
  · apply source_union_included
    · exact Sets_included_trans.trans _ (Sets.union x y) _
        (Sets_included_union1 x y) (Sets_included_union1 (Sets.union x y) z)
    · apply source_union_included
      · exact Sets_included_trans.trans _ (Sets.union x y) _
          (Sets_included_union2 x y) (Sets_included_union1 (Sets.union x y) z)
      · exact Sets_included_union2 (Sets.union x y) z

theorem Sets_intersect_comm {T : Type u} [Sets.SETS T] [SETS_Properties T] (x y : T) :
    Sets.equiv (Sets.intersect x y) (Sets.intersect y x) :=
  source_equiv_of_included
    (Sets_included_intersect _ _ _
      (Sets_intersect_included2 x y) (Sets_intersect_included1 x y))
    (Sets_included_intersect _ _ _
      (Sets_intersect_included2 y x) (Sets_intersect_included1 y x))

theorem Sets_intersect_assoc {T : Type u} [Sets.SETS T] [SETS_Properties T] (x y z : T) :
    Sets.equiv (Sets.intersect (Sets.intersect x y) z)
      (Sets.intersect x (Sets.intersect y z)) := by
  apply source_equiv_of_included
  · apply Sets_included_intersect
    · exact Sets_included_trans.trans _ (Sets.intersect x y) _
        (Sets_intersect_included1 _ _) (Sets_intersect_included1 _ _)
    · apply Sets_included_intersect
      · exact Sets_included_trans.trans _ (Sets.intersect x y) _
          (Sets_intersect_included1 _ _) (Sets_intersect_included2 _ _)
      · exact Sets_intersect_included2 _ _
  · apply Sets_included_intersect
    · apply Sets_included_intersect
      · exact Sets_intersect_included1 _ _
      · exact Sets_included_trans.trans _ (Sets.intersect y z) _
          (Sets_intersect_included2 _ _) (Sets_intersect_included1 _ _)
    · exact Sets_included_trans.trans _ (Sets.intersect y z) _
        (Sets_intersect_included2 _ _) (Sets_intersect_included2 _ _)

theorem Sets_intersect_union_distr_r {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T]
    (x y z : T) :
    Sets.equiv (Sets.intersect (Sets.union x y) z)
      (Sets.union (Sets.intersect x z) (Sets.intersect y z)) :=
  SETS_Algebra_Properties.intersect_union_distr_r x y z

theorem Sets_intersect_union_distr_l {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T]
    (x y z : T) :
    Sets.equiv (Sets.intersect x (Sets.union y z))
      (Sets.union (Sets.intersect x y) (Sets.intersect x z)) :=
  SETS_Algebra_Properties.intersect_union_distr_l x y z

theorem Sets_union_intersect_distr_r {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T]
    (x y z : T) :
    Sets.equiv (Sets.union (Sets.intersect x y) z)
      (Sets.intersect (Sets.union x z) (Sets.union y z)) :=
  SETS_Algebra_Properties.union_intersect_distr_r x y z

theorem Sets_union_intersect_distr_l {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T]
    (x y z : T) :
    Sets.equiv (Sets.union x (Sets.intersect y z))
      (Sets.intersect (Sets.union x y) (Sets.union x z)) :=
  SETS_Algebra_Properties.union_intersect_distr_l x y z

theorem Sets_union_empty {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T] (x : T) :
    Sets.equiv (Sets.union x Sets.empty) x :=
  SETS_Algebra_Properties.union_empty_r x

theorem Sets_empty_union {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T] (x : T) :
    Sets.equiv (Sets.union Sets.empty x) x :=
  SETS_Algebra_Properties.union_empty_l x

theorem Sets_intersect_empty {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T] (x : T) :
    Sets.equiv (Sets.intersect x Sets.empty) Sets.empty :=
  SETS_Algebra_Properties.intersect_empty_r x

theorem Sets_empty_intersect {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T] (x : T) :
    Sets.equiv (Sets.intersect Sets.empty x) Sets.empty :=
  SETS_Algebra_Properties.intersect_empty_l x

theorem Sets_intersect_full {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T] (x : T) :
    Sets.equiv (Sets.intersect x Sets.full) x :=
  SETS_Algebra_Properties.intersect_full_r x

theorem Sets_full_intersect {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T] (x : T) :
    Sets.equiv (Sets.intersect Sets.full x) x :=
  SETS_Algebra_Properties.intersect_full_l x

theorem Sets_complement_self_intersect {T : Type u} [Sets.SETS T]
    [SETS_Algebra_Properties T] (x : T) :
    Sets.equiv (Sets.intersect (Sets.complement x) x) Sets.empty :=
  SETS_Algebra_Properties.complement_self_intersect x

theorem Sets_complement_union {T : Type u} [Sets.SETS T] [SETS_Algebra_Properties T]
    (x y : T) :
    Sets.equiv (Sets.complement (Sets.union x y))
      (Sets.intersect (Sets.complement x) (Sets.complement y)) :=
  SETS_Algebra_Properties.complement_union x y

macro "sets_unfold" : tactic =>
  `(tactic| first
    | simp only [Sets.full, Sets.empty, Sets.prop_inj, Sets.complement,
        Sets.intersect, Sets.union, Sets.indexed_intersect, Sets.indexed_union,
        Sets.equiv, Sets.included, Sets.general_intersect, Sets.general_union,
        Sets.Qaux, Sets.Paux, Sets.conj_aux, Sets.imply_aux, Sets.forall_aux,
        Sets.exists_aux, Sets.inj_aux, Sets.singleton,
        Sets.Prop_SETS, Sets.lift_SETS]
    | skip)

syntax "sets_unfold" " at " ident : tactic
macro_rules
  | `(tactic| sets_unfold at $h:ident) => do
      let location ← `(Lean.Parser.Tactic.location| at $h:ident)
      `(tactic| first
        | simp only [Sets.full, Sets.empty, Sets.prop_inj, Sets.complement,
            Sets.intersect, Sets.union, Sets.indexed_intersect, Sets.indexed_union,
            Sets.equiv, Sets.included, Sets.general_intersect, Sets.general_union,
            Sets.Qaux, Sets.Paux, Sets.conj_aux, Sets.imply_aux, Sets.forall_aux,
            Sets.exists_aux, Sets.inj_aux, Sets.singleton,
            Sets.Prop_SETS, Sets.lift_SETS] $location
        | skip)
