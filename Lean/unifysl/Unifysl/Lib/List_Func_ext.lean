import Unifysl.Lib.Equivalence_ext

/-
Coq inventory from unifysl-prp/lib/List_Func_ext.v:

Definitions:
- not_nil
- semi_group_fold

Instances:
- proper_fold_left
- proper_fold_left'
- Proper_perm_not_nil
- proper_semi_group_fold

Lemmas:
- monoid_fold_left_tail
- monoid_fold_left_head
- monoid_fold_symm
- monoid_fold_left_app
- proper_permutation_fold_left
- not_nil_app_l
- eq_nil_dec
- semi_group_fold_app
- semi_group_fold_concat
- comm_semi_group_fold_perm
- Forall2_impl
- Forall2_rev
-/

namespace Unifysl

open Relation_ext

private theorem foldl_proper_core {A : Type u} {B : Type v}
    {RA : relation A} {RB : relation B}
    (f : A -> B -> A) [Proper_f : Proper (RA ==> RB ==> RA) f] :
    forall {l1 l2 : List B}, List.Forall₂ RB l1 l2 ->
      forall {e1 e2 : A}, RA e1 e2 ->
        RA (List.foldl f e1 l1) (List.foldl f e2 l2) := by
  intro l1 l2 h
  induction h with
  | nil =>
      intro e1 e2 he
      simpa using he
  | cons hxy _ ih =>
      intro e1 e2 he
      simp [List.foldl]
      exact ih (Proper_f.proper e1 e2 he _ _ hxy)

private theorem forall2_refl_of {A : Type u} {R : A -> A -> Prop}
    (hrefl : forall x, R x x) :
    forall (l : List A), List.Forall₂ R l l := by
  intro l
  induction l with
  | nil =>
      exact List.Forall₂.nil
  | cons a l ih =>
      exact List.Forall₂.cons (hrefl a) ih

private theorem foldl_assoc_acc {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z))) :
    forall (x y : A) (l : List A),
      RA (List.foldl f (f x y) l) (f x (List.foldl f y l)) := by
  intro x y l
  induction l generalizing x y with
  | nil =>
      simpa using EqRA.refl (f x y)
  | cons z zs ih =>
      simp [List.foldl]
      have hstep :
          RA (List.foldl f (f (f x y) z) zs)
            (List.foldl f (f x (f y z)) zs) := by
        exact foldl_proper_core f (forall2_refl_of (fun a => EqRA.refl a) zs) (assoc x y z)
      have htail :
          RA (List.foldl f (f x (f y z)) zs)
            (f x (List.foldl f (f y z) zs)) := by
        exact ih x (f y z)
      exact EqRA.trans hstep htail

private theorem foldl_monoid_acc {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (e : A)
    (right_id : forall x, RA (f x e) x)
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z))) :
    forall (x : A) (l : List A),
      RA (List.foldl f x l) (f x (List.foldl f e l)) := by
  intro x l
  have hinit : RA x (f x e) := EqRA.symm (right_id x)
  have hfold :
      RA (List.foldl f x l) (List.foldl f (f x e) l) := by
    exact foldl_proper_core f (forall2_refl_of (fun a => EqRA.refl a) l) hinit
  have hassoc :
      RA (List.foldl f (f x e) l) (f x (List.foldl f e l)) := by
    exact foldl_assoc_acc (EqRA := EqRA) (f := f) assoc x e l
  exact EqRA.trans hfold hassoc

instance proper_fold_left {A : Type u} {B : Type v}
    {RA : relation A} {RB : relation B}
    {_EqRA : Equivalence RA} {_EqRB : Equivalence RB}
    (f : A -> B -> A) [Proper (RA ==> RB ==> RA) f] :
    Proper (List.Forall₂ RB ==> RA ==> RA) (fun l e => List.foldl f e l) where
  proper := by
    intro l1 l2 h e1 e2 he
    exact foldl_proper_core f h he

theorem monoid_fold_left_tail {A : Type u} {B : Type v}
    {RA : relation A} {RB : relation B}
    {EqRA : Equivalence RA} {_EqRB : Equivalence RB}
    {f : A -> B -> A} [Proper (RA ==> RB ==> RA) f]
    (e : A) (a : B) (l : List B) :
    RA (List.foldl f e (l ++ [a])) (f (List.foldl f e l) a) := by
  simpa using EqRA.refl (f (List.foldl f e l) a)

theorem monoid_fold_left_head {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (e a : A) (l : List A)
    (left_id : forall x, RA (f e x) x)
    (right_id : forall x, RA (f x e) x)
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z))) :
    RA (List.foldl f e (a :: l)) (f a (List.foldl f e l)) := by
  simp [List.foldl]
  have hhead :
      RA (List.foldl f (f e a) l) (List.foldl f a l) := by
    exact foldl_proper_core f (forall2_refl_of (fun x => EqRA.refl x) l) (left_id a)
  have htail :
      RA (List.foldl f a l) (f a (List.foldl f e l)) := by
    exact foldl_monoid_acc (EqRA := EqRA) (f := f) e right_id assoc a l
  exact EqRA.trans hhead htail

theorem monoid_fold_symm {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (e : A) (l : List A)
    (left_id : forall x, RA (f e x) x)
    (right_id : forall x, RA (f x e) x)
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z))) :
    RA (List.foldl f e l) (List.foldr f e l) := by
  induction l with
  | nil =>
      simpa using EqRA.refl e
  | cons a l ih =>
      have hhead :
          RA (List.foldl f e (a :: l)) (f a (List.foldl f e l)) :=
        monoid_fold_left_head (EqRA := EqRA) (f := f) e a l left_id right_id assoc
      have htail :
          RA (f a (List.foldl f e l)) (f a (List.foldr f e l)) := by
        exact (inferInstance : Proper (RA ==> RA ==> RA) f).proper
          a a (EqRA.refl a) (List.foldl f e l) (List.foldr f e l) ih
      simpa [List.foldr] using EqRA.trans hhead htail

theorem monoid_fold_left_app {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (e : A) (l l' : List A)
    (left_id : forall x, RA (f e x) x)
    (right_id : forall x, RA (f x e) x)
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z))) :
    RA (List.foldl f e (l ++ l')) (f (List.foldl f e l) (List.foldl f e l')) := by
  have _hleft_id := left_id
  simpa [List.foldl_append] using
    foldl_monoid_acc (EqRA := EqRA) (f := f) e right_id assoc (List.foldl f e l) l'

instance proper_fold_left' {A : Type u} {B : Type v}
    {RA : relation A} {RB : relation B}
    (f : A -> B -> A) [Proper (RA ==> RB ==> RA) f] :
    Proper (List.Forall₂ RB ==> RA ==> RA) (fun l e => List.foldl f e l) where
  proper := by
    intro l1 l2 h e1 e2 he
    exact foldl_proper_core f h he

theorem proper_permutation_fold_left {A : Type u} {B : Type v}
    {RA : relation A} {EqRA : Equivalence RA}
    (f : A -> B -> A) [Proper (RA ==> Eq ==> RA) f]
    (swap :
      forall x1 x2 y z, RA x1 x2 -> RA (f (f x1 y) z) (f (f x2 z) y)) :
    Proper (List.Perm ==> RA ==> RA) (fun l e => List.foldl f e l) := by
  constructor
  intro l l' hperm e e' he
  induction hperm generalizing e e' with
  | nil =>
      simpa using he
  | cons x hperm ih =>
      simp [List.foldl]
      have hstart : RA (f e x) (f e' x) :=
        (inferInstance : Proper (RA ==> Eq ==> RA) f).proper e e' he x x rfl
      exact ih (f e x) (f e' x) hstart
  | swap x y l =>
      simp [List.foldl]
      have hinit : RA (f (f e y) x) (f (f e' x) y) := swap e e' y x he
      exact foldl_proper_core f (forall2_refl_of (fun b : B => rfl) l) hinit
  | trans h₁ h₂ ih₁ ih₂ =>
      exact EqRA.trans (ih₁ e e' he) (ih₂ e' e' (EqRA.refl e'))

def not_nil {A : Type u} (l : List A) : Prop :=
  l ≠ []

inductive sumbool (P Q : Prop) : Type where
  | left : P -> sumbool P Q
  | right : Q -> sumbool P Q

theorem not_nil_app_l {A : Type u} :
    forall (l l' : List A), not_nil l -> not_nil (l ++ l') := by
  intro l l' h
  cases l with
  | nil =>
      exact False.elim (h rfl)
  | cons a xs =>
      intro hnil
      cases hnil

def eq_nil_dec {A : Type u} (l : List A) : sumbool (l = []) (not_nil l) := by
  cases l with
  | nil =>
      exact sumbool.left rfl
  | cons a xs =>
      exact sumbool.right (by intro h; cases h)

instance Proper_perm_not_nil {A : Type u} :
    Proper (List.Perm ==> Iff) (@not_nil A) where
  proper := by
    intro l l' hp
    constructor
    · intro hl hnil
      have hperm : l.Perm [] := by
        simpa [hnil] using hp
      exact hl (List.Perm.eq_nil hperm)
    · intro hl' hnil
      have hperm : l'.Perm [] := by
        simpa [hnil] using hp.symm
      exact hl' (List.Perm.eq_nil hperm)

def semi_group_fold {A : Type u} (default : A) (f : A -> A -> A) (l : List A) : A :=
  match l with
  | [] => default
  | a :: l0 => List.foldl f a l0

instance proper_semi_group_fold {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    (f : A -> A -> A) (default : A) [Proper (RA ==> RA ==> RA) f] :
    Proper (List.Forall₂ RA ==> RA) (semi_group_fold default f) where
  proper := by
    intro l1 l2 h
    cases h with
    | nil =>
        exact EqRA.refl default
    | cons hxy htail =>
        simp [semi_group_fold]
        exact foldl_proper_core f htail hxy

theorem semi_group_fold_app {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (default : A) (l l' : List A)
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z)))
    (hl : not_nil l) (hl' : not_nil l') :
    RA (semi_group_fold default f (l ++ l'))
      (f (semi_group_fold default f l) (semi_group_fold default f l')) := by
  cases l with
  | nil =>
      exact False.elim (hl rfl)
  | cons a l =>
      cases l' with
      | nil =>
          exact False.elim (hl' rfl)
      | cons b l' =>
          simpa [semi_group_fold, List.foldl_append] using
            foldl_assoc_acc (EqRA := EqRA) (f := f) assoc (List.foldl f a l) b l'

theorem semi_group_fold_concat {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (default : A) (ls : List (List A))
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z)))
    (hls : List.Forall not_nil ls) :
    RA (semi_group_fold default f (List.flatten ls))
      (semi_group_fold default f (List.map (semi_group_fold default f) ls)) := by
  induction ls with
  | nil =>
      simpa [semi_group_fold] using EqRA.refl default
  | cons l ls ih =>
      cases hls with
      | cons hl hls =>
          cases ls with
          | nil =>
              simpa [semi_group_fold] using EqRA.refl (semi_group_fold default f l)
          | cons l' ls =>
              have hflat_tail : not_nil (List.flatten (l' :: ls)) := by
                cases hls with
                | cons hl' _ =>
                    exact not_nil_app_l l' (List.flatten ls) hl'
              have hmap_tail :
                  not_nil (List.map (semi_group_fold default f) (l' :: ls)) := by
                simp [not_nil]
              have hflat :
                  RA (semi_group_fold default f (l ++ List.flatten (l' :: ls)))
                    (f (semi_group_fold default f l)
                      (semi_group_fold default f (List.flatten (l' :: ls)))) := by
                exact semi_group_fold_app (EqRA := EqRA) (f := f) default l (List.flatten (l' :: ls))
                  assoc hl hflat_tail
              have hih :
                  RA (semi_group_fold default f (List.flatten (l' :: ls)))
                    (semi_group_fold default f
                      (List.map (semi_group_fold default f) (l' :: ls))) := by
                exact ih hls
              have hmid :
                  RA
                    (f (semi_group_fold default f l)
                      (semi_group_fold default f (List.flatten (l' :: ls))))
                    (f (semi_group_fold default f l)
                      (semi_group_fold default f
                        (List.map (semi_group_fold default f) (l' :: ls)))) := by
                exact (inferInstance : Proper (RA ==> RA ==> RA) f).proper
                  (semi_group_fold default f l) (semi_group_fold default f l)
                  (EqRA.refl (semi_group_fold default f l))
                  (semi_group_fold default f (List.flatten (l' :: ls)))
                  (semi_group_fold default f
                    (List.map (semi_group_fold default f) (l' :: ls)))
                  hih
              have hmap :
                  RA
                    (f (semi_group_fold default f l)
                      (semi_group_fold default f
                        (List.map (semi_group_fold default f) (l' :: ls))))
                    (semi_group_fold default f
                      (semi_group_fold default f l ::
                        List.map (semi_group_fold default f) (l' :: ls))) := by
                have happ :=
                  semi_group_fold_app (EqRA := EqRA) (f := f) default [semi_group_fold default f l]
                    (List.map (semi_group_fold default f) (l' :: ls))
                    assoc (by simp [not_nil]) hmap_tail
                simpa [semi_group_fold] using EqRA.symm happ
              simpa [List.flatten] using EqRA.trans hflat (EqRA.trans hmid hmap)

theorem comm_semi_group_fold_perm {A : Type u}
    {RA : relation A} {EqRA : Equivalence RA}
    {f : A -> A -> A} [Proper (RA ==> RA ==> RA) f]
    (default : A) (l l' : List A)
    (comm : forall x y, RA (f x y) (f y x))
    (assoc : forall x y z, RA (f (f x y) z) (f x (f y z)))
    (hperm : l.Perm l') :
    RA (semi_group_fold default f l) (semi_group_fold default f l') := by
  refine List.Perm.rec ?nil ?cons ?swap ?trans hperm
  · simpa [semi_group_fold] using EqRA.refl default
  · intro x l1 l2 hp ih
    cases l1 with
    | nil =>
        have hl2 : l2 = [] := List.Perm.eq_nil hp.symm
        subst l2
        simpa [semi_group_fold] using EqRA.refl x
    | cons a l1 =>
        cases l2 with
        | nil =>
            have hnil : a :: l1 = [] := List.Perm.eq_nil hp
            cases hnil
        | cons b l2 =>
            have hleft :
                RA (semi_group_fold default f (x :: a :: l1))
                  (f x (semi_group_fold default f (a :: l1))) := by
              have happ :=
                semi_group_fold_app (EqRA := EqRA) (f := f) default [x] (a :: l1)
                  assoc (by simp [not_nil]) (by simp [not_nil])
              simpa [semi_group_fold] using happ
            have hmid :
                RA (f x (semi_group_fold default f (a :: l1)))
                  (f x (semi_group_fold default f (b :: l2))) := by
              exact (inferInstance : Proper (RA ==> RA ==> RA) f).proper
                x x (EqRA.refl x)
                (semi_group_fold default f (a :: l1))
                (semi_group_fold default f (b :: l2))
                ih
            have hright :
                RA (f x (semi_group_fold default f (b :: l2)))
                  (semi_group_fold default f (x :: b :: l2)) := by
              have happ :=
                semi_group_fold_app (EqRA := EqRA) (f := f) default [x] (b :: l2)
                  assoc (by simp [not_nil]) (by simp [not_nil])
              simpa [semi_group_fold] using EqRA.symm happ
            exact EqRA.trans hleft (EqRA.trans hmid hright)
  · intro x y l
    cases l with
    | nil =>
        simpa [semi_group_fold] using comm y x
    | cons z l =>
        have hleft :
            RA (semi_group_fold default f (y :: x :: z :: l))
              (f (semi_group_fold default f [y, x])
                (semi_group_fold default f (z :: l))) := by
          exact semi_group_fold_app (EqRA := EqRA) (f := f) default [y, x] (z :: l)
            assoc (by simp [not_nil]) (by simp [not_nil])
        have hbase :
            RA (semi_group_fold default f [y, x])
              (semi_group_fold default f [x, y]) := by
          simpa [semi_group_fold] using comm y x
        have hmid :
            RA
              (f (semi_group_fold default f [y, x])
                (semi_group_fold default f (z :: l)))
              (f (semi_group_fold default f [x, y])
                (semi_group_fold default f (z :: l))) := by
          exact (inferInstance : Proper (RA ==> RA ==> RA) f).proper
            (semi_group_fold default f [y, x])
            (semi_group_fold default f [x, y])
            hbase
            (semi_group_fold default f (z :: l))
            (semi_group_fold default f (z :: l))
            (EqRA.refl (semi_group_fold default f (z :: l)))
        have hright :
            RA
              (f (semi_group_fold default f [x, y])
                (semi_group_fold default f (z :: l)))
              (semi_group_fold default f (x :: y :: z :: l)) := by
          have happ :=
            semi_group_fold_app (EqRA := EqRA) (f := f) default [x, y] (z :: l)
              assoc (by simp [not_nil]) (by simp [not_nil])
          exact EqRA.symm happ
        exact EqRA.trans hleft (EqRA.trans hmid hright)
  · intro l1 l2 l3 _ _ ih1 ih2
    exact EqRA.trans ih1 ih2

theorem Forall2_impl {A : Type u} {B : Type v} (P Q : A -> B -> Prop)
    (hPQ : forall a b, P a b -> Q a b) :
    forall (lA : List A) (lB : List B),
      List.Forall₂ P lA lB -> List.Forall₂ Q lA lB := by
  intro lA lB h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hp _ ih =>
      exact List.Forall₂.cons (hPQ _ _ hp) ih

theorem Forall2_rev {A : Type u} {B : Type v} (P : A -> B -> Prop) :
    forall (lA : List A) (lB : List B),
      List.Forall₂ (fun b a => P a b) lB lA -> List.Forall₂ P lA lB := by
  intro lA lB h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hp _ ih =>
      exact List.Forall₂.cons hp ih

end Unifysl
