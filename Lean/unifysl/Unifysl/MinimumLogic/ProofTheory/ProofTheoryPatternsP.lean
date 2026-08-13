import Unifysl.MinimumLogic.ProofTheory.RewriteClass

/-!
Coq inventory from `MinimumLogic/ProofTheory/ProofTheoryPatternsP.v`:
- Classes: `Adjointness`, `Commutativity`, `Monotonicity`,
  `Associativity`, `LeftUnit`, `RightUnit`, `LeftDistr`, `RightDistr`.
- Class fields: `adjoint`, `prodp_comm_impp`, `prodp_mono`,
  `prodp_assoc1`, `prodp_assoc2`, `left_unit1`, `left_unit2`,
  `right_unit1`, `right_unit2`, `left_distr1`, `left_distr2`,
  `right_distr1`, `right_distr2`.
- Lemmas/instances: `prodp_mono1`, `funcp_mono2`,
  `adjoint_modus_ponens`, `adjoint_iter`, `Adjoint2Mono`, `funcp_mono`,
  `fold_left_mono`, `fold_right_mono`, `fold_left_mono2`,
  `fold_right_mono2`, `assoc_fold_left_cons`,
  `assoc_fold_right_cons`, `assoc_fold_left_fold_right`,
  `assoc_fold_right_fold_left`, `assoc_prodp_fold_left`,
  `assoc_fold_left_app`, `LeftDistr2RightDistr`, `RightDistr2LeftDistr`,
  `Build_Associativity1`, `Build_Associativity2`.
-/

universe u

namespace Unifysl.ProofTheoryPatternsP

class Adjointness (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  adjoint :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (prodp x y ⟶ z) <->
        @Provable.provable L Gamma (x ⟶ funcp y z)

class Commutativity (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (prodp : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  prodp_comm_impp :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (prodp x y ⟶ prodp y x)

class Monotonicity (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (prodp : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  prodp_mono :
    forall x1 y1 x2 y2 : @Language.expr L,
      @Provable.provable L Gamma (x1 ⟶ x2) ->
      @Provable.provable L Gamma (y1 ⟶ y2) ->
      @Provable.provable L Gamma (prodp x1 y1 ⟶ prodp x2 y2)

class Associativity (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (prodp : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  prodp_assoc1 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (prodp x (prodp y z) ⟶ prodp (prodp x y) z)
  prodp_assoc2 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (prodp (prodp x y) z ⟶ prodp x (prodp y z))

class LeftUnit (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (e : @Language.expr L)
    (prodp : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  left_unit1 :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (prodp e x ⟶ x)
  left_unit2 :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ prodp e x)

class RightUnit (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (e : @Language.expr L)
    (prodp : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  right_unit1 :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (prodp x e ⟶ x)
  right_unit2 :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ prodp x e)

class LeftDistr (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  left_distr1 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma
        (prodp x (sump y z) ⟶ sump (prodp x y) (prodp x z))
  left_distr2 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma
        (sump (prodp x y) (prodp x z) ⟶ prodp x (sump y z))

class RightDistr (L : Language.{u}) [MinimumLanguage L] (Gamma : Provable L)
    (prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L) :
    Prop where
  right_distr1 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma
        (prodp (sump y z) x ⟶ sump (prodp y x) (prodp z x))
  right_distr2 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma
        (sump (prodp y x) (prodp z x) ⟶ prodp (sump y z) x)

theorem adjoint {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Adj : Adjointness L Gamma prodp funcp] :
    forall x y z : @Language.expr L,
      (|-- (prodp x y ⟶ z)) <-> (|-- (x ⟶ funcp y z)) :=
  Adj.adjoint

theorem prodp_comm_impp {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Comm : Commutativity L Gamma prodp] :
    forall x y : @Language.expr L, |-- (prodp x y ⟶ prodp y x) :=
  Comm.prodp_comm_impp

theorem prodp_mono {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Mono : Monotonicity L Gamma prodp] :
    forall x1 y1 x2 y2 : @Language.expr L,
      (|-- (x1 ⟶ x2)) -> (|-- (y1 ⟶ y2)) ->
        |-- (prodp x1 y1 ⟶ prodp x2 y2) :=
  Mono.prodp_mono

theorem prodp_assoc1 {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Assoc : Associativity L Gamma prodp] :
    forall x y z : @Language.expr L,
      |-- (prodp x (prodp y z) ⟶ prodp (prodp x y) z) :=
  Assoc.prodp_assoc1

theorem prodp_assoc2 {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Assoc : Associativity L Gamma prodp] :
    forall x y z : @Language.expr L,
      |-- (prodp (prodp x y) z ⟶ prodp x (prodp y z)) :=
  Assoc.prodp_assoc2

theorem left_unit1 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [LU : LeftUnit L Gamma e prodp] :
    forall x : @Language.expr L, |-- (prodp e x ⟶ x) :=
  LU.left_unit1

theorem left_unit2 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [LU : LeftUnit L Gamma e prodp] :
    forall x : @Language.expr L, |-- (x ⟶ prodp e x) :=
  LU.left_unit2

theorem right_unit1 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [RU : RightUnit L Gamma e prodp] :
    forall x : @Language.expr L, |-- (prodp x e ⟶ x) :=
  RU.right_unit1

theorem right_unit2 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [RU : RightUnit L Gamma e prodp] :
    forall x : @Language.expr L, |-- (x ⟶ prodp x e) :=
  RU.right_unit2

theorem left_distr1 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [LDistr : LeftDistr L Gamma prodp sump] :
    forall x y z : @Language.expr L,
      |-- (prodp x (sump y z) ⟶ sump (prodp x y) (prodp x z)) :=
  LDistr.left_distr1

theorem left_distr2 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [LDistr : LeftDistr L Gamma prodp sump] :
    forall x y z : @Language.expr L,
      |-- (sump (prodp x y) (prodp x z) ⟶ prodp x (sump y z)) :=
  LDistr.left_distr2

theorem right_distr1 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [RDistr : RightDistr L Gamma prodp sump] :
    forall x y z : @Language.expr L,
      |-- (prodp (sump y z) x ⟶ sump (prodp y x) (prodp z x)) :=
  RDistr.right_distr1

theorem right_distr2 {L : Language.{u}} [MinimumLanguage L] [Gamma : Provable L]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [RDistr : RightDistr L Gamma prodp sump] :
    forall x y z : @Language.expr L,
      |-- (sump (prodp y x) (prodp z x) ⟶ prodp (sump y z) x) :=
  RDistr.right_distr2

section AdjointTheorems

variable {L : Language.{u}}
variable [MinimumLanguage L]
variable [Gamma : Provable L]
variable [minAX : MinimumAxiomatization L Gamma]
variable {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
variable [Adj : Adjointness L Gamma prodp funcp]
include minAX Adj

theorem prodp_mono1 :
    forall x1 x2 y : @Language.expr L,
      (|-- (x1 ⟶ x2)) -> |-- (prodp x1 y ⟶ prodp x2 y) := by
  intro x1 x2 y hx
  have hadj :
      (|-- (prodp x1 y ⟶ prodp x2 y)) <-> (|-- (x1 ⟶ funcp y (prodp x2 y))) :=
    adjoint x1 y (prodp x2 y)
  apply hadj.mpr
  have hadj_refl :
      (|-- (prodp x2 y ⟶ prodp x2 y)) <-> (|-- (x2 ⟶ funcp y (prodp x2 y))) :=
    adjoint x2 y (prodp x2 y)
  exact aux_minimun_rule02 x1 x2 (funcp y (prodp x2 y)) hx
    (hadj_refl.mp (provable_impp_refl (prodp x2 y)))

theorem funcp_mono2 :
    forall x y1 y2 : @Language.expr L,
      (|-- (y1 ⟶ y2)) -> |-- (funcp x y1 ⟶ funcp x y2) := by
  intro x y1 y2 hy
  have hadj :
      (|-- (prodp (funcp x y1) x ⟶ y2)) <-> (|-- (funcp x y1 ⟶ funcp x y2)) :=
    adjoint (funcp x y1) x y2
  apply hadj.mp
  have hadj_refl :
      (|-- (prodp (funcp x y1) x ⟶ y1)) <-> (|-- (funcp x y1 ⟶ funcp x y1)) :=
    adjoint (funcp x y1) x y1
  exact aux_minimun_rule02 (prodp (funcp x y1) x) y1 y2
    (hadj_refl.mpr (provable_impp_refl (funcp x y1))) hy

theorem adjoint_modus_ponens :
    forall x y : @Language.expr L, |-- (prodp (funcp x y) x ⟶ y) := by
  intro x y
  have hadj :
      (|-- (prodp (funcp x y) x ⟶ y)) <-> (|-- (funcp x y ⟶ funcp x y)) :=
    adjoint (funcp x y) x y
  exact hadj.mpr (provable_impp_refl (funcp x y))

omit minAX in
theorem adjoint_iter :
    forall (x : @Language.expr L) (xs : List (@Language.expr L))
      (y : @Language.expr L),
      (|-- (List.foldl prodp x xs ⟶ y)) <->
        (|-- (x ⟶ List.foldr funcp y xs)) := by
  intro x xs y
  induction xs generalizing x with
  | nil =>
      simp
  | cons a xs ih =>
      have hadj :
          (|-- (prodp x a ⟶ List.foldr funcp y xs)) <->
            (|-- (x ⟶ funcp a (List.foldr funcp y xs))) :=
        adjoint x a (List.foldr funcp y xs)
      simpa [List.foldl, List.foldr] using
        Iff.trans (ih (prodp x a)) hadj

section AdjointCommutativeTheorems

variable [Comm : Commutativity L Gamma prodp]
include Comm

theorem Adjoint2Mono : Monotonicity L Gamma prodp := by
  constructor
  intro x1 y1 x2 y2 hx hy
  exact aux_minimun_rule02 (prodp x1 y1) (prodp x2 y1) (prodp x2 y2)
    (prodp_mono1 (prodp := prodp) (funcp := funcp) x1 x2 y1 hx)
    (aux_minimun_rule02 (prodp x2 y1) (prodp y1 x2) (prodp x2 y2)
      (prodp_comm_impp x2 y1)
      (aux_minimun_rule02 (prodp y1 x2) (prodp y2 x2) (prodp x2 y2)
        (prodp_mono1 (prodp := prodp) (funcp := funcp) y1 y2 x2 hy)
        (prodp_comm_impp y2 x2)))

end AdjointCommutativeTheorems

section AdjointMonoTheorems

variable [Mono : Monotonicity L Gamma prodp]
include Mono

theorem funcp_mono :
    forall x1 y1 x2 y2 : @Language.expr L,
      (|-- (x2 ⟶ x1)) -> (|-- (y1 ⟶ y2)) ->
        |-- (funcp x1 y1 ⟶ funcp x2 y2) := by
  intro x1 y1 x2 y2 hx hy
  have hadj :
      (|-- (prodp (funcp x1 y1) x2 ⟶ y2)) <-> (|-- (funcp x1 y1 ⟶ funcp x2 y2)) :=
    adjoint (funcp x1 y1) x2 y2
  apply hadj.mp
  exact aux_minimun_rule02 (prodp (funcp x1 y1) x2)
    (prodp (funcp x1 y1) x1) y2
    (prodp_mono (funcp x1 y1) x2 (funcp x1 y1) x1
      (provable_impp_refl (funcp x1 y1)) hx)
    (aux_minimun_rule02 (prodp (funcp x1 y1) x1) y1 y2
      (adjoint_modus_ponens x1 y1) hy)

end AdjointMonoTheorems

end AdjointTheorems

section MonoTheorems

variable {L : Language.{u}}
variable [MinimumLanguage L]
variable [Gamma : Provable L]
variable [minAX : MinimumAxiomatization L Gamma]
variable {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
variable [Mono : Monotonicity L Gamma prodp]
include minAX Mono

omit minAX in
theorem fold_left_mono :
    forall (x1 x2 : @Language.expr L) (xs1 xs2 : List (@Language.expr L)),
      List.Forall₂ (fun x1 x2 => |-- (x1 ⟶ x2)) xs1 xs2 ->
      (|-- (x1 ⟶ x2)) ->
      |-- (List.foldl prodp x1 xs1 ⟶ List.foldl prodp x2 xs2) := by
  intro x1 x2 xs1 xs2 hxs
  revert x1 x2
  induction hxs with
  | nil =>
      intro x1 x2 hx
      simpa using hx
  | cons hxy htail ih =>
      intro x1 x2 hx
      simp [List.foldl]
      exact ih (prodp x1 _) (prodp x2 _) (prodp_mono x1 _ x2 _ hx hxy)

omit minAX in
theorem fold_right_mono :
    forall (x1 x2 : @Language.expr L) (xs1 xs2 : List (@Language.expr L)),
      List.Forall₂ (fun x1 x2 => |-- (x1 ⟶ x2)) xs1 xs2 ->
      (|-- (x1 ⟶ x2)) ->
      |-- (List.foldr prodp x1 xs1 ⟶ List.foldr prodp x2 xs2) := by
  intro x1 x2 xs1 xs2 hxs hx
  induction hxs with
  | nil =>
      simpa using hx
  | cons hxy htail ih =>
      simp [List.foldr]
      exact prodp_mono _ _ _ _ hxy ih

theorem fold_left_mono2 :
    forall (x1 x2 : @Language.expr L) (xs : List (@Language.expr L)),
      (|-- (x1 ⟶ x2)) ->
      |-- (List.foldl prodp x1 xs ⟶ List.foldl prodp x2 xs) := by
  intro x1 x2 xs hx
  induction xs generalizing x1 x2 with
  | nil =>
      simpa using hx
  | cons a xs ih =>
      simp [List.foldl]
      exact ih (prodp x1 a) (prodp x2 a)
        (prodp_mono x1 a x2 a hx (provable_impp_refl a))

theorem fold_right_mono2 :
    forall (x1 x2 : @Language.expr L) (xs : List (@Language.expr L)),
      (|-- (x1 ⟶ x2)) ->
      |-- (List.foldr prodp x1 xs ⟶ List.foldr prodp x2 xs) := by
  intro x1 x2 xs hx
  induction xs with
  | nil =>
      simpa using hx
  | cons a xs ih =>
      simp [List.foldr]
      exact prodp_mono a (List.foldr prodp x1 xs) a (List.foldr prodp x2 xs)
        (provable_impp_refl a) ih

end MonoTheorems

section AssocTheorems

variable {L : Language.{u}}
variable [MinimumLanguage L]
variable [Gamma : Provable L]
variable [minAX : MinimumAxiomatization L Gamma]
variable {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
variable {e : @Language.expr L}
variable [Mono : Monotonicity L Gamma prodp]
variable [Assoc : Associativity L Gamma prodp]
variable [LU : LeftUnit L Gamma e prodp]
variable [RU : RightUnit L Gamma e prodp]
include minAX Mono Assoc LU RU

theorem assoc_fold_left_cons :
    forall (x : @Language.expr L) (xs : List (@Language.expr L)),
      |-- (List.foldl prodp (prodp e x) xs ⟶ prodp x (List.foldr prodp e xs)) := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      exact aux_minimun_rule02 (prodp e x) x (prodp x e)
        (left_unit1 x) (right_unit2 x)
  | cons a xs ih =>
      simp [List.foldl, List.foldr]
      exact aux_minimun_rule02
        (List.foldl prodp (prodp (prodp e x) a) xs)
        (List.foldl prodp (prodp e (prodp x a)) xs)
        (prodp x (prodp a (List.foldr prodp e xs)))
        (fold_left_mono2 (prodp (prodp e x) a) (prodp e (prodp x a)) xs
          (prodp_assoc2 e x a))
        (aux_minimun_rule02
          (List.foldl prodp (prodp e (prodp x a)) xs)
          (prodp (prodp x a) (List.foldr prodp e xs))
          (prodp x (prodp a (List.foldr prodp e xs)))
          (ih (prodp x a))
          (prodp_assoc2 x a (List.foldr prodp e xs)))

theorem assoc_fold_right_cons :
    forall (x : @Language.expr L) (xs : List (@Language.expr L)),
      |-- (prodp x (List.foldr prodp e xs) ⟶ List.foldl prodp (prodp e x) xs) := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      exact aux_minimun_rule02 (prodp x e) x (prodp e x)
        (right_unit1 x) (left_unit2 x)
  | cons a xs ih =>
      simp [List.foldl, List.foldr]
      exact aux_minimun_rule02
        (prodp x (prodp a (List.foldr prodp e xs)))
        (prodp (prodp x a) (List.foldr prodp e xs))
        (List.foldl prodp (prodp (prodp e x) a) xs)
        (prodp_assoc1 x a (List.foldr prodp e xs))
        (aux_minimun_rule02
          (prodp (prodp x a) (List.foldr prodp e xs))
          (List.foldl prodp (prodp e (prodp x a)) xs)
          (List.foldl prodp (prodp (prodp e x) a) xs)
          (ih (prodp x a))
          (fold_left_mono2 (prodp e (prodp x a)) (prodp (prodp e x) a) xs
            (prodp_assoc1 e x a)))

theorem assoc_fold_left_fold_right :
    forall xs : List (@Language.expr L),
      |-- (List.foldl prodp e xs ⟶ List.foldr prodp e xs) := by
  intro xs
  induction xs with
  | nil =>
      exact provable_impp_refl e
  | cons a xs ih =>
      simpa [List.foldl, List.foldr] using
        assoc_fold_left_cons (e := e) (prodp := prodp) a xs

theorem assoc_fold_right_fold_left :
    forall xs : List (@Language.expr L),
      |-- (List.foldr prodp e xs ⟶ List.foldl prodp e xs) := by
  intro xs
  induction xs with
  | nil =>
      exact provable_impp_refl e
  | cons a xs ih =>
      simpa [List.foldl, List.foldr] using
        assoc_fold_right_cons (e := e) (prodp := prodp) a xs

theorem assoc_prodp_fold_left :
    forall xs1 xs2 : List (@Language.expr L),
      |-- (prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2) ⟶
        List.foldl prodp e (xs1 ++ xs2)) := by
  intro xs1 xs2
  have hfoldr :
      |-- (prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2) ⟶
        List.foldr prodp e (xs1 ++ xs2)) := by
    induction xs1 with
    | nil =>
        simpa using left_unit1 (List.foldr prodp e xs2)
    | cons a xs1 ih =>
        simpa [List.foldr] using aux_minimun_rule02
          (prodp (prodp a (List.foldr prodp e xs1)) (List.foldr prodp e xs2))
          (prodp a (prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2)))
          (prodp a (List.foldr prodp e (xs1 ++ xs2)))
          (prodp_assoc2 a (List.foldr prodp e xs1) (List.foldr prodp e xs2))
          (prodp_mono _ _ _ _ (provable_impp_refl a) ih)
  have hmono :
      |-- (prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2) ⟶
        prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2)) := by
    exact prodp_mono _ _ _ _
      (assoc_fold_left_fold_right (e := e) (prodp := prodp) xs1)
      (assoc_fold_left_fold_right (e := e) (prodp := prodp) xs2)
  exact aux_minimun_rule02
    (prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2))
    (prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2))
    (List.foldl prodp e (xs1 ++ xs2))
    hmono
    (aux_minimun_rule02
      (prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2))
      (List.foldr prodp e (xs1 ++ xs2))
      (List.foldl prodp e (xs1 ++ xs2))
      hfoldr
      (assoc_fold_right_fold_left (e := e) (prodp := prodp) (xs1 ++ xs2)))

theorem assoc_fold_left_app :
    forall xs1 xs2 : List (@Language.expr L),
      |-- (List.foldl prodp e (xs1 ++ xs2) ⟶
        prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2)) := by
  intro xs1 xs2
  have hfoldr :
      |-- (List.foldr prodp e (xs1 ++ xs2) ⟶
        prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2)) := by
    induction xs1 with
    | nil =>
        simpa using left_unit2 (List.foldr prodp e xs2)
    | cons a xs1 ih =>
        simpa [List.foldr] using aux_minimun_rule02
          (prodp a (List.foldr prodp e (xs1 ++ xs2)))
          (prodp a (prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2)))
          (prodp (prodp a (List.foldr prodp e xs1)) (List.foldr prodp e xs2))
          (prodp_mono _ _ _ _ (provable_impp_refl a) ih)
          (prodp_assoc1 a (List.foldr prodp e xs1) (List.foldr prodp e xs2))
  have hmono :
      |-- (prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2) ⟶
        prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2)) := by
    exact prodp_mono _ _ _ _
      (assoc_fold_right_fold_left (e := e) (prodp := prodp) xs1)
      (assoc_fold_right_fold_left (e := e) (prodp := prodp) xs2)
  exact aux_minimun_rule02
    (List.foldl prodp e (xs1 ++ xs2))
    (List.foldr prodp e (xs1 ++ xs2))
    (prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2))
    (assoc_fold_left_fold_right (e := e) (prodp := prodp) (xs1 ++ xs2))
    (aux_minimun_rule02
      (List.foldr prodp e (xs1 ++ xs2))
      (prodp (List.foldr prodp e xs1) (List.foldr prodp e xs2))
      (prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2))
      hfoldr hmono)

end AssocTheorems

section DistrCommTheorems

variable {L : Language.{u}}
variable [MinimumLanguage L]
variable [Gamma : Provable L]
variable [minAX : MinimumAxiomatization L Gamma]
variable {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
variable [Comm : Commutativity L Gamma prodp]
variable [Mono : Monotonicity L Gamma sump]
include minAX Comm Mono

theorem LeftDistr2RightDistr [LDistr : LeftDistr L Gamma prodp sump] :
    RightDistr L Gamma prodp sump := by
  constructor
  · intro x y z
    exact aux_minimun_rule02 (prodp (sump y z) x) (prodp x (sump y z))
      (sump (prodp y x) (prodp z x))
      (prodp_comm_impp (sump y z) x)
      (aux_minimun_rule02 (prodp x (sump y z))
        (sump (prodp x y) (prodp x z))
        (sump (prodp y x) (prodp z x))
        (left_distr1 x y z)
        (prodp_mono (prodp x y) (prodp x z) (prodp y x) (prodp z x)
          (prodp_comm_impp x y) (prodp_comm_impp x z)))
  · intro x y z
    exact aux_minimun_rule02 (sump (prodp y x) (prodp z x))
      (sump (prodp x y) (prodp x z)) (prodp (sump y z) x)
      (prodp_mono (prodp y x) (prodp z x) (prodp x y) (prodp x z)
        (prodp_comm_impp y x) (prodp_comm_impp z x))
      (aux_minimun_rule02 (sump (prodp x y) (prodp x z))
        (prodp x (sump y z)) (prodp (sump y z) x)
        (left_distr2 x y z)
        (prodp_comm_impp x (sump y z)))

theorem RightDistr2LeftDistr [RDistr : RightDistr L Gamma prodp sump] :
    LeftDistr L Gamma prodp sump := by
  constructor
  · intro x y z
    exact aux_minimun_rule02 (prodp x (sump y z)) (prodp (sump y z) x)
      (sump (prodp x y) (prodp x z))
      (prodp_comm_impp x (sump y z))
      (aux_minimun_rule02 (prodp (sump y z) x)
        (sump (prodp y x) (prodp z x))
        (sump (prodp x y) (prodp x z))
        (right_distr1 x y z)
        (prodp_mono (prodp y x) (prodp z x) (prodp x y) (prodp x z)
          (prodp_comm_impp y x) (prodp_comm_impp z x)))
  · intro x y z
    exact aux_minimun_rule02 (sump (prodp x y) (prodp x z))
      (sump (prodp y x) (prodp z x)) (prodp x (sump y z))
      (prodp_mono (prodp x y) (prodp x z) (prodp y x) (prodp z x)
        (prodp_comm_impp x y) (prodp_comm_impp x z))
      (aux_minimun_rule02 (sump (prodp y x) (prodp z x))
        (prodp (sump y z) x) (prodp x (sump y z))
        (right_distr2 x y z)
        (prodp_comm_impp (sump y z) x))

end DistrCommTheorems

section CommForSimpleAssocConstruction

variable {L : Language.{u}}
variable [MinimumLanguage L]
variable [Gamma : Provable L]
variable [minAX : MinimumAxiomatization L Gamma]
variable {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
variable [Comm : Commutativity L Gamma prodp]
variable [Mono : Monotonicity L Gamma prodp]
include minAX Comm Mono

theorem Build_Associativity1 :
    (forall x y z : @Language.expr L,
      |-- (prodp x (prodp y z) ⟶ prodp (prodp x y) z)) ->
    Associativity L Gamma prodp := by
  intro h
  constructor
  · exact h
  · intro x y z
    exact aux_minimun_rule02 (prodp (prodp x y) z) (prodp z (prodp x y))
      (prodp x (prodp y z))
      (prodp_comm_impp (prodp x y) z)
      (aux_minimun_rule02 (prodp z (prodp x y)) (prodp z (prodp y x))
        (prodp x (prodp y z))
        (prodp_mono z (prodp x y) z (prodp y x)
          (provable_impp_refl z) (prodp_comm_impp x y))
        (aux_minimun_rule02 (prodp z (prodp y x)) (prodp (prodp z y) x)
          (prodp x (prodp y z))
          (h z y x)
          (aux_minimun_rule02 (prodp (prodp z y) x) (prodp (prodp y z) x)
            (prodp x (prodp y z))
            (prodp_mono (prodp z y) x (prodp y z) x
              (prodp_comm_impp z y) (provable_impp_refl x))
            (prodp_comm_impp (prodp y z) x))))

theorem Build_Associativity2 :
    (forall x y z : @Language.expr L,
      |-- (prodp (prodp x y) z ⟶ prodp x (prodp y z))) ->
    Associativity L Gamma prodp := by
  intro h
  constructor
  · intro x y z
    exact aux_minimun_rule02 (prodp x (prodp y z)) (prodp (prodp y z) x)
      (prodp (prodp x y) z)
      (prodp_comm_impp x (prodp y z))
      (aux_minimun_rule02 (prodp (prodp y z) x) (prodp (prodp z y) x)
        (prodp (prodp x y) z)
        (prodp_mono (prodp y z) x (prodp z y) x
          (prodp_comm_impp y z) (provable_impp_refl x))
        (aux_minimun_rule02 (prodp (prodp z y) x) (prodp z (prodp y x))
          (prodp (prodp x y) z)
          (h z y x)
          (aux_minimun_rule02 (prodp z (prodp y x)) (prodp z (prodp x y))
            (prodp (prodp x y) z)
            (prodp_mono z (prodp y x) z (prodp x y)
              (provable_impp_refl z) (prodp_comm_impp y x))
            (prodp_comm_impp z (prodp x y)))))
  · exact h

end CommForSimpleAssocConstruction

end Unifysl.ProofTheoryPatternsP
