import AUXLib.Morphisms
import FP.PartialOrder_Setoid
import SetsClass.SetsDomain

universe u v

namespace FP

open AUXLib

def upper_bound {A : Type} [Order A] (T : A -> Prop) (bnd : A) : Prop :=
  forall a, T a -> order_rel a bnd

def least_upper_bound {A : Type} [Order A] (T : A -> Prop) (bnd : A) : Prop :=
  upper_bound T bnd /\ forall bnd', upper_bound T bnd' -> order_rel bnd bnd'

def lower_bound {A : Type} [Order A] (T : A -> Prop) (bnd : A) : Prop :=
  forall a, T a -> order_rel bnd a

def greatest_lower_bound {A : Type} [Order A] (T : A -> Prop) (bnd : A) : Prop :=
  lower_bound T bnd /\ forall bnd', lower_bound T bnd' -> order_rel bnd' bnd

class Lub (A : Type) where
  lub : (A -> Prop) -> A

class Glb (A : Type) where
  glb : (A -> Prop) -> A

abbrev lub {A : Type} [l : Lub A] : (A -> Prop) -> A := l.lub
abbrev glb {A : Type} [g : Glb A] : (A -> Prop) -> A := g.glb

class CompleteLattice_Setoid (A : Type) [Order A] [Equiv A]
    [Lub A] [Glb A] : Prop where
  CL_PartialOrder : PartialOrder_Setoid A
  CL_Complete_lub : forall T : A -> Prop,
    @least_upper_bound A _ T (@lub A _ T)
  lub_congr : forall T1 T2 : A -> Prop,
    (forall a, T1 a <-> T2 a) ->
      @equiv A _ (@lub A _ T1) (@lub A _ T2)

instance completeLatticePartialOrder (A : Type) [Order A] [Equiv A]
    [Lub A] [Glb A] [c : CompleteLattice_Setoid A] : PartialOrder_Setoid A :=
  c.CL_PartialOrder

def lower_than_fp {A : Type} [Order A] (F : A -> A) : A -> Prop :=
  fun x => order_rel x (F x)

def greater_than_fp {A : Type} [Order A] (F : A -> A) : A -> Prop :=
  fun x => order_rel (F x) x

def glb_of_lub {A : Type} [Order A] [Lub A] (X : A -> Prop) : A :=
  lub (lower_bound X)

def KT_fix_g {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [CompleteLattice_Setoid A] (f : A -> A) : A := lub (lower_than_fp f)

def KT_fix_l {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [CompleteLattice_Setoid A] (f : A -> A) : A := glb_of_lub (greater_than_fp f)

theorem lower_bound_mono {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [CompleteLattice_Setoid A] :
    Proper (AUXLib.flipRel Sets.included ==> Sets.included) (@lower_bound A _) where
  proper X Y hXY b hb x hx := hb x (hXY x hx)

theorem upper_bound_mono {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [CompleteLattice_Setoid A] :
    Proper (AUXLib.flipRel Sets.included ==> Sets.included) (@upper_bound A _) where
  proper X Y hXY b hb x hx := hb x (hXY x hx)

theorem lub_less_than {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [c : CompleteLattice_Setoid A] (X : A -> Prop) (y : A)
    (h : forall x, X x -> order_rel x y) : order_rel (lub X) y :=
  (c.CL_Complete_lub X).2 y h

theorem less_than_lub {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [c : CompleteLattice_Setoid A] (x y : A) (Y : A -> Prop)
    (hy : Y y) (hxy : order_rel x y) : order_rel x (lub Y) :=
  c.CL_PartialOrder.PO_Transitive.trans _ y _ hxy ((c.CL_Complete_lub Y).1 y hy)

theorem element_less_than_lub {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [c : CompleteLattice_Setoid A] (x : A) (X : A -> Prop) (hx : X x) :
    order_rel x (lub X) := (c.CL_Complete_lub X).1 x hx

theorem CL_Complete_glb {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [c : CompleteLattice_Setoid A] (T : A -> Prop) :
    greatest_lower_bound T (glb_of_lub T) := by
  constructor
  · intro x hx
    exact lub_less_than _ _ (fun b hb => hb x hx)
  · intro bnd hbnd
    exact element_less_than_lub bnd (lower_bound T) hbnd

theorem lub_mono {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [CompleteLattice_Setoid A] :
    Proper (Sets.included ==> @order_rel A _) (@lub A _) where
  proper X Y h := lub_less_than X (lub Y) (fun x hx =>
    element_less_than_lub x Y (h x hx))

theorem glb_congr {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [c : CompleteLattice_Setoid A] (T1 T2 : A -> Prop)
    (h : forall a, T1 a <-> T2 a) :
    equiv (glb_of_lub T1) (glb_of_lub T2) :=
  c.lub_congr _ _ (fun b => by
    constructor <;> intro hb x hx
    · exact hb x ((h x).mpr hx)
    · exact hb x ((h x).mp hx))

theorem less_than_glb {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [c : CompleteLattice_Setoid A] (X : A -> Prop) (y : A)
    (h : forall x, X x -> order_rel y x) : order_rel y (glb_of_lub X) :=
  (CL_Complete_glb X).2 y h

theorem glb_less_than {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [c : CompleteLattice_Setoid A] (x y : A) (Y : A -> Prop)
    (hy : Y y) (hxy : order_rel y x) : order_rel (glb_of_lub Y) x :=
  c.CL_PartialOrder.PO_Transitive.trans _ y _ ((CL_Complete_glb Y).1 y hy) hxy

theorem glb_mono {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [CompleteLattice_Setoid A] :
    Proper (AUXLib.flipRel Sets.included ==> @order_rel A _) (@glb_of_lub A _ _) where
  proper X Y h := less_than_glb Y (glb_of_lub X) (fun y hy =>
    (CL_Complete_glb X).1 y (h y hy))

theorem glb_less_than_element {A : Type} [Order A] [Equiv A] [Lub A] [Glb A]
    [CompleteLattice_Setoid A] (x : A) (X : A -> Prop) (hx : X x) :
    order_rel (glb_of_lub X) x := (CL_Complete_glb X).1 x hx

theorem KnasterTarski_fixpoint_theorem_g {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompleteLattice_Setoid A] (f : A -> A)
    (hf : Proper (order_rel ==> order_rel) f) :
    equiv (KT_fix_g f) (f (KT_fix_g f)) := by
  apply c.CL_PartialOrder.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
  · apply lub_less_than
    intro x hx
    exact c.CL_PartialOrder.PO_Transitive.trans _ (f x) _ hx
      (hf.proper _ _ (element_less_than_lub x (lower_than_fp f) hx))
  · apply element_less_than_lub
    exact hf.proper _ _ (by
      apply lub_less_than
      intro x hx
      exact c.CL_PartialOrder.PO_Transitive.trans _ (f x) _ hx
        (hf.proper _ _ (element_less_than_lub x (lower_than_fp f) hx)))

theorem KnasterTarski_fixpoint_greatest_fixpoint {A : Type}
    [Order A] [Equiv A] [Lub A] [Glb A] [CompleteLattice_Setoid A]
    (f : A -> A) (x : A) (_ : Proper (order_rel ==> order_rel) f)
    (hx : equiv x (f x)) : order_rel x (KT_fix_g f) :=
  element_less_than_lub x _
    ((inferInstance : PartialOrder_Setoid A).PO_Reflexive_Setoid _ _ hx)

theorem KnasterTarski_fixpoint_theorem_l {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompleteLattice_Setoid A] (f : A -> A)
    (hf : Proper (order_rel ==> order_rel) f) :
    equiv (KT_fix_l f) (f (KT_fix_l f)) := by
  apply c.CL_PartialOrder.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
  · apply glb_less_than_element
    exact hf.proper _ _ (by
      apply less_than_glb
      intro x hx
      exact c.CL_PartialOrder.PO_Transitive.trans _ (f x) _
        (hf.proper _ _ (glb_less_than_element x (greater_than_fp f) hx)) hx)
  · apply less_than_glb
    intro x hx
    exact c.CL_PartialOrder.PO_Transitive.trans _ (f x) _
      (hf.proper _ _ (glb_less_than_element x (greater_than_fp f) hx)) hx

theorem KnasterTarski_fixpoint_least_fixpoint {A : Type}
    [Order A] [Equiv A] [Lub A] [Glb A]
    [e : AUXLib.Equivalence (@equiv A _)] [CompleteLattice_Setoid A]
    (f : A -> A) (x : A) (_ : Proper (order_rel ==> order_rel) f)
    (hx : equiv x (f x)) : order_rel (KT_fix_l f) x :=
  glb_less_than_element x _
    ((inferInstance : PartialOrder_Setoid A).PO_Reflexive_Setoid _ _
      (e.symm _ _ hx))

theorem KnasterTarski_fixpoint_least_prefixpoint {A : Type}
    [Order A] [Equiv A] [Lub A] [Glb A]
    [AUXLib.Equivalence (@equiv A _)] [CompleteLattice_Setoid A]
    (f : A -> A) (x : A) (_ : Proper (order_rel ==> order_rel) f)
    (hx : order_rel (f x) x) : order_rel (KT_fix_l f) x :=
  glb_less_than_element x _ hx

theorem KT_fix_l_mono_strong {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [e : AUXLib.Equivalence (@equiv A _)]
    [CompleteLattice_Setoid A] :
    Proper ((@equiv A _ ==> @order_rel A _) ==> @order_rel A _)
      (@KT_fix_l A _ _ _ _ _) where
  proper f g h := by
    apply glb_mono.proper
    intro x hx
    exact (inferInstance : Transitive (@order_rel A _)).trans _ (g x) _
      (h x x (e.refl x)) hx

theorem KT_fix_l_congr_strong {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompleteLattice_Setoid A] :
    Proper ((@equiv A _ ==> @equiv A _) ==> @equiv A _)
      (@KT_fix_l A _ _ _ _ _) where
  proper f g h := by
    apply c.CL_PartialOrder.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
    · exact KT_fix_l_mono_strong.proper f g (fun x y hxy =>
        c.CL_PartialOrder.PO_Reflexive_Setoid _ _ (h x y hxy))
    · exact KT_fix_l_mono_strong.proper g f (fun x y hxy =>
        c.CL_PartialOrder.PO_Reflexive_Setoid _ _
          (e.symm _ _ (h y x (e.symm _ _ hxy))))

theorem KT_fix_l_mono {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompleteLattice_Setoid A] (f g : A -> A)
    (hf : Proper (order_rel ==> order_rel) f)
    (hg : Proper (order_rel ==> order_rel) g)
    (hfg : lift_rel2 order_rel f g) : order_rel (KT_fix_l f) (KT_fix_l g) := by
  apply KnasterTarski_fixpoint_least_prefixpoint f (KT_fix_l g) hf
  exact c.CL_PartialOrder.PO_Transitive.trans _ (g (KT_fix_l g)) _
    (hfg _) (c.CL_PartialOrder.PO_Reflexive_Setoid _ _
      (e.symm _ _ (KnasterTarski_fixpoint_theorem_l g hg)))

theorem KT_fix_l_congr {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompleteLattice_Setoid A] (f g : A -> A)
    (hf : Proper (order_rel ==> order_rel) f)
    (hg : Proper (order_rel ==> order_rel) g)
    (hfg : lift_rel2 equiv f g) : equiv (KT_fix_l f) (KT_fix_l g) := by
  apply c.CL_PartialOrder.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
  · apply KT_fix_l_mono f g hf hg
    intro x
    exact c.CL_PartialOrder.PO_Reflexive_Setoid _ _ (hfg x)
  · apply KT_fix_l_mono g f hg hf
    intro x
    exact c.CL_PartialOrder.PO_Reflexive_Setoid _ _ (e.symm _ _ (hfg x))

theorem KT_fix_g_mono {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [CompleteLattice_Setoid A] (f g : A -> A)
    (hfg : forall a, order_rel (f a) (g a)) : order_rel (KT_fix_g f) (KT_fix_g g) :=
  lub_mono.proper _ _ (fun x hx =>
    (inferInstance : Transitive (@order_rel A _)).trans _ (f x) _ hx (hfg x))

theorem KT_fix_g_congr {A : Type} [Order A] [Equiv A]
    [Lub A] [Glb A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompleteLattice_Setoid A] (f g : A -> A)
    (hfg : forall a, equiv (f a) (g a)) : equiv (KT_fix_g f) (KT_fix_g g) :=
  c.lub_congr _ _ (fun x =>
    (PartialOrder_Setoid_Proper A).proper _ _ (e.refl x) _ _ (hfg x))

namespace CL_lift

instance Lub_lift (A : Type) {B : Type} [Lub B] : Lub (A -> B) where
  lub := lift_set_summary lub

instance Glb_lift (A : Type) {B : Type} [Glb B] : Glb (A -> B) where
  glb := lift_set_summary glb

instance CL_lift (A : Type) {B : Type} [Order B] [Equiv B] [Lub B] [Glb B]
    [c : CompleteLattice_Setoid B] : CompleteLattice_Setoid (A -> B) where
  CL_PartialOrder := PO_lift.PO_lift A
  CL_Complete_lub := by
    intro T
    constructor
    · intro f hf a
      exact (c.CL_Complete_lub (fun b => exists g, T g /\ g a = b)).1
        (f a) ⟨f, hf, rfl⟩
    · intro bnd hbnd a
      apply (c.CL_Complete_lub (fun b => exists g, T g /\ g a = b)).2
      intro b hb
      rcases hb with ⟨f, hf, rfl⟩
      exact hbnd f hf a
  lub_congr := by
    intro T1 T2 h a
    apply c.lub_congr
    intro b
    constructor
    · rintro ⟨f, hf, hfb⟩
      exact ⟨f, (h f).mp hf, hfb⟩
    · rintro ⟨f, hf, hfb⟩
      exact ⟨f, (h f).mpr hf, hfb⟩

end CL_lift

namespace CL_sets

instance Lub_sets {T : Type} [Sets.SETS T] : Lub T where
  lub := Sets.general_union

instance Glb_sets {T : Type} [Sets.SETS T] : Glb T where
  glb := Sets.general_intersect

macro "unfold_CL_defs" : tactic =>
  `(tactic| simp only [order_rel, equiv, lub, glb, PO_sets.R_sets,
      PO_sets.Equiv_sets, Lub_sets, Glb_sets])

instance CL_sets {T : Type} [Sets.SETS T] [SETS_Properties T] :
    CompleteLattice_Setoid T where
  CL_PartialOrder := PO_sets.PO_sets
  CL_Complete_lub := by
    intro X
    exact ⟨fun x hx => Sets_included_general_union X x hx,
      fun y h => Sets_general_union_included X y h⟩
  lub_congr := by
    intro X Y h
    exact (Sets_equiv_Sets_included _ _).mpr
      ⟨Sets_general_union_included X _ (fun x hx =>
          Sets_included_general_union Y x ((h x).mp hx)),
       Sets_general_union_included Y _ (fun x hx =>
          Sets_included_general_union X x ((h x).mpr hx))⟩

end CL_sets

end FP

export FP (upper_bound least_upper_bound lower_bound greatest_lower_bound Lub Glb
  lub glb CompleteLattice_Setoid lower_than_fp greater_than_fp glb_of_lub
  KT_fix_g KT_fix_l lower_bound_mono upper_bound_mono lub_less_than less_than_lub
  element_less_than_lub CL_Complete_glb lub_mono glb_congr less_than_glb
  glb_less_than glb_mono glb_less_than_element KnasterTarski_fixpoint_theorem_g
  KnasterTarski_fixpoint_greatest_fixpoint KnasterTarski_fixpoint_theorem_l
  KnasterTarski_fixpoint_least_fixpoint KnasterTarski_fixpoint_least_prefixpoint
  KT_fix_l_mono_strong KT_fix_l_congr_strong KT_fix_l_mono KT_fix_l_congr
  KT_fix_g_mono KT_fix_g_congr)
