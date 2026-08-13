import FP.AllFramework

namespace FP

open AUXLib

def lower_than_fx {A : Type} [Sets.SETS A] (F : A -> A) : A -> Prop :=
  fun x => Sets.included x (F x)

def sseq_mono {A : Type} [Sets.SETS A] (T : Nat -> A) : Prop :=
  forall n, Sets.included (T n) (T (n + 1))

def sfixpoint {A : Type} [Sets.SETS A] (f : A -> A) (x0 : A) : Prop :=
  Sets.equiv x0 (f x0)

theorem sseq_mono_nat_le {A : Type} [Sets.SETS A] [SETS_Properties A]
    (T : Nat -> A) (hmono : sseq_mono T) {n m : Nat} (hnm : n <= m) :
    Sets.included (T n) (T m) := by
  induction hnm with
  | refl => exact Sets_included_refl.refl _
  | @step m _ ih => exact Sets_included_trans.trans _ _ _ ih (hmono m)

def sseq_continuous {A B : Type} [Sets.SETS A] [Sets.SETS B]
    (f : A -> B) : Prop :=
  forall T : Nat -> A, sseq_mono T ->
    Sets.equiv (f (Sets.indexed_union T))
      (Sets.indexed_union (fun n => f (T n)))

def Lfix {A : Type} [Sets.SETS A] (f : A -> A) : A :=
  Sets.indexed_union (fun n => nat_iter n f Sets.empty)

theorem Lfix_fixpoint {A : Type} [Sets.SETS A] [SETS_Properties A]
    (f : A -> A) (hf : Proper (Sets.included ==> Sets.included) f)
    (hcont : sseq_continuous f) : Sets.equiv (Lfix f) (f (Lfix f)) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : OmegaLub A := CPO_sets.oLub_sets
  letI : Bot A := CPO_sets.Bot_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompletePartialOrder_Setoid A := CPO_sets.CPO_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact BourbakiWitt_fixpoint f hf hcont

theorem Lfix_least_fixpoint {A : Type} [Sets.SETS A] [SETS_Properties A]
    (f : A -> A) (x0 : A) (hf : Proper (Sets.included ==> Sets.included) f)
    (hcont : sseq_continuous f) (hfix : sfixpoint f x0) :
    Sets.included (Lfix f) x0 := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : OmegaLub A := CPO_sets.oLub_sets
  letI : Bot A := CPO_sets.Bot_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompletePartialOrder_Setoid A := CPO_sets.CPO_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact BourbakiWitt_least_fixpoint f x0 hf hcont hfix

theorem Lfix_fixpoint_relax {A : Type} [Sets.SETS A] [SETS_Properties A]
    (f g : A -> A)
    (hf : Proper (Sets.included ==> Sets.included) f)
    (hg : Proper (Sets.included ==> Sets.included) g)
    (hfc : sseq_continuous f) (hgc : sseq_continuous g)
    (hstep : forall a b, Sets.included a b -> Sets.included a (f a) ->
      Sets.included (f a) (g b))
    (hclosed : forall b,
      (forall a, Sets.included a b -> Sets.included (f a) b) ->
      forall a, Sets.included a b -> Sets.included (g a) b) :
    Sets.equiv (Lfix f) (Lfix g) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : OmegaLub A := CPO_sets.oLub_sets
  letI : Bot A := CPO_sets.Bot_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompletePartialOrder_Setoid A := CPO_sets.CPO_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact BourbakiWitt_fixpoint_relax f g hf hg hfc hgc hstep hclosed

def Gfix {A : Type} [Sets.SETS A] (f : A -> A) : A :=
  Sets.general_union (lower_than_fx f)

theorem Gfix_fixpoint_theorem_g {A : Type} [Sets.SETS A] [SETS_Properties A]
    (f : A -> A) (hf : Proper (Sets.included ==> Sets.included) f) :
    Sets.equiv (Gfix f) (f (Gfix f)) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : Lub A := CL_sets.Lub_sets
  letI : Glb A := CL_sets.Glb_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompleteLattice_Setoid A := CL_sets.CL_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact KnasterTarski_fixpoint_theorem_g f hf

theorem Gfix_greatest_fixpoint {A : Type} [Sets.SETS A] [SETS_Properties A]
    (f : A -> A) (x : A) (hf : Proper (Sets.included ==> Sets.included) f)
    (hfix : Sets.equiv x (f x)) : Sets.included x (Gfix f) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : Lub A := CL_sets.Lub_sets
  letI : Glb A := CL_sets.Glb_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompleteLattice_Setoid A := CL_sets.CL_sets
  exact KnasterTarski_fixpoint_greatest_fixpoint f x hf hfix

def rconcat {A B C T V : Type}
    (X : A -> List T -> B -> Prop)
    (Y : V -> B -> List T -> C -> Prop) :
    V -> A -> List T -> C -> Prop :=
  fun v => Rels.concat X (Y v)

end FP

namespace SetsNotation

scoped infixr:12 " • " => FP.rconcat

end SetsNotation

namespace FP

open AUXLib

instance rconcat_mono {A T V : Type} :
    Proper (Sets.included ==> Sets.included ==> Sets.included)
      (@rconcat A A A T V) where
  proper X X' hX Y Y' hY v a trace c := by
    rintro ⟨b, t2, t1, htrace, hxb, hyb⟩
    exact ⟨b, t2, t1, htrace, hX a t1 b hxb, hY v b t2 c hyb⟩

theorem Lfix_mono {A : Type} [Sets.SETS A] [SETS_Properties A]
    (F G : A -> A) (Fmono : Proper (Sets.included ==> Sets.included) F)
    (hFG : forall a, Sets.included (F a) (G a)) :
    Sets.included (Lfix F) (Lfix G) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : OmegaLub A := CPO_sets.oLub_sets
  letI : Bot A := CPO_sets.Bot_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompletePartialOrder_Setoid A := CPO_sets.CPO_sets
  letI : CompletePartialOrder_Strong_Setoid A := CPO_sets.CPOs_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact BourbakiWitt_fixpoint_mono' F G Fmono hFG

theorem Lfix_congr {A : Type} [Sets.SETS A] [SETS_Properties A]
    (F G : A -> A) (Fcongr : Proper (Sets.equiv ==> Sets.equiv) F)
    (hFG : forall a, Sets.equiv (F a) (G a)) :
    Sets.equiv (Lfix F) (Lfix G) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : OmegaLub A := CPO_sets.oLub_sets
  letI : Bot A := CPO_sets.Bot_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompletePartialOrder_Setoid A := CPO_sets.CPO_sets
  letI : CompletePartialOrder_Strong_Setoid A := CPO_sets.CPOs_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact BourbakiWitt_fixpoint_congr' F G Fcongr hFG

theorem Lfix_mono_weak {A : Type} [Sets.SETS A] [SETS_Properties A]
    (F G : A -> A) (Fmono : Proper (Sets.included ==> Sets.included) F)
    (hFG : forall a b, Sets.included a b -> Sets.included (F a) (G b)) :
    Sets.included (Lfix F) (Lfix G) :=
  Lfix_mono F G Fmono (fun a => hFG a a (Sets_included_refl.refl a))

theorem Lfix_congr_weak {A : Type} [Sets.SETS A] [SETS_Properties A]
    (F G : A -> A)
    (hFG : forall a b, Sets.equiv a b -> Sets.equiv (F a) (G b)) :
    Sets.equiv (Lfix F) (Lfix G) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : OmegaLub A := CPO_sets.oLub_sets
  letI : Bot A := CPO_sets.Bot_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompletePartialOrder_Setoid A := CPO_sets.CPO_sets
  letI : CompletePartialOrder_Strong_Setoid A := CPO_sets.CPOs_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact BourbakiWitt_fixpoint_congr F G hFG

theorem Gfix_mono {A : Type} [Sets.SETS A] [SETS_Properties A]
    (F G : A -> A) (hFG : forall x, Sets.included (F x) (G x)) :
    Sets.included (Gfix F) (Gfix G) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : Lub A := CL_sets.Lub_sets
  letI : Glb A := CL_sets.Glb_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompleteLattice_Setoid A := CL_sets.CL_sets
  exact KT_fix_g_mono F G hFG

theorem Gfix_congr {A : Type} [Sets.SETS A] [SETS_Properties A]
    (F G : A -> A) (hFG : forall x, Sets.equiv (F x) (G x)) :
    Sets.equiv (Gfix F) (Gfix G) := by
  letI : Order A := PO_sets.R_sets
  letI : Equiv A := PO_sets.Equiv_sets
  letI : Lub A := CL_sets.Lub_sets
  letI : Glb A := CL_sets.Glb_sets
  letI : PartialOrder_Setoid A := PO_sets.PO_sets
  letI : CompleteLattice_Setoid A := CL_sets.CL_sets
  letI : AUXLib.Equivalence (@equiv A _) := PO_sets.Equiv_equiv_sets
  exact KT_fix_g_congr F G hFG

end FP

export FP (lower_than_fx sseq_mono sfixpoint sseq_mono_nat_le sseq_continuous
  Lfix Lfix_fixpoint Lfix_least_fixpoint Lfix_fixpoint_relax Gfix
  Gfix_fixpoint_theorem_g Gfix_greatest_fixpoint rconcat rconcat_mono
  Lfix_mono Lfix_congr Lfix_mono_weak Lfix_congr_weak Gfix_mono Gfix_congr)
