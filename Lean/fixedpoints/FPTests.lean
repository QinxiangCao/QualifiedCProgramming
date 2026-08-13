import FP
import AUXLib.Relations

open AUXLib

#check FP.Order
#check FP.PartialOrder_Setoid
#check FP.CompletePartialOrder_Setoid
#check FP.CompleteLattice_Setoid
#check FP.BW_fix
#check FP.BourbakiWitt_fixpoint
#check FP.KT_fix_l
#check FP.KT_fix_g
#check FP.CL_lift.Lub_lift
#check FP.CL_lift.Glb_lift
#check FP.CL_lift.CL_lift
#check FP.Lfix
#check FP.Gfix
#check AUXLib.OmegaCompletePartialOrder_Setoid
#check AUXLib.BW_LFix
#check AUXLib.BW_LFix_is_fix
#check Rels.concat
#check clos_refl_trans
#check FP.rconcat
#check FP.rconcat_mono

open scoped SetsNotation

example {A B C T V : Type} (X : A -> List T -> B -> Prop)
    (Y : V -> B -> List T -> C -> Prop) (v : V) :
    FP.rconcat X Y v = Rels.concat X (Y v) := rfl

example {A B C T V : Type} (X : A -> List T -> B -> Prop)
    (Y : V -> B -> List T -> C -> Prop) (v : V) :
    (X • Y) v = FP.rconcat X Y v := rfl

example {A B C T V : Type} (X : A -> List T -> B -> Prop)
    (Y : V -> B -> List T -> C -> Prop) (v : V) (a : A)
    (trace : List T) (c : C) :
    FP.rconcat X Y v a trace c <->
      exists t1 t2, t1 ++ t2 = trace /\ exists b, X a t1 b /\ Y v b t2 c := by
  constructor
  · rintro ⟨b, t2, t1, htrace, hX, hY⟩
    exact ⟨t1, t2, htrace, b, hX, hY⟩
  · rintro ⟨t1, t2, htrace, b, hX, hY⟩
    exact ⟨b, t2, t1, htrace, hX, hY⟩

def successorStep (x y : Nat) : Prop := y = x + 1

example : clos_refl_trans successorStep 0 2 := by
  exact ⟨2, ⟨1, rfl, ⟨2, rfl, rfl⟩⟩⟩

example {A : Type} (R : A -> A -> Prop) {x z : A}
    (h : clos_refl_trans R x z) :
    x = z \/ exists y, R x y /\ clos_refl_trans R y z :=
  clos_refl_trans_cases A R h

example {A : Type} (R : A -> A -> Prop) {x z : A}
    (h : clos_refl_trans R x z) : True := by
  induction_1n h <;> trivial

example {A : Type} (R : A -> A -> Prop) (P : A -> Prop)
    (hstep : forall a b, R a b -> P a -> P b) {x z : A}
    (h : clos_refl_trans R x z) (hx : P x) : P z := by
  induction_1n h <;> grind

example {A : Type} (R : A -> A -> Prop) (P : A -> Prop)
    (hstep : forall a b, R a b -> P a -> P b) {x z : A}
    (h : clos_refl_trans R x z) (hx : P x) : P z := by
  induction_n1 h <;> grind

section FixedPointTactics

local instance : FP.Order Prop := FP.CPO_Prop.R_Prop
local instance : FP.Equiv Prop := FP.CPO_Prop.Equiv_Prop
local instance : FP.OmegaLub Prop := FP.CPO_Prop.oLub_Prop
local instance : FP.Bot Prop := FP.CPO_Prop.Bot_Prop
local instance : FP.PartialOrder_Setoid Prop := FP.CPO_Prop.PO_Prop
local instance : AUXLib.Equivalence (@FP.equiv Prop _) := FP.CPO_Prop.EquivEquivProp
local instance : FP.CompletePartialOrder_Setoid Prop := FP.CPO_Prop.CPO_Prop

example (P Q : Prop) :
    @FP.order_rel Prop FP.CPO_Prop.R_Prop P Q <-> (P -> Q) := by
  unfold_CPO_defs

example (f g : Nat -> Prop) :
    @FP.order_rel (Nat -> Prop) (FP.PO_lift.R_lift Nat) f g <->
      forall n, f n -> g n := by
  unfold_PO_defs
  rfl

example (P : Prop) : FP.order_rel FP.bot P := by
  solve_order FP.order_rel

example (T : Nat -> Prop) (hmono : FP.seq_mono T) :
    FP.seq_mono (fun n => T (n + 1)) := by
  solve_seq_mono FP.order_rel

example (T : Nat -> Prop) (P : Prop) (hmono : FP.seq_mono T)
    (hub : FP.seq_upper_bound T P) :
    FP.seq_upper_bound (fun n => T (n + 1)) P := by
  solve_seq_upper_bound FP.order_rel

example (f : Prop -> Prop) (hf : Proper (FP.order_rel ==> FP.order_rel) f) :
    FP.seq_mono (fun n => FP.nat_iter n f FP.bot) := by
  solve_seq_mono FP.order_rel

example (T1 T2 : Nat -> Prop) (h1 : FP.seq_mono T1) (h2 : FP.seq_mono T2)
    (hle : forall n, FP.order_rel (T1 n) (T2 n)) :
    FP.order_rel (FP.omega_lub T1) (FP.omega_lub T2) := by
  solve_order FP.order_rel

example (T : Nat -> Prop) (P : Prop) (hmono : FP.seq_mono T)
    (hub : FP.seq_upper_bound T P) : FP.order_rel (FP.omega_lub T) P := by
  solve_order FP.order_rel

example (f : Prop -> Prop) (hf : Proper (FP.order_rel ==> FP.order_rel) f)
    (P Q : Prop) (hPQ : FP.order_rel P Q) : FP.order_rel (f P) (f Q) := by
  solve_order FP.order_rel

example (f : Prop -> Prop -> Prop)
    (hf : Proper (FP.order_rel ==> FP.order_rel ==> FP.order_rel) f)
    (P P' Q Q' : Prop) (hP : FP.order_rel P P') (hQ : FP.order_rel Q Q') :
    FP.order_rel (f P Q) (f P' Q') := by
  solve_order FP.order_rel

example (f : Prop -> Prop -> Prop -> Prop)
    (hf : Proper
      (FP.order_rel ==> FP.order_rel ==> FP.order_rel ==> FP.order_rel) f)
    (P P' Q Q' R R' : Prop)
    (hP : FP.order_rel P P') (hQ : FP.order_rel Q Q')
    (hR : FP.order_rel R R') :
    FP.order_rel (f P Q R) (f P' Q' R') := by
  solve_order FP.order_rel

example (P Q : Prop) (hPQ : FP.equiv P Q) : FP.order_rel P Q := by
  solve_order FP.order_rel

example (P Q : Prop) (hQP : FP.equiv Q P) : FP.order_rel P Q := by
  solve_order FP.order_rel

example : True := by
  solve_seq_mono FP.order_rel
  trivial

end FixedPointTactics

section CompleteLatticeLift

local instance : FP.Order Prop := FP.CPO_Prop.R_Prop
local instance : FP.Equiv Prop := FP.CPO_Prop.Equiv_Prop
local instance : FP.Lub Prop := ⟨fun X => exists P, X P /\ P⟩
local instance : FP.Glb Prop := ⟨fun X => forall P, X P -> P⟩
local instance : FP.CompleteLattice_Setoid Prop where
  CL_PartialOrder := FP.CPO_Prop.PO_Prop
  CL_Complete_lub := by
    intro X
    constructor
    · intro P hP hTrue
      exact ⟨P, hP, hTrue⟩
    · intro Q hQ
      rintro ⟨P, hP, hTrue⟩
      exact hQ P hP hTrue
  lub_congr := by
    intro X Y h
    constructor
    · rintro ⟨P, hP, hTrue⟩; exact ⟨P, (h P).mp hP, hTrue⟩
    · rintro ⟨P, hP, hTrue⟩; exact ⟨P, (h P).mpr hP, hTrue⟩

example : FP.CompleteLattice_Setoid (Nat -> Prop) := inferInstance

example (X : (Nat -> Prop) -> Prop) :
    @FP.lub (Nat -> Prop) (FP.CL_sets.Lub_sets) X = Sets.general_union X := by
  unfold_CL_defs

example (X : (Nat -> Prop) -> Prop) (n : Nat) :
    (@FP.lub (Nat -> Prop) (FP.CL_lift.Lub_lift Nat) X) n <->
      exists f, X f /\ f n := by
  change (exists b, (exists f, X f /\ f n = b) /\ b) <-> _
  constructor
  · rintro ⟨b, ⟨f, hf, rfl⟩, hb⟩
    exact ⟨f, hf, hb⟩
  · rintro ⟨f, hf, hfn⟩
    exact ⟨f n, ⟨f, hf, rfl⟩, hfn⟩

end CompleteLatticeLift

example : FP.Lfix (fun _ : Prop => True) <-> True := by
  change (exists n, FP.nat_iter n (fun _ : Prop => True) False) <-> True
  constructor
  · intro; trivial
  · intro; exact ⟨1, trivial⟩

#print axioms FP.BourbakiWitt_fixpoint
#print axioms FP.KnasterTarski_fixpoint_theorem_g
#print axioms AUXLib.BW_LFix_is_fix
