import Std.Tactic
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Apply
import AUXLib.Morphisms
import FP.PartialOrder_Setoid
import SetsClass.SetsDomain

universe u v

namespace FP

open AUXLib

def seq_upper_bound {A : Type u} [Order A] (T : Nat -> A) (bnd : A) : Prop :=
  forall n, order_rel (T n) bnd

def seq_least_upper_bound {A : Type u} [Order A]
    (T : Nat -> A) (bnd : A) : Prop :=
  seq_upper_bound T bnd /\
    forall bnd', seq_upper_bound T bnd' -> order_rel bnd bnd'

def least_element {A : Type u} [Order A] (bot : A) : Prop :=
  forall a, order_rel bot a

def seq_mono {A : Type u} [Order A] (T : Nat -> A) : Prop :=
  forall n, order_rel (T n) (T (n + 1))

class OmegaLub (A : Type u) where
  omega_lub : (Nat -> A) -> A

class Bot (A : Type u) where
  bot : A

abbrev omega_lub {A : Type u} [o : OmegaLub A] : (Nat -> A) -> A := o.omega_lub
abbrev bot {A : Type u} [b : Bot A] : A := b.bot

class CompletePartialOrder_Setoid (A : Type u) [Order A] [Equiv A]
    [OmegaLub A] [Bot A] : Prop where
  CPO_PartialOrder : PartialOrder_Setoid A
  CPO_SeqCont : forall T : Nat -> A,
    @seq_mono A _ T -> @seq_least_upper_bound A _ T (@omega_lub A _ T)
  CPO_least : @least_element A _ (@bot A _)

class CompletePartialOrder_Strong_Setoid (A : Type u) [Order A] [Equiv A]
    [OmegaLub A] [Bot A] : Prop where
  CPOs_CompletePartialOrder : CompletePartialOrder_Setoid A
  CPOs_SeqCont : forall T : Nat -> A,
    @seq_least_upper_bound A _ T (@omega_lub A _ T)

instance cpoPartialOrder (A : Type u) [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : CompletePartialOrder_Setoid A] : PartialOrder_Setoid A := c.CPO_PartialOrder

instance strongCpo (A : Type u) [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : CompletePartialOrder_Strong_Setoid A] : CompletePartialOrder_Setoid A :=
  c.CPOs_CompletePartialOrder

def limit_congr {A : Type u} [Equiv A] (oLubA : OmegaLub A) : Prop :=
  forall T1 T2 : Nat -> A,
    (forall n, equiv (T1 n) (T2 n)) ->
      equiv (@omega_lub A oLubA T1) (@omega_lub A oLubA T2)

def seq_continuous {A : Type u} [Order A] [OmegaLub A]
    {B : Type v} [Equiv B] [OmegaLub B] (f : A -> B) : Prop :=
  forall T : Nat -> A, seq_mono T ->
    equiv (f (omega_lub T)) (omega_lub (fun n => f (T n)))

def nat_iter {A : Type u} (n : Nat) (f : A -> A) (a : A) : A :=
  Nat.rec a (fun _ r => f r) n

def BW_fix {A : Type u} [OmegaLub A] [Bot A] (f : A -> A) : A :=
  omega_lub (fun n => nat_iter n f bot)

theorem limit_smaller_iff {A : Type u} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : CompletePartialOrder_Setoid A] (xs : Nat -> A) (y : A)
    (hmono : seq_mono xs) :
    order_rel (omega_lub xs) y <-> forall n, order_rel (xs n) y := by
  rcases c.CPO_SeqCont xs hmono with ⟨hub, hleast⟩
  constructor
  · intro h n
    exact c.CPO_PartialOrder.PO_Transitive.trans _ _ _ (hub n) h
  · intro h
    exact hleast y h

theorem limit_greater {A : Type u} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [c : CompletePartialOrder_Setoid A] (xs : Nat -> A) (y : A)
    (hmono : seq_mono xs) (h : exists n, order_rel y (xs n)) :
    order_rel y (omega_lub xs) := by
  rcases h with ⟨n, hyn⟩
  rcases c.CPO_SeqCont xs hmono with ⟨hub, _⟩
  exact c.CPO_PartialOrder.PO_Transitive.trans _ _ _ hyn (hub n)

theorem limit_mono {A : Type u} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [AUXLib.Equivalence (@equiv A _)] [CompletePartialOrder_Setoid A]
    (T1 T2 : Nat -> A) (h1 : seq_mono T1) (h2 : seq_mono T2)
    (hle : lift_rel2 order_rel T1 T2) :
    order_rel (omega_lub T1) (omega_lub T2) := by
  apply (limit_smaller_iff T1 (omega_lub T2) h1).mpr
  intro n
  exact limit_greater T2 (T1 n) h2 ⟨n, hle n⟩

theorem CPOs_limit_congr {A : Type u} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Strong_Setoid A] : limit_congr (inferInstance : OmegaLub A) := by
  intro T1 T2 h
  apply c.CPOs_CompletePartialOrder.CPO_PartialOrder.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
  · exact (c.CPOs_SeqCont T1).2 _ (fun n =>
      c.CPOs_CompletePartialOrder.CPO_PartialOrder.PO_Transitive.trans _ (T2 n) _
        (c.CPOs_CompletePartialOrder.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (h n))
        ((c.CPOs_SeqCont T2).1 n))
  · exact (c.CPOs_SeqCont T2).2 _ (fun n =>
      c.CPOs_CompletePartialOrder.CPO_PartialOrder.PO_Transitive.trans _ (T1 n) _
        (c.CPOs_CompletePartialOrder.CPO_PartialOrder.PO_Reflexive_Setoid _ _
          (e.symm _ _ (h n)))
        ((c.CPOs_SeqCont T1).1 n))

theorem const_limit {A : Type u} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [e : AUXLib.Equivalence (@equiv A _)] [c : CompletePartialOrder_Setoid A]
    (a : A) : equiv (omega_lub (fun _ => a)) a := by
  apply c.CPO_PartialOrder.PO_AntiSymmetric_Setoid.antisymmetricity_setoid
  · exact (limit_smaller_iff (fun _ => a) a
      (fun _ => c.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (e.refl a))).mpr
      (fun _ => c.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (e.refl a))
  · exact limit_greater (fun _ => a) a
      (fun _ => c.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (e.refl a))
      ⟨0, c.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (e.refl a)⟩

theorem seq_mono_nat_le {A : Type u} [Order A]
    [r : Reflexive (@order_rel A _)] [t : Transitive (@order_rel A _)]
    (T : Nat -> A) (hmono : seq_mono T) {n m : Nat} (hnm : n <= m) :
    order_rel (T n) (T m) := by
  induction hnm with
  | refl => exact r.refl _
  | @step m hnm ih => exact t.trans _ _ _ ih (hmono m)

theorem seq_least_upper_bound_unique {A : Type u} [Order A] [Equiv A]
    [p : PartialOrder_Setoid A] (T : Nat -> A) (bnd1 bnd2 : A)
    (h1 : seq_least_upper_bound T bnd1)
    (h2 : seq_least_upper_bound T bnd2) : equiv bnd1 bnd2 :=
  p.PO_AntiSymmetric_Setoid.antisymmetricity_setoid _ _
    (h1.2 _ h2.1) (h2.2 _ h1.1)

theorem iter_bot_mono {A : Type u} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [e : AUXLib.Equivalence (@equiv A _)] [c : CompletePartialOrder_Setoid A]
    (f : A -> A) (hf : Proper (order_rel ==> order_rel) f) :
    seq_mono (fun n => nat_iter n f bot) := by
  intro n
  induction n with
  | zero => exact c.CPO_least (f bot)
  | succ n ih =>
      simpa [nat_iter] using hf.proper _ _ ih

theorem seq_mono_without_0_seq_mono {A : Type u} [Order A]
    (T : Nat -> A) (h : seq_mono T) : seq_mono (fun n => T (n + 1)) :=
  fun n => h (n + 1)

theorem seq_mono_without_0_upper_bound {A : Type u} [Order A]
    (T : Nat -> A) (bnd : A) (_ : seq_mono T) (h : seq_upper_bound T bnd) :
    seq_upper_bound (fun n => T (n + 1)) bnd := fun n => h (n + 1)

theorem seq_mono_without_0_upper_bound_inv {A : Type u} [Order A]
    [t : Transitive (@order_rel A _)] (T : Nat -> A) (bnd : A)
    (hmono : seq_mono T) (h : seq_upper_bound (fun n => T (n + 1)) bnd) :
    seq_upper_bound T bnd := by
  intro n
  cases n with
  | zero => exact t.trans _ (T 1) _ (hmono 0) (h 0)
  | succ n => simpa using h n

theorem seq_mono_without_0_least_upper_bound {A : Type u} [Order A]
    [Transitive (@order_rel A _)] (T : Nat -> A) (bnd : A)
    (hmono : seq_mono T) (h : seq_least_upper_bound T bnd) :
    seq_least_upper_bound (fun n => T (n + 1)) bnd := by
  constructor
  · exact seq_mono_without_0_upper_bound T bnd hmono h.1
  · intro bnd' hbnd'
    exact h.2 _ (seq_mono_without_0_upper_bound_inv T bnd' hmono hbnd')

theorem seq_mono_without_0_limit {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Setoid A] (T : Nat -> A) (hmono : seq_mono T) :
    equiv (omega_lub T) (omega_lub (fun n => T (n + 1))) := by
  apply seq_least_upper_bound_unique (fun n => T (n + 1))
  · exact seq_mono_without_0_least_upper_bound T (omega_lub T) hmono
      (c.CPO_SeqCont T hmono)
  · exact c.CPO_SeqCont _ (seq_mono_without_0_seq_mono T hmono)

theorem seq_mono_squeeze_limit {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Setoid A] (T1 T2 : Nat -> A)
    (h1 : seq_mono T1) (h2 : seq_mono T2)
    (hle : forall n, order_rel (T1 n) (T2 n))
    (hub : forall n, order_rel (T2 n) (omega_lub T1)) :
    equiv (omega_lub T1) (omega_lub T2) := by
  apply seq_least_upper_bound_unique T2
  · constructor
    · exact hub
    · intro bnd hbnd
      exact (c.CPO_SeqCont T1 h1).2 _ (fun n =>
        c.CPO_PartialOrder.PO_Transitive.trans _ _ _ (hle n) (hbnd n))
  · exact c.CPO_SeqCont T2 h2

theorem BourbakiWitt_fixpoint {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Setoid A] (f : A -> A)
    (hf : Proper (order_rel ==> order_rel) f) (hcont : seq_continuous f) :
    equiv (BW_fix f) (f (BW_fix f)) := by
  let T : Nat -> A := fun n => nat_iter n f bot
  have hmono : seq_mono T := iter_bot_mono f hf
  have hcont' := hcont T hmono
  have htail := seq_mono_without_0_limit T hmono
  exact e.trans _ _ _ htail (e.symm _ _ hcont')

theorem BourbakiWitt_least_fixpoint {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Setoid A] (f : A -> A) (p : A)
    (hf : Proper (order_rel ==> order_rel) f) (_ : seq_continuous f)
    (hp : fixpoint f p) : order_rel (BW_fix f) p := by
  apply (limit_smaller_iff _ p (iter_bot_mono f hf)).mpr
  intro n
  induction n with
  | zero => exact c.CPO_least p
  | succ n ih =>
      have hfp := hf.proper _ _ ih
      exact c.CPO_PartialOrder.PO_Transitive.trans _ (f p) _ hfp
        (c.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (e.symm _ _ hp))

theorem BourbakiWitt_fixpoint_monotonic {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [AUXLib.Equivalence (@equiv A _)]
    [CompletePartialOrder_Setoid A] (f g : A -> A)
    (hf : Proper (order_rel ==> order_rel) f)
    (hg : Proper (order_rel ==> order_rel) g)
    (hfg : forall a b, order_rel a b -> order_rel (f a) (g b)) :
    order_rel (BW_fix f) (BW_fix g) := by
  apply limit_mono _ _ (iter_bot_mono f hf) (iter_bot_mono g hg)
  intro n
  induction n with
  | zero => exact (inferInstance : Reflexive (@order_rel A _)).refl bot
  | succ n ih => simpa [nat_iter] using hfg _ _ ih

theorem BourbakiWitt_fixpoint_mono {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Strong_Setoid A] (f g : A -> A)
    (hf : Proper (order_rel ==> order_rel) f)
    (hfg : forall a b, order_rel a b -> order_rel (f a) (g b)) :
    order_rel (BW_fix f) (BW_fix g) := by
  apply (c.CPOs_SeqCont _).2
  intro n
  have hiter : order_rel (nat_iter n f bot) (nat_iter n g bot) := by
    induction n with
    | zero => exact (inferInstance : Reflexive (@order_rel A _)).refl bot
    | succ n ih => simpa [nat_iter] using hfg _ _ ih
  exact c.CPOs_CompletePartialOrder.CPO_PartialOrder.PO_Transitive.trans _ _ _
    hiter ((c.CPOs_SeqCont _).1 n)

theorem BourbakiWitt_fixpoint_mono' {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Strong_Setoid A] (f g : A -> A)
    (hf : Proper (order_rel ==> order_rel) f)
    (hfg : forall a, order_rel (f a) (g a)) :
    order_rel (BW_fix f) (BW_fix g) :=
  BourbakiWitt_fixpoint_mono f g hf (fun a b hab =>
    c.CPOs_CompletePartialOrder.CPO_PartialOrder.PO_Transitive.trans _ (f b) _
      (hf.proper _ _ hab) (hfg b))

theorem BourbakiWitt_fixpoint_congr {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Strong_Setoid A] (f g : A -> A)
    (hfg : forall a b, equiv a b -> equiv (f a) (g b)) :
    equiv (BW_fix f) (BW_fix g) := by
  apply CPOs_limit_congr
  intro n
  induction n with
  | zero => exact e.refl bot
  | succ n ih => simpa [nat_iter] using hfg _ _ ih

theorem BourbakiWitt_fixpoint_congr' {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Strong_Setoid A] (f g : A -> A)
    (hf : Proper (equiv ==> equiv) f)
    (hfg : forall a, equiv (f a) (g a)) :
    equiv (BW_fix f) (BW_fix g) :=
  BourbakiWitt_fixpoint_congr f g (fun a b hab =>
    e.trans _ _ _ (hf.proper _ _ hab) (hfg b))

theorem BourbakiWitt_fixpoint_relax {A : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [e : AUXLib.Equivalence (@equiv A _)]
    [c : CompletePartialOrder_Setoid A] (f g : A -> A)
    (hf : Proper (order_rel ==> order_rel) f)
    (hg : Proper (order_rel ==> order_rel) g)
    (hfc : seq_continuous f) (hgc : seq_continuous g)
    (hstep : forall a b, order_rel a b -> order_rel a (f a) ->
      order_rel (f a) (g b))
    (hclosed : forall b,
      (forall a, order_rel a b -> order_rel (f a) b) ->
      forall a, order_rel a b -> order_rel (g a) b) :
    equiv (BW_fix f) (BW_fix g) := by
  have hmonoF := iter_bot_mono f hf
  have hmonoG := iter_bot_mono g hg
  have hFG : forall n, order_rel (nat_iter n f bot) (nat_iter n g bot) := by
    intro n
    induction n with
    | zero => exact c.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (e.refl bot)
    | succ n ih =>
        exact hstep _ _ ih (hmonoF n)
  have hGub : forall n, order_rel (nat_iter n g bot) (BW_fix f) := by
    intro n
    induction n with
    | zero => exact c.CPO_least _
    | succ n ih =>
        apply hclosed (BW_fix f)
        · intro a ha
          have hfix := BourbakiWitt_fixpoint f hf hfc
          exact c.CPO_PartialOrder.PO_Transitive.trans _ (f (BW_fix f)) _
            (hf.proper _ _ ha)
            (c.CPO_PartialOrder.PO_Reflexive_Setoid _ _ (e.symm _ _ hfix))
        · exact ih
  exact seq_mono_squeeze_limit _ _ hmonoF hmonoG hFG hGub

namespace CPO_sets

instance oLub_sets {T : Type} [Sets.SETS T] : OmegaLub T where
  omega_lub := fun xs => @Sets.indexed_union Nat T _ xs

instance Bot_sets {T : Type} [Sets.SETS T] : Bot T where
  bot := Sets.empty

instance CPO_sets {T : Type} [Sets.SETS T] [SETS_Properties T] :
    CompletePartialOrder_Setoid T where
  CPO_PartialOrder := PO_sets.PO_sets
  CPO_SeqCont := by
    intro xs _
    constructor
    · intro n; exact Sets_included_indexed_union (I := Nat) n xs
    · intro bnd h; exact Sets_indexed_union_included (I := Nat) xs bnd h
  CPO_least := Sets_empty_included

instance CPOs_sets {T : Type} [Sets.SETS T] [SETS_Properties T] :
    CompletePartialOrder_Strong_Setoid T where
  CPOs_CompletePartialOrder := CPO_sets
  CPOs_SeqCont := by
    intro xs
    exact ⟨fun n => Sets_included_indexed_union (I := Nat) n xs,
      fun bnd h => Sets_indexed_union_included (I := Nat) xs bnd h⟩

end CPO_sets

namespace CPO_Prop

instance R_Prop : Order Prop := ⟨fun P Q => P -> Q⟩
instance Equiv_Prop : Equiv Prop := ⟨Iff⟩
instance oLub_Prop : OmegaLub Prop := ⟨fun P => exists n, P n⟩
instance Bot_Prop : Bot Prop := ⟨False⟩

instance PO_Prop : PartialOrder_Setoid Prop where
  PO_AntiSymmetric_Setoid := ⟨by intro P Q hPQ hQP; exact ⟨hPQ, hQP⟩⟩
  PO_Reflexive_Setoid := by intro P Q h; exact h.mp
  PO_Transitive := ⟨by intro P Q R hPQ hQR hP; exact hQR (hPQ hP)⟩

instance EquivEquivProp : AUXLib.Equivalence (@equiv Prop Equiv_Prop) :=
  AUXLib.iff_equivalence

instance CPO_Prop : CompletePartialOrder_Setoid Prop where
  CPO_PartialOrder := PO_Prop
  CPO_SeqCont := by
    intro xs _
    constructor
    · intro n h; exact ⟨n, h⟩
    · intro bnd hbnd
      rintro ⟨n, hn⟩
      exact hbnd n hn
  CPO_least := by intro _ h; exact h.elim

end CPO_Prop

namespace CPO_Prop_flip

instance R_Prop_flip : Order Prop := ⟨fun P Q => Q -> P⟩
instance Equiv_Prop_flip : Equiv Prop := ⟨Iff⟩
instance oLub_Prop_flip : OmegaLub Prop := ⟨fun P => forall n, P n⟩
instance Bot_Prop_flip : Bot Prop := ⟨True⟩

instance PO_Prop_flip : PartialOrder_Setoid Prop where
  PO_AntiSymmetric_Setoid := ⟨by intro P Q hPQ hQP; exact ⟨hQP, hPQ⟩⟩
  PO_Reflexive_Setoid := by intro P Q h; exact h.mpr
  PO_Transitive := ⟨by intro P Q R hPQ hQR hR; exact hPQ (hQR hR)⟩

instance EquivEquivPropFlip : AUXLib.Equivalence (@equiv Prop Equiv_Prop_flip) :=
  AUXLib.iff_equivalence

instance CPO_Prop_flip : CompletePartialOrder_Setoid Prop where
  CPO_PartialOrder := PO_Prop_flip
  CPO_SeqCont := by
    intro xs _
    constructor
    · intro n hall; exact hall n
    · intro bnd hbnd hB n
      exact hbnd n hB
  CPO_least := by intro _ _; trivial

end CPO_Prop_flip

namespace CPO_lift

instance oLub_lift (A : Type u) {B : Type v} [OmegaLub B] : OmegaLub (A -> B) where
  omega_lub := lift_binder omega_lub

instance Bot_lift (A : Type u) {B : Type v} [Bot B] : Bot (A -> B) where
  bot := lift_fun0 bot

instance CPO_lift (A : Type u) {B : Type v} [Order B] [Equiv B]
    [OmegaLub B] [Bot B] [c : CompletePartialOrder_Setoid B] :
    CompletePartialOrder_Setoid (A -> B) where
  CPO_PartialOrder := PO_lift.PO_lift A
  CPO_SeqCont := by
    intro T hmono
    constructor
    · intro n a
      exact (c.CPO_SeqCont (fun m => T m a) (fun m => hmono m a)).1 n
    · intro bnd hbnd a
      exact (c.CPO_SeqCont (fun m => T m a) (fun m => hmono m a)).2 _
        (fun n => hbnd n a)
  CPO_least := by intro f a; exact c.CPO_least (f a)

end CPO_lift

macro "unfold_CPO_defs" : tactic =>
  `(tactic| simp only [order_rel, equiv, omega_lub, bot,
      PO_sets.R_sets, PO_sets.Equiv_sets, CPO_sets.oLub_sets, CPO_sets.Bot_sets,
      CPO_Prop.R_Prop, CPO_Prop.Equiv_Prop, CPO_Prop.oLub_Prop, CPO_Prop.Bot_Prop,
      CPO_Prop_flip.R_Prop_flip, CPO_Prop_flip.Equiv_Prop_flip,
      CPO_Prop_flip.oLub_Prop_flip, CPO_Prop_flip.Bot_Prop_flip,
      PO_lift.R_lift, PO_lift.Equiv_lift, CPO_lift.oLub_lift,
      CPO_lift.Bot_lift, lift_rel2, lift_binder, lift_fun0,
      Sets.indexed_union, Sets.empty])

syntax "apply_local_proper" : tactic

elab_rules : tactic
  | `(tactic| apply_local_proper) => do
      let goal <- Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        for fvarId in (← Lean.getLCtx).getFVarIds.reverse do
          let type <- Lean.instantiateMVars (← fvarId.getType)
          let args := type.getAppArgs
          if type.getAppFn.isConstOf ``AUXLib.Proper && args.size == 3 then
            let saved <- Lean.Elab.Tactic.saveState
            try
              let level <- Lean.Meta.getLevel args[0]!
              let projection := Lean.mkConst ``AUXLib.Proper.proper [level]
              let proof := Lean.mkAppN projection
                #[args[0]!, args[1]!, args[2]!, Lean.mkFVar fvarId]
              Lean.Elab.Tactic.setGoals (← goal.apply proof)
              return
            catch _ =>
              saved.restore
        Lean.Elab.throwAbortTactic

macro "solve_seq_mono" term : tactic =>
  `(tactic| first
    | assumption
    | (apply iter_bot_mono <;> assumption)
    | (apply seq_mono_without_0_seq_mono <;> assumption)
    | (intro n; first | assumption | grind)
    | skip)

macro "solve_seq_upper_bound" term : tactic =>
  `(tactic| first
    | assumption
    | (apply seq_mono_without_0_upper_bound <;> assumption)
    | (intro n; first | assumption | grind)
    | skip)

macro "solve_order" r:term : tactic =>
  `(tactic| first
    | assumption
    | rfl
    | apply CompletePartialOrder_Setoid.CPO_least
    | (apply limit_mono
       · solve_seq_mono $r
       · solve_seq_mono $r
       · intro n; first | assumption | grind)
    | (refine (limit_smaller_iff _ _ ?_).mpr ?_
       · solve_seq_mono $r
       · first | assumption | (intro n; first | assumption | grind))
    | (apply PartialOrder_Setoid.PO_Reflexive_Setoid
       assumption)
    | (apply PartialOrder_Setoid.PO_Reflexive_Setoid
       apply AUXLib.Equivalence.symm
       assumption)
    | (apply_local_proper <;> first | assumption | rfl | grind)
    | grind
    | skip)

end FP

export FP (seq_upper_bound seq_least_upper_bound least_element seq_mono OmegaLub Bot
  omega_lub bot CompletePartialOrder_Setoid CompletePartialOrder_Strong_Setoid
  limit_congr seq_continuous BW_fix limit_smaller_iff limit_greater limit_mono
  CPOs_limit_congr const_limit seq_mono_nat_le seq_least_upper_bound_unique
  iter_bot_mono seq_mono_without_0_seq_mono seq_mono_without_0_upper_bound
  seq_mono_without_0_upper_bound_inv seq_mono_without_0_least_upper_bound
  seq_mono_without_0_limit seq_mono_squeeze_limit BourbakiWitt_fixpoint
  BourbakiWitt_least_fixpoint BourbakiWitt_fixpoint_monotonic
  BourbakiWitt_fixpoint_mono BourbakiWitt_fixpoint_mono'
  BourbakiWitt_fixpoint_congr BourbakiWitt_fixpoint_congr'
  BourbakiWitt_fixpoint_relax nat_iter)
