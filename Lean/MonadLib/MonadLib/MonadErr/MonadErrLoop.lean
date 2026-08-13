import MonadLib.MonadErr.MonadErrBasic
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Generalize

universe u

namespace MonadLib

open AUXLib
open FP
open MonadErr
open scoped MonadNotation

instance oLub_program {Sigma : Type u} {A : Type} : OmegaLub (program Sigma A) where
  omega_lub := ProgramPO.indexed_union

instance bot_program {Sigma : Type u} {A : Type} : Bot (program Sigma A) where
  bot := ProgramPO.bot

instance oCPO_program {Sigma : Type u} {A : Type} :
    CompletePartialOrder_Setoid (program Sigma A) where
  CPO_PartialOrder := program_PO
  CPO_SeqCont T _ := by
    constructor
    · intro n
      exact ⟨fun s a s' h => ⟨n, h⟩, fun s h => ⟨n, h⟩⟩
    · intro upper hUpper
      constructor
      · rintro s a s' ⟨n, h⟩
        exact (hUpper n).nrmle s a s' h
      · rintro s ⟨n, h⟩
        exact (hUpper n).errle s h
  CPO_least _ := ⟨fun _ _ _ h => False.elim h, fun _ h => False.elim h⟩

instance Transitive_lift {A : Type} {B : Type u} [Order B]
    [AUXLib.Transitive (@order_rel B _)] :
    AUXLib.Transitive (@order_rel (A -> B) _) where
  trans _ _ _ h1 h2 a := AUXLib.Transitive.trans _ _ _ (h1 a) (h2 a)

instance Reflexive_lift {A : Type} {B : Type u} [Order B]
    [AUXLib.Reflexive (@order_rel B _)] :
    AUXLib.Reflexive (@order_rel (A -> B) _) where
  refl _ a := AUXLib.Reflexive.refl _

abbrev increasing {A : Type u} [Order A] (T : Nat -> A) : Prop := seq_mono T

abbrev mono {A B : Type u} [Order A] [Order B] (f : A -> B) : Prop :=
  Proper (order_rel ==> order_rel) f

abbrev continuous {A : Type u} [Order A] [OmegaLub A]
    {B : Type u} [Equiv B] [OmegaLub B] (f : A -> B) : Prop :=
  seq_continuous f

def mono_cont {A B : Type u} [Order A] [OmegaLub A]
    [Order B] [Equiv B] [OmegaLub B] (f : A -> B) : Prop :=
  mono f /\ continuous f

theorem BW_fixpoint' {A : Type u} [Order A] [Equiv A] [OmegaLub A] [Bot A]
    [AUXLib.Equivalence (@equiv A _)] [CompletePartialOrder_Setoid A]
    (f : A -> A) : mono_cont f -> equiv (BW_fix f) (f (BW_fix f)) := by
  rintro ⟨hm, hc⟩
  exact BourbakiWitt_fixpoint f hm hc

theorem increasing_program_plus {Sigma : Type u} {A B : Type}
    (m n : Nat) (c : Nat -> A -> program Sigma B) :
    increasing c -> order_rel (c n) (c (n + m)) := by
  intro h
  exact seq_mono_nat_le c h (Nat.le_add_right n m)

theorem increasing_program_le {Sigma : Type u} {A B : Type}
    (m n : Nat) (c : Nat -> A -> program Sigma B) :
    n <= m -> increasing c -> order_rel (c n) (c m) := by
  intro hle h
  exact seq_mono_nat_le c h hle

theorem increasing_program_plus' {Sigma : Type u} {B : Type}
    (m n : Nat) (c : Nat -> program Sigma B) :
    increasing c -> order_rel (c n) (c (n + m)) := by
  intro h
  exact seq_mono_nat_le c h (Nat.le_add_right n m)

theorem increasing_program_le' {Sigma : Type u} {B : Type}
    (m n : Nat) (c : Nat -> program Sigma B) :
    n <= m -> increasing c -> order_rel (c n) (c m) := by
  intro hle h
  exact seq_mono_nat_le c h hle

theorem mono_intro {Sigma : Type u} {A B : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B) :
    (forall a, mono fun W => f W a) -> mono f := by
  intro h
  constructor
  intro x y hxy a
  exact (h a).proper x y hxy

private theorem mono_bind_core {Sigma : Type u} {X : Type u} [Order X]
    {C D : Type} (c1 : X -> program Sigma D)
    (c2 : X -> D -> program Sigma C) :
    mono c1 -> (forall d, mono fun W => c2 W d) ->
      mono fun W => MonadErr.bind (c1 W) (c2 W) := by
  intro h1 h2
  constructor
  intro x y hxy
  have hc1 := h1.proper x y hxy
  constructor
  · rintro s c s' ⟨d, s0, hd, hc⟩
    exact ⟨d, s0, hc1.nrmle s d s0 hd, ((h2 d).proper x y hxy).nrmle s0 c s' hc⟩
  · intro s h
    rcases h with h | ⟨d, s0, hd, he⟩
    · exact Or.inl (hc1.errle s h)
    · exact Or.inr ⟨d, s0, hc1.nrmle s d s0 hd, ((h2 d).proper x y hxy).errle s0 he⟩

theorem mono_bind {Sigma : Type u} {A B C D : Type}
    (c1 : (A -> program Sigma B) -> program Sigma D)
    (c2 : (A -> program Sigma B) -> D -> program Sigma C) :
    mono c1 -> (forall d, mono fun W => c2 W d) ->
      mono fun W => MonadErr.bind (c1 W) (c2 W) :=
  mono_bind_core c1 c2

theorem mono_bind' {Sigma : Type u} {B C D : Type}
    (c1 : program Sigma B -> program Sigma D)
    (c2 : program Sigma B -> D -> program Sigma C) :
    mono c1 -> (forall d, mono fun W => c2 W d) ->
      mono fun W => MonadErr.bind (c1 W) (c2 W) :=
  mono_bind_core c1 c2

private theorem mono_choice_core {Sigma : Type u} {X : Type u} [Order X]
    {D : Type} (c1 c2 : X -> program Sigma D) :
    mono c1 -> mono c2 -> mono fun W => choice (c1 W) (c2 W) := by
  intro h1 h2
  constructor
  intro x y hxy
  have hc1 := h1.proper x y hxy
  have hc2 := h2.proper x y hxy
  constructor
  · rintro s d s' (h | h)
    · exact Or.inl (hc1.nrmle s d s' h)
    · exact Or.inr (hc2.nrmle s d s' h)
  · rintro s (h | h)
    · exact Or.inl (hc1.errle s h)
    · exact Or.inr (hc2.errle s h)

theorem mono_choice {Sigma : Type u} {A B D : Type}
    (c1 c2 : (A -> program Sigma B) -> program Sigma D) :
    mono c1 -> mono c2 -> mono fun W => choice (c1 W) (c2 W) :=
  mono_choice_core c1 c2

theorem mono_choice' {Sigma : Type u} {B D : Type}
    (c1 c2 : program Sigma B -> program Sigma D) :
    mono c1 -> mono c2 -> mono fun W => choice (c1 W) (c2 W) :=
  mono_choice_core c1 c2

theorem continuous_intro {Sigma : Type u} {A B : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B) :
    (forall a, continuous fun W => f W a) -> continuous f := by
  intro h T hT a
  exact h a T hT

private theorem continuous_const_core {Sigma : Type u} {X : Type u}
    [Order X] [OmegaLub X] {C : Type} (f : program Sigma C) :
    continuous fun _ : X => f := by
  intro _ _
  constructor
  · intro s c s'
    constructor
    · intro h; exact ⟨0, h⟩
    · rintro ⟨_, h⟩; exact h
  · intro s
    constructor
    · intro h; exact ⟨0, h⟩
    · rintro ⟨_, h⟩; exact h

theorem continuous_const {Sigma : Type u} {A B C : Type} (f : program Sigma C) :
    continuous fun _ : A -> program Sigma B => f :=
  continuous_const_core f

theorem continuous_const' {Sigma : Type u} {B C : Type} (f : program Sigma C) :
    continuous fun _ : program Sigma B => f :=
  continuous_const_core f

private theorem continuous_bind_core {Sigma : Type u} {X : Type u}
    [Order X] [OmegaLub X] [AUXLib.Reflexive (@order_rel X _)]
    [AUXLib.Transitive (@order_rel X _)] {C D : Type}
    (c1 : X -> program Sigma D) (c2 : X -> D -> program Sigma C) :
    mono c1 -> continuous c1 ->
    (forall d, mono fun W => c2 W d) ->
    (forall d, continuous fun W => c2 W d) ->
    continuous fun W => MonadErr.bind (c1 W) (c2 W) := by
  intro hm1 hc1 hm2 hc2 T hT
  have e1 := hc1 T hT
  constructor
  · intro s c s'
    constructor
    · rintro ⟨d, s0, hd, hc⟩
      rcases (e1.nrmequiv s d s0).mp hd with ⟨i, hi⟩
      rcases ((hc2 d T hT).nrmequiv s0 c s').mp hc with ⟨j, hj⟩
      let k := max i j
      have hik : i <= k := Nat.le_max_left _ _
      have hjk : j <= k := Nat.le_max_right _ _
      have hTik : order_rel (T i) (T k) := seq_mono_nat_le T hT hik
      have hTjk : order_rel (T j) (T k) := seq_mono_nat_le T hT hjk
      exact ⟨k, d, s0, (hm1.proper _ _ hTik).nrmle s d s0 hi,
        ((hm2 d).proper _ _ hTjk).nrmle s0 c s' hj⟩
    · rintro ⟨i, d, s0, hd, hc⟩
      exact ⟨d, s0, (e1.nrmequiv s d s0).mpr ⟨i, hd⟩,
        ((hc2 d T hT).nrmequiv s0 c s').mpr ⟨i, hc⟩⟩
  · intro s
    constructor
    · intro h
      rcases h with h | ⟨d, s0, hd, he⟩
      · rcases (e1.errequiv s).mp h with ⟨i, hi⟩
        exact ⟨i, Or.inl hi⟩
      · rcases (e1.nrmequiv s d s0).mp hd with ⟨i, hi⟩
        rcases ((hc2 d T hT).errequiv s0).mp he with ⟨j, hj⟩
        let k := max i j
        have hik : i <= k := Nat.le_max_left _ _
        have hjk : j <= k := Nat.le_max_right _ _
        have hTik : order_rel (T i) (T k) := seq_mono_nat_le T hT hik
        have hTjk : order_rel (T j) (T k) := seq_mono_nat_le T hT hjk
        exact ⟨k, Or.inr ⟨d, s0, (hm1.proper _ _ hTik).nrmle s d s0 hi,
          ((hm2 d).proper _ _ hTjk).errle s0 hj⟩⟩
    · rintro ⟨i, h | ⟨d, s0, hd, he⟩⟩
      · exact Or.inl ((e1.errequiv s).mpr ⟨i, h⟩)
      · exact Or.inr ⟨d, s0, (e1.nrmequiv s d s0).mpr ⟨i, hd⟩,
          ((hc2 d T hT).errequiv s0).mpr ⟨i, he⟩⟩

theorem continuous_bind {Sigma : Type u} {A B C D : Type}
    (c1 : (A -> program Sigma B) -> program Sigma D)
    (c2 : (A -> program Sigma B) -> D -> program Sigma C) :
    mono c1 -> continuous c1 ->
    (forall d, mono fun W => c2 W d) ->
    (forall d, continuous fun W => c2 W d) ->
    continuous fun W => MonadErr.bind (c1 W) (c2 W) :=
  continuous_bind_core c1 c2

theorem continuous_bind' {Sigma : Type u} {B C D : Type}
    (c1 : program Sigma B -> program Sigma D)
    (c2 : program Sigma B -> D -> program Sigma C) :
    mono c1 -> continuous c1 ->
    (forall d, mono fun W => c2 W d) ->
    (forall d, continuous fun W => c2 W d) ->
    continuous fun W => MonadErr.bind (c1 W) (c2 W) :=
  continuous_bind_core c1 c2

private theorem continuous_choice_core {Sigma : Type u} {X : Type u}
    [Order X] [OmegaLub X] {D : Type} (c1 c2 : X -> program Sigma D) :
    continuous c1 -> continuous c2 ->
      continuous fun W => choice (c1 W) (c2 W) := by
  intro h1 h2 T hT
  have e1 := h1 T hT
  have e2 := h2 T hT
  constructor
  · intro s d s'
    constructor
    · rintro (h | h)
      · rcases (e1.nrmequiv s d s').mp h with ⟨i, hi⟩; exact ⟨i, Or.inl hi⟩
      · rcases (e2.nrmequiv s d s').mp h with ⟨i, hi⟩; exact ⟨i, Or.inr hi⟩
    · rintro ⟨i, h | h⟩
      · exact Or.inl ((e1.nrmequiv s d s').mpr ⟨i, h⟩)
      · exact Or.inr ((e2.nrmequiv s d s').mpr ⟨i, h⟩)
  · intro s
    constructor
    · rintro (h | h)
      · rcases (e1.errequiv s).mp h with ⟨i, hi⟩; exact ⟨i, Or.inl hi⟩
      · rcases (e2.errequiv s).mp h with ⟨i, hi⟩; exact ⟨i, Or.inr hi⟩
    · rintro ⟨i, h | h⟩
      · exact Or.inl ((e1.errequiv s).mpr ⟨i, h⟩)
      · exact Or.inr ((e2.errequiv s).mpr ⟨i, h⟩)

theorem continuous_choice {Sigma : Type u} {A B D : Type}
    (c1 c2 : (A -> program Sigma B) -> program Sigma D) :
    continuous c1 -> continuous c2 ->
      continuous fun W => choice (c1 W) (c2 W) :=
  continuous_choice_core c1 c2

theorem continuous_choice' {Sigma : Type u} {B D : Type}
    (c1 c2 : program Sigma B -> program Sigma D) :
    continuous c1 -> continuous c2 ->
      continuous fun W => choice (c1 W) (c2 W) :=
  continuous_choice_core c1 c2

theorem mono_cont_intro {Sigma : Type u} {A B : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B) :
    (forall a, mono_cont fun W => f W a) -> mono_cont f := by
  intro h
  exact ⟨mono_intro f (fun a => (h a).1), continuous_intro f (fun a => (h a).2)⟩

theorem mono_cont_const {Sigma : Type u} {A B C : Type} (f : program Sigma C) :
    mono_cont fun _ : A -> program Sigma B => f :=
  ⟨⟨fun _ _ _ => AUXLib.Reflexive.refl f⟩, continuous_const f⟩

theorem mono_cont_const' {Sigma : Type u} {B C : Type} (f : program Sigma C) :
    mono_cont fun _ : program Sigma B => f :=
  ⟨⟨fun _ _ _ => AUXLib.Reflexive.refl f⟩, continuous_const' f⟩

theorem mono_cont_bind {Sigma : Type u} {A B C D : Type}
    (c1 : (A -> program Sigma B) -> program Sigma D)
    (c2 : (A -> program Sigma B) -> D -> program Sigma C) :
    mono_cont c1 -> (forall d, mono_cont fun W => c2 W d) ->
      mono_cont fun W => MonadErr.bind (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ h2
  exact ⟨mono_bind c1 c2 hm1 (fun d => (h2 d).1),
    continuous_bind c1 c2 hm1 hc1 (fun d => (h2 d).1) (fun d => (h2 d).2)⟩

theorem mono_cont_bind' {Sigma : Type u} {B C D : Type}
    (c1 : program Sigma B -> program Sigma D)
    (c2 : program Sigma B -> D -> program Sigma C) :
    mono_cont c1 -> (forall d, mono_cont fun W => c2 W d) ->
      mono_cont fun W => MonadErr.bind (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ h2
  exact ⟨mono_bind' c1 c2 hm1 (fun d => (h2 d).1),
    continuous_bind' c1 c2 hm1 hc1 (fun d => (h2 d).1) (fun d => (h2 d).2)⟩

theorem mono_cont_choice {Sigma : Type u} {A B D : Type}
    (c1 c2 : (A -> program Sigma B) -> program Sigma D) :
    mono_cont c1 -> mono_cont c2 ->
      mono_cont fun W => choice (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ ⟨hm2, hc2⟩
  exact ⟨mono_choice c1 c2 hm1 hm2, continuous_choice c1 c2 hc1 hc2⟩

theorem mono_cont_choice' {Sigma : Type u} {B D : Type}
    (c1 c2 : program Sigma B -> program Sigma D) :
    mono_cont c1 -> mono_cont c2 ->
      mono_cont fun W => choice (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ ⟨hm2, hc2⟩
  exact ⟨mono_choice' c1 c2 hm1 hm2, continuous_choice' c1 c2 hc1 hc2⟩

theorem increasing_mono_increasing {A B : Type u} [Order A] [Order B]
    (f : A -> B) (l : Nat -> A) :
    increasing l -> mono f -> increasing fun n => f (l n) := by
  intro hl hf n
  exact hf.proper _ _ (hl n)

theorem mono_BW_fix {A B : Type u} [Order A] [Order B] [Equiv B]
    [OmegaLub B] [Bot B] [AUXLib.Equivalence (@equiv B _)]
    [CompletePartialOrder_Setoid B] (f : A -> B -> B) :
    (forall a, mono (f a)) ->
    (forall b, mono (fun a => f a b)) ->
    mono (fun a => BW_fix (f a)) := by
  intro hfa hfb
  constructor
  intro x y hxy
  apply BourbakiWitt_fixpoint_monotonic (f x) (f y)
  · exact hfa x
  · exact hfa y
  · intro b1 b2 hb
    exact AUXLib.Transitive.trans _ (f y b1) _
      ((hfb b1).proper x y hxy) ((hfa y).proper b1 b2 hb)

theorem BW_fix_seq_cont_general {A B : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [CompletePartialOrder_Setoid A]
    [Order B] [Equiv B] [OmegaLub B] [Bot B]
    [AUXLib.Equivalence (@equiv A _)] [AUXLib.Equivalence (@equiv B _)]
    [CompletePartialOrder_Setoid B]
    (f : A -> B -> B)
    (hf : Proper (order_rel ==> order_rel ==> order_rel) f)
    (hfa : forall a, continuous (f a))
    (hfb : forall b, continuous (fun a => f a b)) :
    continuous (fun a => BW_fix (f a)) := by
  have hfaMono : forall a, mono (f a) := by
    intro a
    constructor
    intro x y hxy
    exact hf.proper a a (AUXLib.Reflexive.refl a) x y hxy
  have hfbMono : forall b, mono (fun a => f a b) := by
    intro b
    constructor
    intro x y hxy
    exact hf.proper x y hxy b b (AUXLib.Reflexive.refl b)
  have hfixMono : mono (fun a => BW_fix (f a)) :=
    mono_BW_fix f hfaMono hfbMono
  intro T hT
  apply (inferInstance : PartialOrder_Setoid B).PO_AntiSymmetric_Setoid.antisymmetricity_setoid
  · unfold BW_fix
    apply (limit_smaller_iff
      (fun n => FP.nat_iter n (f (omega_lub T)) bot)
      (omega_lub (fun n => BW_fix (f (T n))))
      (iter_bot_mono (f (omega_lub T)) (hfaMono (omega_lub T)))).mpr
    intro n
    induction n with
    | zero => exact (inferInstance : CompletePartialOrder_Setoid B).CPO_least _
    | succ n ih =>
        simp only [FP.nat_iter]
        apply AUXLib.Transitive.trans _
          (f (omega_lub T) (omega_lub (fun k => BW_fix (f (T k))))) _
        · exact hf.proper _ _ (AUXLib.Reflexive.refl _) _ _ ih
        · apply AUXLib.Transitive.trans _
            (omega_lub (fun k => f (T k)
              (omega_lub (fun j => BW_fix (f (T j)))))) _
          · exact (inferInstance : PartialOrder_Setoid B).PO_Reflexive_Setoid _ _
              (hfb (omega_lub (fun j => BW_fix (f (T j)))) T hT)
          · have hseq : increasing (fun k => f (T k)
                (omega_lub (fun j => BW_fix (f (T j))))) :=
              increasing_mono_increasing _ T hT
                (hfbMono (omega_lub (fun j => BW_fix (f (T j)))))
            apply (limit_smaller_iff _ _ hseq).mpr
            intro k
            apply AUXLib.Transitive.trans _
              (omega_lub (fun j => f (T k) (BW_fix (f (T j))))) _
            · have hfixSeq : increasing (fun j => BW_fix (f (T j))) :=
                increasing_mono_increasing _ T hT hfixMono
              exact (inferInstance : PartialOrder_Setoid B).PO_Reflexive_Setoid _ _
                (hfa (T k) (fun j => BW_fix (f (T j))) hfixSeq)
            · have hseq2 : increasing (fun j => f (T k) (BW_fix (f (T j)))) :=
                increasing_mono_increasing _ (fun j => BW_fix (f (T j)))
                  (increasing_mono_increasing _ T hT hfixMono) (hfaMono (T k))
              apply (limit_smaller_iff _ _ hseq2).mpr
              intro m
              have hfixSeq : increasing (fun j => BW_fix (f (T j))) :=
                increasing_mono_increasing _ T hT hfixMono
              apply limit_greater (fun j => BW_fix (f (T j))) _ hfixSeq
              let km := max k m
              refine ⟨km, ?_⟩
              have hfp : equiv (BW_fix (f (T km)))
                  (f (T km) (BW_fix (f (T km)))) :=
                BW_fixpoint' (f (T km)) ⟨hfaMono (T km), hfa (T km)⟩
              apply AUXLib.Transitive.trans _
                (f (T km) (BW_fix (f (T km)))) _
              · apply hf.proper
                · exact seq_mono_nat_le T hT (Nat.le_max_left _ _)
                · exact hfixMono.proper _ _
                    (seq_mono_nat_le T hT (Nat.le_max_right _ _))
              · exact (inferInstance : PartialOrder_Setoid B).PO_Reflexive_Setoid _ _
                  (AUXLib.Equivalence.symm _ _ hfp)
  · have hfixSeq : increasing (fun n => BW_fix (f (T n))) :=
      increasing_mono_increasing _ T hT hfixMono
    apply (limit_smaller_iff _ _ hfixSeq).mpr
    intro n
    exact hfixMono.proper _ _
      (limit_greater T (T n) hT ⟨n, AUXLib.Reflexive.refl _⟩)

theorem mono_cont_BW_fix {A B : Type u} [Order A] [Equiv A]
    [OmegaLub A] [Bot A] [CompletePartialOrder_Setoid A]
    [Order B] [Equiv B] [OmegaLub B] [Bot B]
    [AUXLib.Equivalence (@equiv A _)] [AUXLib.Equivalence (@equiv B _)]
    [CompletePartialOrder_Setoid B] (f : A -> B -> B) :
    (forall a, mono_cont (f a)) ->
    (forall b, mono_cont (fun a => f a b)) ->
    mono_cont (fun a => BW_fix (f a)) := by
  intro hfa hfb
  exact ⟨mono_BW_fix f (fun a => (hfa a).1) (fun b => (hfb b).1),
    BW_fix_seq_cont_general f
      (by
        constructor
        intro a1 a2 ha b1 b2 hb
        exact AUXLib.Transitive.trans _ (f a2 b1) _
          ((hfb b1).1.proper a1 a2 ha) ((hfa a2).1.proper b1 b2 hb))
      (fun a => (hfa a).2) (fun b => (hfb b).2)⟩

private theorem mono_cont_id_program {Sigma : Type u} {A : Type} :
    mono_cont (fun W : program Sigma A => W) := by
  constructor
  · constructor; intro _ _ h; exact h
  · intro _ _; exact AUXLib.Equivalence.refl _

private theorem mono_cont_proj_program {Sigma : Type u} {A B : Type} (a : A) :
    mono_cont (fun W : A -> program Sigma B => W a) := by
  constructor
  · constructor; intro _ _ h; exact h a
  · intro _ _; exact AUXLib.Equivalence.refl _

syntax "err_mono_cont_auto" : tactic
syntax "__err_mono_cont_match" : tactic

namespace MonoContTactic

open Lean Meta Elab Tactic

private partial def lambdaBody (e : Expr) : Expr :=
  match e.consumeMData with
  | .lam _ _ body _ => lambdaBody body
  | body => body

private def destructMatch : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.consumeMData.getAppFn.isConstOf ``mono_cont do
    throwError "mono_cont_auto: expected a mono_cont goal"
  let args := target.getAppArgs
  let some fn := args.back? | throwError "mono_cont_auto: malformed mono_cont goal"
  let some matcher ← matchMatcherApp? (lambdaBody fn) |
    throwError "mono_cont_auto: continuation body is not headed by match"
  let some discr := matcher.discrs[0]? |
    throwError "mono_cont_auto: match has no discriminant"
  if discr.hasLooseBVars then
    throwError "mono_cont_auto: match discriminant depends on a continuation binder"
  let (vars, generalizedGoal) ← goal.generalize #[{ expr := discr }]
  let some discrVar := vars[0]? |
    throwError "mono_cont_auto: failed to generalize match discriminant"
  let subgoals ← generalizedGoal.cases discrVar
  replaceMainGoal (subgoals.map (·.mvarId)).toList

end MonoContTactic

elab_rules : tactic
  | `(tactic| __err_mono_cont_match) => MonoContTactic.destructMatch

macro_rules
  | `(tactic| err_mono_cont_auto) =>
      `(tactic|
        first
          | (apply mono_cont_intro <;> err_mono_cont_auto)
          | (apply mono_cont_bind <;> err_mono_cont_auto)
          | (apply mono_cont_choice <;> err_mono_cont_auto)
          | (apply mono_cont_bind' <;> err_mono_cont_auto)
          | (apply mono_cont_choice' <;> err_mono_cont_auto)
          | (apply mono_cont_BW_fix <;> err_mono_cont_auto)
          | (__err_mono_cont_match <;> simp only <;> err_mono_cont_auto)
          | apply mono_cont_id_program
          | apply mono_cont_proj_program
          | apply mono_cont_const
          | apply mono_cont_const'
          | assumption
          | (intro; err_mono_cont_auto)
          | trivial)

def while_f {Sigma : Type u} (cond : program Sigma Bool) (body : program Sigma Unit)
    (W : program Sigma Unit) : program Sigma Unit :=
  x <- cond ;; if x then body ;; W else MonadErr.ret ()

def «while» {Sigma : Type u} (cond : program Sigma Bool) (body : program Sigma Unit) :
    program Sigma Unit :=
  BW_fix (while_f cond body)

def whileP_f {Sigma : Type u} (cond : Sigma -> Prop) (body : program Sigma Unit)
    (W : program Sigma Unit) : program Sigma Unit :=
  choice (test cond ;; body ;; W)
    (test (fun s => Not (cond s)) ;; MonadErr.ret ())

def whileP {Sigma : Type u} (cond : Sigma -> Prop) (body : program Sigma Unit) :
    program Sigma Unit :=
  BW_fix (whileP_f cond body)

def whileret_f {Sigma : Type u} {A : Type} (cond : A -> program Sigma Bool)
    (body : A -> program Sigma A) (W : A -> program Sigma A) :
    A -> program Sigma A :=
  fun a => x <- cond a ;; if x then MonadErr.bind (body a) W else MonadErr.ret a

def «continue» {Sigma : Type u} {A B : Type} (a : A) : program Sigma (CntOrBrk A B) :=
  MonadErr.ret (by_continue a)

def «break» {Sigma : Type u} {A B : Type} (b : B) : program Sigma (CntOrBrk A B) :=
  MonadErr.ret (by_break b)

def whileret {Sigma : Type u} {A : Type} (cond : A -> program Sigma Bool)
    (body : A -> program Sigma A) : A -> program Sigma A :=
  BW_fix (whileret_f cond body)

def whileretP_f {Sigma : Type u} {A : Type} (cond : A -> Sigma -> Prop)
    (body : A -> program Sigma A) (W : A -> program Sigma A) :
    A -> program Sigma A :=
  fun a => choice
    (test (fun s => cond a s) ;; a' <- body a ;; W a')
    (test (fun s => Not (cond a s)) ;; MonadErr.ret a)

def whileretP {Sigma : Type u} {A : Type} (cond : A -> Sigma -> Prop)
    (body : A -> program Sigma A) : A -> program Sigma A :=
  BW_fix (whileretP_f cond body)

def repeat_break_f {Sigma : Type u} {A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) (W : A -> program Sigma B) :
    A -> program Sigma B :=
  fun a => x <- body a ;; match x with
    | .by_continue a' => W a'
    | .by_break b => MonadErr.ret b

def repeat_break {Sigma : Type u} {A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) : A -> program Sigma B :=
  BW_fix (repeat_break_f body)

def repeat_break_f_noinput {Sigma : Type u} {B : Type}
    (body : program Sigma (CntOrBrk Unit B)) (W : program Sigma B) : program Sigma B :=
  x <- body ;; match x with
    | .by_continue _ => W
    | .by_break b => MonadErr.ret b

def repeat_break_noin {Sigma : Type u} {B : Type}
    (body : program Sigma (CntOrBrk Unit B)) : program Sigma B :=
  BW_fix (repeat_break_f_noinput body)

def range_iter_f {Sigma : Type u} {A : Type} (hi : Int)
    (body : Int -> A -> program Sigma A) (W : Int × A -> program Sigma A) :
    Int × A -> program Sigma A
  | (lo, a0) => choice
      (testPure (lo < hi) ;; a1 <- body lo a0 ;; W (lo + 1, a1))
      (testPure (lo >= hi) ;; MonadErr.ret a0)

def range_iter {Sigma : Type u} {A : Type} (lo hi : Int)
    (body : Int -> A -> program Sigma A) : A -> program Sigma A :=
  fun a => BW_fix (range_iter_f hi body) (lo, a)

def range_iter_break_f {Sigma : Type u} {A B : Type} (hi : Int)
    (body : Int -> A -> program Sigma (CntOrBrk A B))
    (W : Int × A -> program Sigma (CntOrBrk A B)) :
    Int × A -> program Sigma (CntOrBrk A B)
  | (lo, a0) => choice
      (testPure (lo < hi) ;; ab <- body lo a0 ;; match ab with
        | .by_continue a1 => W (lo + 1, a1)
        | .by_break b => «break» b)
      (testPure (lo >= hi) ;; «continue» a0)

def range_iter_break {Sigma : Type u} {A B : Type} (lo hi : Int)
    (body : Int -> A -> program Sigma (CntOrBrk A B)) :
    A -> program Sigma (CntOrBrk A B) :=
  fun a => BW_fix (range_iter_break_f hi body) (lo, a)

def forset_f {Sigma : Type} {A : Type} (body : A -> program Sigma Unit)
    (W : (A -> Prop) -> program Sigma Unit) («universe» : A -> Prop) :
    program Sigma Unit :=
  choice
    (a <- get (fun _ a => «universe» a) ;; body a ;;
      W (fun x => «universe» x /\ x ≠ a))
    (testPure (forall x, Not («universe» x)) ;; MonadErr.ret ())

def forset {Sigma : Type} {A : Type} («universe» : A -> Prop)
    (body : A -> program Sigma Unit) : program Sigma Unit :=
  BW_fix (forset_f body) «universe»

def Repeat_f {Sigma : Type u} (body : program Sigma Unit)
    (W : program Sigma Unit) : program Sigma Unit :=
  body ;; W

def Repeat {Sigma : Type u} (body : program Sigma Unit) : program Sigma Unit :=
  BW_fix (Repeat_f body)

def list_iter {Sigma : Type u} {A B : Type} (body : A -> B -> program Sigma B) :
    List A -> B -> program Sigma B
  | [], b => MonadErr.ret b
  | a :: rest, b => b0 <- body a b ;; list_iter body rest b0

def ret_some {Sigma : Type u} {A : Type} : Option A -> program Sigma Bool
  | some _ => MonadErr.ret true
  | none => MonadErr.ret false

private theorem while_f_mono_cont {Sigma : Type u}
    (cond : program Sigma Bool) (body : program Sigma Unit) :
    mono_cont (while_f cond body) := by
  unfold while_f
  apply mono_cont_bind'
  · exact mono_cont_const' cond
  · intro b
    cases b
    · exact mono_cont_const' (MonadErr.ret ())
    · apply mono_cont_bind'
      · exact mono_cont_const' body
      · intro _; exact mono_cont_id_program

private theorem whileP_f_mono_cont {Sigma : Type u}
    (cond : Sigma -> Prop) (body : program Sigma Unit) :
    mono_cont (whileP_f cond body) := by
  unfold whileP_f
  apply mono_cont_choice'
  · apply mono_cont_bind'
    · exact mono_cont_const' (test cond)
    · intro _
      apply mono_cont_bind'
      · exact mono_cont_const' body
      · intro _; exact mono_cont_id_program
  · exact mono_cont_const'
      (test (fun s => Not (cond s)) ;; MonadErr.ret ())

private theorem whileret_f_mono_cont {Sigma : Type u} {A : Type}
    (cond : A -> program Sigma Bool) (body : A -> program Sigma A) :
    mono_cont (whileret_f cond body) := by
  unfold whileret_f
  apply mono_cont_intro
  intro a
  apply mono_cont_bind
  · exact mono_cont_const (cond a)
  · intro b
    cases b
    · exact mono_cont_const (MonadErr.ret a)
    · apply mono_cont_bind
      · exact mono_cont_const (body a)
      · intro a'; exact mono_cont_proj_program a'

private theorem whileretP_f_mono_cont {Sigma : Type u} {A : Type}
    (cond : A -> Sigma -> Prop) (body : A -> program Sigma A) :
    mono_cont (whileretP_f cond body) := by
  unfold whileretP_f
  apply mono_cont_intro
  intro a
  apply mono_cont_choice
  · apply mono_cont_bind
    · exact mono_cont_const (test fun s => cond a s)
    · intro _
      apply mono_cont_bind
      · exact mono_cont_const (body a)
      · intro a'; exact mono_cont_proj_program a'
  · exact mono_cont_const
      (test (fun s => Not (cond a s)) ;; MonadErr.ret a)

private theorem repeat_break_f_mono_cont {Sigma : Type u} {A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) :
    mono_cont (repeat_break_f body) := by
  unfold repeat_break_f
  apply mono_cont_intro
  intro a
  apply mono_cont_bind
  · exact mono_cont_const (body a)
  · intro ab
    cases ab with
    | by_continue a' => exact mono_cont_proj_program a'
    | by_break b => exact mono_cont_const (MonadErr.ret b)

private theorem repeat_break_noin_f_mono_cont {Sigma : Type u} {B : Type}
    (body : program Sigma (CntOrBrk Unit B)) :
    mono_cont (repeat_break_f_noinput body) := by
  unfold repeat_break_f_noinput
  apply mono_cont_bind'
  · exact mono_cont_const' body
  · intro ab
    cases ab with
    | by_continue _ => exact mono_cont_id_program
    | by_break b => exact mono_cont_const' (MonadErr.ret b)

private theorem range_iter_f_mono_cont {Sigma : Type u} {A : Type}
    (hi : Int) (body : Int -> A -> program Sigma A) :
    mono_cont (range_iter_f hi body) := by
  unfold range_iter_f
  apply mono_cont_intro
  intro p
  rcases p with ⟨lo, a⟩
  apply mono_cont_choice
  · apply mono_cont_bind
    · exact mono_cont_const (testPure (lo < hi))
    · intro _
      apply mono_cont_bind
      · exact mono_cont_const (body lo a)
      · intro a'; exact mono_cont_proj_program (lo + 1, a')
  · exact mono_cont_const (testPure (lo >= hi) ;; MonadErr.ret a)

private theorem range_iter_break_f_mono_cont {Sigma : Type u} {A B : Type}
    (hi : Int) (body : Int -> A -> program Sigma (CntOrBrk A B)) :
    mono_cont (range_iter_break_f hi body) := by
  unfold range_iter_break_f
  apply mono_cont_intro
  intro p
  rcases p with ⟨lo, a⟩
  apply mono_cont_choice
  · apply mono_cont_bind
    · exact mono_cont_const (testPure (lo < hi))
    · intro _
      apply mono_cont_bind
      · exact mono_cont_const (body lo a)
      · intro ab
        cases ab with
        | by_continue a' => exact mono_cont_proj_program (lo + 1, a')
        | by_break b => exact mono_cont_const («break» b)
  · exact mono_cont_const (testPure (lo >= hi) ;; «continue» a)

private theorem forset_f_mono_cont {Sigma : Type} {A : Type}
    (body : A -> program Sigma Unit) : mono_cont (forset_f body) := by
  unfold forset_f
  apply mono_cont_intro
  intro uPred
  apply mono_cont_choice
  · apply mono_cont_bind
    · exact mono_cont_const (get fun _ a => uPred a)
    · intro a
      apply mono_cont_bind
      · exact mono_cont_const (body a)
      · intro _; exact mono_cont_proj_program (fun x => uPred x /\ x ≠ a)
  · exact mono_cont_const
      (testPure (forall x, Not (uPred x)) ;; MonadErr.ret ())

theorem while_unfold {Sigma : Type u} (cond : program Sigma Bool)
    (body : program Sigma Unit) :
    equiv («while» cond body)
      (x <- cond ;; if x then body ;; «while» cond body else MonadErr.ret ()) := by
  simpa [«while», while_f] using BW_fixpoint' (while_f cond body)
    (while_f_mono_cont cond body)

theorem whileP_unfold {Sigma : Type u} (cond : Sigma -> Prop)
    (body : program Sigma Unit) :
    equiv (whileP cond body)
      (choice (test cond ;; body ;; whileP cond body)
        (test (fun s => Not (cond s)) ;; MonadErr.ret ())) := by
  simpa [whileP, whileP_f] using BW_fixpoint' (whileP_f cond body)
    (whileP_f_mono_cont cond body)

theorem whileret_unfold {Sigma : Type u} {A : Type}
    (cond : A -> program Sigma Bool) (body : A -> program Sigma A) :
    equiv (whileret cond body)
      (fun a => x <- cond a ;;
        if x then y <- body a ;; whileret cond body y else MonadErr.ret a) := by
  simpa [whileret, whileret_f] using BW_fixpoint' (whileret_f cond body)
    (whileret_f_mono_cont cond body)

theorem whileret_unfold_apply {Sigma : Type u} {A : Type}
    (cond : A -> program Sigma Bool) (body : A -> program Sigma A) (a : A) :
    equiv (whileret cond body a)
      (x <- cond a ;;
        if x then y <- body a ;; whileret cond body y else MonadErr.ret a) :=
  whileret_unfold cond body a

theorem repeat_break_unfold {Sigma : Type u} {A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) :
    equiv (repeat_break body) (fun a =>
      x <- body a ;; match x with
        | .by_continue a0 => repeat_break body a0
        | .by_break b0 => MonadErr.ret b0) := by
  simpa [repeat_break, repeat_break_f] using BW_fixpoint' (repeat_break_f body)
    (repeat_break_f_mono_cont body)

theorem repeat_break_unfold_apply {Sigma : Type u} {A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) (a : A) :
    equiv (repeat_break body a)
      (x <- body a ;; match x with
        | .by_continue a0 => repeat_break body a0
        | .by_break b0 => MonadErr.ret b0) :=
  repeat_break_unfold body a

theorem repeat_break_noin_unfold {Sigma : Type u} {B : Type}
    (body : program Sigma (CntOrBrk Unit B)) :
    equiv (repeat_break_noin body)
      (x <- body ;; match x with
        | .by_continue _ => repeat_break_noin body
        | .by_break b0 => MonadErr.ret b0) := by
  simpa [repeat_break_noin, repeat_break_f_noinput] using
    BW_fixpoint' (repeat_break_f_noinput body) (repeat_break_noin_f_mono_cont body)

theorem range_iter_unfold_aux {Sigma : Type u} {A : Type} (hi : Int)
    (body : Int -> A -> program Sigma A) :
    equiv (fun p : Int × A => range_iter p.1 hi body p.2)
      (fun p => choice
        (testPure (p.1 < hi) ;; b <- body p.1 p.2 ;;
          range_iter (p.1 + 1) hi body b)
        (testPure (p.1 >= hi) ;; MonadErr.ret p.2)) := by
  simpa [range_iter, range_iter_f] using BW_fixpoint' (range_iter_f hi body)
    (range_iter_f_mono_cont hi body)

theorem range_iter_unfold {Sigma : Type u} {A : Type} (hi : Int)
    (body : Int -> A -> program Sigma A) (lo : Int) (a : A) :
    equiv (range_iter lo hi body a)
      (choice
        (testPure (lo < hi) ;; b <- body lo a ;;
          range_iter (lo + 1) hi body b)
        (testPure (lo >= hi) ;; MonadErr.ret a)) :=
  range_iter_unfold_aux hi body (lo, a)

theorem range_iter_break_unfold_aux {Sigma : Type u} {A B : Type} (hi : Int)
    (body : Int -> A -> program Sigma (CntOrBrk A B)) :
    equiv (fun p : Int × A => range_iter_break p.1 hi body p.2)
      (fun p => choice
        (testPure (p.1 < hi) ;; b <- body p.1 p.2 ;; match b with
          | .by_continue a' => range_iter_break (p.1 + 1) hi body a'
          | .by_break b' => «break» b')
        (testPure (p.1 >= hi) ;; «continue» p.2)) := by
  simpa [range_iter_break, range_iter_break_f] using
    BW_fixpoint' (range_iter_break_f hi body) (range_iter_break_f_mono_cont hi body)

theorem range_iter_break_unfold {Sigma : Type u} {A B : Type} (hi : Int)
    (body : Int -> A -> program Sigma (CntOrBrk A B)) (lo : Int) (a : A) :
    equiv (range_iter_break lo hi body a)
      (choice
        (testPure (lo < hi) ;; b <- body lo a ;; match b with
          | .by_continue al => range_iter_break (lo + 1) hi body al
          | .by_break br => «break» br)
        (testPure (lo >= hi) ;; «continue» a)) :=
  range_iter_break_unfold_aux hi body (lo, a)

theorem forset_unfold_aux {Sigma : Type} {A : Type}
    (body : A -> program Sigma Unit) :
    equiv (BW_fix (forset_f body)) (fun uPred =>
      choice
        (a <- get (fun _ a => uPred a) ;; body a ;;
          forset (fun x => uPred x /\ x ≠ a) body)
        (testPure (forall x, Not (uPred x)) ;; MonadErr.ret ())) := by
  simpa [forset, forset_f] using BW_fixpoint' (forset_f body)
    (forset_f_mono_cont body)

theorem forset_unfold {Sigma : Type} {A : Type} (uPred : A -> Prop)
    (body : A -> program Sigma Unit) :
    equiv (forset uPred body)
      (choice
        (a <- get (fun _ a => uPred a) ;; body a ;;
          forset (fun x => uPred x /\ x ≠ a) body)
        (testPure (forall x, Not (uPred x)) ;; MonadErr.ret ())) :=
  forset_unfold_aux body uPred

theorem list_iter_nil_unfold {Sigma : Type u} {A B : Type}
    (body : A -> B -> program Sigma B) (b : B) :
    equiv (list_iter body [] b) (MonadErr.ret b) :=
  AUXLib.Equivalence.refl _

theorem list_iter_cons_unfold {Sigma : Type u} {A B : Type}
    (a : A) (xs : List A) (body : A -> B -> program Sigma B) (b : B) :
    equiv (list_iter body (a :: xs) b)
      (b0 <- body a b ;; list_iter body xs b0) :=
  AUXLib.Equivalence.refl _

macro "err_unfold_loop" : tactic =>
  `(tactic|
    (repeat first
      | rel_rw [while_unfold]
      | rel_rw [whileP_unfold]
      | rel_rw [whileret_unfold_apply]
      | rel_rw [whileret_unfold]
      | rel_rw [repeat_break_unfold_apply]
      | rel_rw [repeat_break_unfold]
      | rel_rw [repeat_break_noin_unfold]
      | rel_rw [range_iter_unfold]
      | rel_rw [range_iter_break_unfold]
      | rel_rw [forset_unfold]) <;>
    try exact AUXLib.Equivalence.refl _)

macro "err_unfold_loop" " in " loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic|
    repeat first
      | rel_rw [while_unfold] at $loc
      | rel_rw [whileP_unfold] at $loc
      | rel_rw [whileret_unfold_apply] at $loc
      | rel_rw [whileret_unfold] at $loc
      | rel_rw [repeat_break_unfold_apply] at $loc
      | rel_rw [repeat_break_unfold] at $loc
      | rel_rw [repeat_break_noin_unfold] at $loc
      | rel_rw [range_iter_unfold] at $loc
      | rel_rw [range_iter_break_unfold] at $loc
      | rel_rw [forset_unfold] at $loc)

end MonadLib
