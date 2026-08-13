import MonadLib.StateRelMonad.StateRelBasic
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Generalize

namespace MonadLib.StateRelMonad

open AUXLib FP
open scoped MonadNotation

abbrev increasing {A : Type} [Sets.SETS A] (T : Nat -> A) : Prop :=
  sseq_mono T

abbrev mono {A B : Type} [Sets.SETS A] [Sets.SETS B] (f : A -> B) : Prop :=
  Proper (Sets.included ==> Sets.included) f

abbrev continuous {A B : Type} [Sets.SETS A] [Sets.SETS B]
    (f : A -> B) : Prop :=
  sseq_continuous f

def mono_cont {A B : Type} [Sets.SETS A] [Sets.SETS B] (f : A -> B) : Prop :=
  mono f /\ continuous f

theorem Lfix_fixpoint' {A : Type} [Sets.SETS A] [SETS_Properties A]
    (f : A -> A) : mono_cont f -> Sets.equiv (Lfix f) (f (Lfix f)) := by
  rintro ⟨hm, hc⟩
  exact Lfix_fixpoint f hm hc

theorem increasing_mono_increasing {A B : Type} [Sets.SETS A] [Sets.SETS B]
    (f : A -> B) (l : Nat -> A) :
    increasing l -> mono f -> increasing fun n => f (l n) := by
  intro hl hf n
  exact hf.proper _ _ (hl n)

theorem increasing_program_plus {Sigma A B : Type}
    (m n : Nat) (c : Nat -> A -> program Sigma B) :
    increasing c -> Sets.included (c n) (c (n + m)) := by
  intro h
  exact sseq_mono_nat_le c h (Nat.le_add_right n m)

theorem increasing_program_le {Sigma A B : Type}
    (m n : Nat) (c : Nat -> A -> program Sigma B) :
    n <= m -> increasing c -> Sets.included (c n) (c m) := by
  intro hle h
  exact sseq_mono_nat_le c h hle

theorem increasing_program_plus' {Sigma B : Type}
    (m n : Nat) (c : Nat -> program Sigma B) :
    increasing c -> Sets.included (c n) (c (n + m)) := by
  intro h
  exact sseq_mono_nat_le c h (Nat.le_add_right n m)

theorem increasing_program_le' {Sigma B : Type}
    (m n : Nat) (c : Nat -> program Sigma B) :
    n <= m -> increasing c -> Sets.included (c n) (c m) := by
  intro hle h
  exact sseq_mono_nat_le c h hle

theorem mono_intro {Sigma A B : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B) :
    (forall a, mono fun W => f W a) -> mono f := by
  intro h
  constructor
  intro x y hxy a
  exact (h a).proper x y hxy

private theorem mono_bind_core {Sigma X C D : Type} [Sets.SETS X]
    (c1 : X -> program Sigma D) (c2 : X -> D -> program Sigma C) :
    mono c1 -> (forall d, mono fun W => c2 W d) ->
      mono fun W => bind (c1 W) (c2 W) := by
  intro h1 h2
  constructor
  intro x y hxy s c s'
  rintro ⟨d, s0, hd, hc⟩
  exact ⟨d, s0, h1.proper x y hxy s d s0 hd,
    (h2 d).proper x y hxy s0 c s' hc⟩

theorem mono_bind {Sigma A B C D : Type}
    (c1 : (A -> program Sigma B) -> program Sigma D)
    (c2 : (A -> program Sigma B) -> D -> program Sigma C) :
    mono c1 -> (forall d, mono fun W => c2 W d) ->
      mono fun W => bind (c1 W) (c2 W) :=
  mono_bind_core c1 c2

theorem mono_bind' {Sigma B C D : Type}
    (c1 : program Sigma B -> program Sigma D)
    (c2 : program Sigma B -> D -> program Sigma C) :
    mono c1 -> (forall d, mono fun W => c2 W d) ->
      mono fun W => bind (c1 W) (c2 W) :=
  mono_bind_core c1 c2

private theorem mono_choice_core {Sigma X D : Type} [Sets.SETS X]
    (c1 c2 : X -> program Sigma D) :
    mono c1 -> mono c2 -> mono fun W => choice (c1 W) (c2 W) := by
  intro h1 h2
  constructor
  intro x y hxy s d s'
  rintro (h | h)
  · exact Or.inl (h1.proper x y hxy s d s' h)
  · exact Or.inr (h2.proper x y hxy s d s' h)

theorem mono_choice {Sigma A B D : Type}
    (c1 c2 : (A -> program Sigma B) -> program Sigma D) :
    mono c1 -> mono c2 -> mono fun W => choice (c1 W) (c2 W) :=
  mono_choice_core c1 c2

theorem mono_choice' {Sigma B D : Type}
    (c1 c2 : program Sigma B -> program Sigma D) :
    mono c1 -> mono c2 -> mono fun W => choice (c1 W) (c2 W) :=
  mono_choice_core c1 c2

theorem continuous_intro {Sigma A B : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B) :
    (forall a, continuous fun W => f W a) -> continuous f := by
  intro h T hT a
  exact h a T hT

private theorem continuous_const_core {Sigma X C : Type} [Sets.SETS X]
    (f : program Sigma C) : continuous fun _ : X => f := by
  intro _ _ s c s'
  change f s c s' <-> exists _ : Nat, f s c s'
  constructor
  · exact fun h => ⟨0, h⟩
  · rintro ⟨_, h⟩
    exact h

theorem continuous_const {Sigma A B C : Type} (f : program Sigma C) :
    continuous fun _ : A -> program Sigma B => f :=
  continuous_const_core f

theorem continuous_const' {Sigma B C : Type} (f : program Sigma C) :
    continuous fun _ : program Sigma B => f :=
  continuous_const_core f

private theorem continuous_bind_core {Sigma X C D : Type}
    [Sets.SETS X] [SETS_Properties X]
    (c1 : X -> program Sigma D) (c2 : X -> D -> program Sigma C) :
    mono c1 -> continuous c1 ->
    (forall d, mono fun W => c2 W d) ->
    (forall d, continuous fun W => c2 W d) ->
    continuous fun W => bind (c1 W) (c2 W) := by
  intro hm1 hc1 hm2 hc2 T hT
  have e1 := hc1 T hT
  intro s c s'
  constructor
  · rintro ⟨d, s0, hd, hc⟩
    rcases (e1 s d s0).mp hd with ⟨i, hi⟩
    rcases ((hc2 d T hT) s0 c s').mp hc with ⟨j, hj⟩
    let k := max i j
    have hik : i <= k := Nat.le_max_left _ _
    have hjk : j <= k := Nat.le_max_right _ _
    have hTik : Sets.included (T i) (T k) := sseq_mono_nat_le T hT hik
    have hTjk : Sets.included (T j) (T k) := sseq_mono_nat_le T hT hjk
    exact ⟨k, d, s0, hm1.proper _ _ hTik s d s0 hi,
      (hm2 d).proper _ _ hTjk s0 c s' hj⟩
  · rintro ⟨i, d, s0, hd, hc⟩
    exact ⟨d, s0, (e1 s d s0).mpr ⟨i, hd⟩,
      ((hc2 d T hT) s0 c s').mpr ⟨i, hc⟩⟩

theorem continuous_bind {Sigma A B C D : Type}
    (c1 : (A -> program Sigma B) -> program Sigma D)
    (c2 : (A -> program Sigma B) -> D -> program Sigma C) :
    mono c1 -> continuous c1 ->
    (forall d, mono fun W => c2 W d) ->
    (forall d, continuous fun W => c2 W d) ->
    continuous fun W => bind (c1 W) (c2 W) :=
  continuous_bind_core c1 c2

theorem continuous_bind' {Sigma B C D : Type}
    (c1 : program Sigma B -> program Sigma D)
    (c2 : program Sigma B -> D -> program Sigma C) :
    mono c1 -> continuous c1 ->
    (forall d, mono fun W => c2 W d) ->
    (forall d, continuous fun W => c2 W d) ->
    continuous fun W => bind (c1 W) (c2 W) :=
  continuous_bind_core c1 c2

private theorem continuous_choice_core {Sigma X D : Type} [Sets.SETS X]
    (c1 c2 : X -> program Sigma D) :
    continuous c1 -> continuous c2 ->
      continuous fun W => choice (c1 W) (c2 W) := by
  intro h1 h2 T hT
  have e1 := h1 T hT
  have e2 := h2 T hT
  intro s d s'
  constructor
  · rintro (h | h)
    · rcases (e1 s d s').mp h with ⟨i, hi⟩
      exact ⟨i, Or.inl hi⟩
    · rcases (e2 s d s').mp h with ⟨i, hi⟩
      exact ⟨i, Or.inr hi⟩
  · rintro ⟨i, h | h⟩
    · exact Or.inl ((e1 s d s').mpr ⟨i, h⟩)
    · exact Or.inr ((e2 s d s').mpr ⟨i, h⟩)

theorem continuous_choice {Sigma A B D : Type}
    (c1 c2 : (A -> program Sigma B) -> program Sigma D) :
    continuous c1 -> continuous c2 ->
      continuous fun W => choice (c1 W) (c2 W) :=
  continuous_choice_core c1 c2

theorem continuous_choice' {Sigma B D : Type}
    (c1 c2 : program Sigma B -> program Sigma D) :
    continuous c1 -> continuous c2 ->
      continuous fun W => choice (c1 W) (c2 W) :=
  continuous_choice_core c1 c2

theorem mono_cont_intro {Sigma A B : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B) :
    (forall a, mono_cont fun W => f W a) -> mono_cont f := by
  intro h
  exact ⟨mono_intro f (fun a => (h a).1),
    continuous_intro f (fun a => (h a).2)⟩

theorem mono_cont_const {Sigma A B C : Type} (f : program Sigma C) :
    mono_cont fun _ : A -> program Sigma B => f :=
  ⟨⟨fun _ _ _ => Sets_included_refl.refl f⟩, continuous_const f⟩

theorem mono_cont_const' {Sigma B C : Type} (f : program Sigma C) :
    mono_cont fun _ : program Sigma B => f :=
  ⟨⟨fun _ _ _ => Sets_included_refl.refl f⟩, continuous_const' f⟩

theorem mono_cont_bind {Sigma A B C D : Type}
    (c1 : (A -> program Sigma B) -> program Sigma D)
    (c2 : (A -> program Sigma B) -> D -> program Sigma C) :
    mono_cont c1 -> (forall d, mono_cont fun W => c2 W d) ->
      mono_cont fun W => bind (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ h2
  exact ⟨mono_bind c1 c2 hm1 (fun d => (h2 d).1),
    continuous_bind c1 c2 hm1 hc1 (fun d => (h2 d).1) (fun d => (h2 d).2)⟩

theorem mono_cont_bind' {Sigma B C D : Type}
    (c1 : program Sigma B -> program Sigma D)
    (c2 : program Sigma B -> D -> program Sigma C) :
    mono_cont c1 -> (forall d, mono_cont fun W => c2 W d) ->
      mono_cont fun W => bind (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ h2
  exact ⟨mono_bind' c1 c2 hm1 (fun d => (h2 d).1),
    continuous_bind' c1 c2 hm1 hc1 (fun d => (h2 d).1) (fun d => (h2 d).2)⟩

theorem mono_cont_choice {Sigma A B D : Type}
    (c1 c2 : (A -> program Sigma B) -> program Sigma D) :
    mono_cont c1 -> mono_cont c2 ->
      mono_cont fun W => choice (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ ⟨hm2, hc2⟩
  exact ⟨mono_choice c1 c2 hm1 hm2, continuous_choice c1 c2 hc1 hc2⟩

theorem mono_cont_choice' {Sigma B D : Type}
    (c1 c2 : program Sigma B -> program Sigma D) :
    mono_cont c1 -> mono_cont c2 ->
      mono_cont fun W => choice (c1 W) (c2 W) := by
  rintro ⟨hm1, hc1⟩ ⟨hm2, hc2⟩
  exact ⟨mono_choice' c1 c2 hm1 hm2, continuous_choice' c1 c2 hc1 hc2⟩

theorem mono_Lfix {A B : Type} [Sets.SETS A] [Sets.SETS B]
    [SETS_Properties A] [SETS_Properties B] (f : A -> B -> B) :
    (forall a, mono (f a)) ->
    (forall b, mono fun W => f W b) ->
      mono fun W => Lfix (f W) := by
  intro hfa hfb
  constructor
  intro x y hxy
  apply Lfix_mono
  · exact hfa x
  · intro b
    exact (hfb b).proper x y hxy

theorem Lfix_seq_cont_general {A B : Type}
    [Sets.SETS A] [SETS_Properties A] [Sets.SETS B] [SETS_Properties B]
    (f : A -> B -> B)
    (hfMono : Proper (Sets.included ==> Sets.included ==> Sets.included) f)
    (hfaContinuous : forall a, continuous (f a))
    (hfbContinuous : forall b, continuous fun a => f a b) :
    continuous fun a => Lfix (f a) := by
  intro T hT
  apply (Sets_equiv_Sets_included _ _).mpr
  constructor
  · unfold Lfix
    apply Sets_indexed_union_included
    intro n
    induction n with
    | zero =>
        exact Sets_empty_included _
    | succ n ih =>
        change Sets.included
          (f (Sets.indexed_union T)
            (nat_iter n (f (Sets.indexed_union T)) Sets.empty))
          (Sets.indexed_union fun n => Lfix (f (T n)))
        apply Sets_included_trans.trans _ _ _
          ((hfMono.proper (Sets.indexed_union T)
            (Sets.indexed_union T) (Sets_included_refl.refl _)) _ _ ih)
        have hParam := hfbContinuous
          (Sets.indexed_union fun n => Lfix (f (T n))) T hT
        apply Sets_included_trans.trans _ _ _
          ((Sets_equiv_Sets_included _ _).mp hParam |>.1)
        apply Sets_indexed_union_included
        intro m
        have hLfixMono : sseq_mono (fun k => Lfix (f (T k))) := by
          intro k
          apply Lfix_mono
          · exact ⟨hfMono.proper _ _ (Sets_included_refl.refl _)⟩
          · intro b
            exact (hfMono.proper _ _ (hT k)) _ _
              (Sets_included_refl.refl _)
        have hArg := hfaContinuous (T m)
          (fun k => Lfix (f (T k))) hLfixMono
        apply Sets_included_trans.trans _ _ _
          ((Sets_equiv_Sets_included _ _).mp hArg |>.1)
        apply Sets_indexed_union_included
        intro k
        let mk := max m k
        have hTk : Sets.included (T k) (T mk) :=
          sseq_mono_nat_le T hT (Nat.le_max_right m k)
        have hTm : Sets.included (T m) (T mk) :=
          sseq_mono_nat_le T hT (Nat.le_max_left m k)
        apply Sets_included_trans.trans _ _ _
          ((hfMono.proper _ _ hTm) _ _
            (Lfix_mono _ _
              ⟨hfMono.proper _ _ (Sets_included_refl.refl _)⟩
              (fun b => (hfMono.proper _ _ hTk) _ _
                (Sets_included_refl.refl _))))
        apply Sets_included_trans.trans _ _ _
          ((Sets_equiv_Sets_included _ _).mp
            (Lfix_fixpoint (f (T mk))
              ⟨hfMono.proper _ _ (Sets_included_refl.refl _)⟩
              (hfaContinuous (T mk))) |>.2)
        exact Sets_included_indexed_union mk (fun n => Lfix (f (T n)))
  · apply Sets_indexed_union_included
    intro n
    apply Lfix_mono
    · exact ⟨hfMono.proper _ _ (Sets_included_refl.refl _)⟩
    · intro b
      exact (hfMono.proper _ _
        (Sets_included_indexed_union n T)) _ _
        (Sets_included_refl.refl _)

theorem mono_cont_Lfix {A B : Type} [Sets.SETS A] [Sets.SETS B]
    [SETS_Properties A] [SETS_Properties B] (f : A -> B -> B) :
    (forall a, mono_cont (f a)) ->
    (forall b, mono_cont fun W => f W b) ->
      mono_cont fun W => Lfix (f W) := by
  intro hfa hfb
  constructor
  · apply mono_Lfix f
    · intro a
      exact (hfa a).1
    · intro b
      exact (hfb b).1
  · apply Lfix_seq_cont_general f
    · exact ⟨fun x y hxy b1 b2 hb =>
        Sets_included_trans.trans _ _ _
          ((hfa x).1.proper b1 b2 hb)
          ((hfb b2).1.proper x y hxy)⟩
    · intro a
      exact (hfa a).2
    · intro b
      exact (hfb b).2

private theorem mono_cont_id_program {Sigma A : Type} :
    mono_cont (fun W : program Sigma A => W) := by
  constructor
  · constructor
    intro _ _ h
    exact h
  · intro _ _
    exact Sets_equiv_refl _

private theorem mono_cont_proj_program {Sigma A B : Type} (a : A) :
    mono_cont (fun W : A -> program Sigma B => W a) := by
  constructor
  · constructor
    intro _ _ h
    exact h a
  · intro _ _
    exact Sets_equiv_refl _

syntax "state_mono_cont_auto" : tactic
syntax "__state_mono_cont_match" : tactic

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
    throwError "state_mono_cont_auto: expected a StateRelMonad.mono_cont goal"
  let args := target.getAppArgs
  let some fn := args.back? |
    throwError "state_mono_cont_auto: malformed mono_cont goal"
  let some matcher ← matchMatcherApp? (lambdaBody fn) |
    throwError "state_mono_cont_auto: continuation body is not headed by match"
  let some discr := matcher.discrs[0]? |
    throwError "state_mono_cont_auto: match has no discriminant"
  if discr.hasLooseBVars then
    throwError "state_mono_cont_auto: match discriminant depends on a continuation binder"
  let (vars, generalizedGoal) ← goal.generalize #[{ expr := discr }]
  let some discrVar := vars[0]? |
    throwError "state_mono_cont_auto: failed to generalize match discriminant"
  let subgoals ← generalizedGoal.cases discrVar
  replaceMainGoal (subgoals.map (·.mvarId)).toList

end MonoContTactic

elab_rules : tactic
  | `(tactic| __state_mono_cont_match) => MonoContTactic.destructMatch

macro_rules
  | `(tactic| state_mono_cont_auto) =>
      `(tactic|
        first
          | (apply mono_cont_intro <;> state_mono_cont_auto)
          | (apply mono_cont_bind <;> state_mono_cont_auto)
          | (apply mono_cont_choice <;> state_mono_cont_auto)
          | (apply mono_cont_bind' <;> state_mono_cont_auto)
          | (apply mono_cont_choice' <;> state_mono_cont_auto)
          | (apply mono_cont_Lfix <;> intro <;> state_mono_cont_auto)
          | (__state_mono_cont_match <;> simp only <;> state_mono_cont_auto)
          | apply mono_cont_id_program
          | apply mono_cont_proj_program
          | apply mono_cont_const
          | apply mono_cont_const'
          | assumption
          | (intro; state_mono_cont_auto)
          | trivial)

theorem whileb_unfold {Sigma : Type} (cond : program Sigma Bool)
    (body : program Sigma Unit) :
    Sets.equiv («while» cond body)
      (x <- cond ;; match x with | true => body ;; «while» cond body | false => ret ()) := by
  apply Lfix_fixpoint'
  unfold while_f
  state_mono_cont_auto

theorem whileretb_unfold {Sigma A : Type} (cond : A -> program Sigma Bool)
    (body : A -> program Sigma A) (a : A) :
    Sets.equiv (whileret cond body a)
      (x <- cond a ;;
        match x with
        | true => bind (body a) (whileret cond body)
        | false => ret a) := by
  have h := Lfix_fixpoint' (whileret_f cond body)
  exact h (by unfold whileret_f; state_mono_cont_auto) a

theorem while_unfold {Sigma : Type} (cond : Sigma -> Prop)
    (body : program Sigma Unit) :
    Sets.equiv (whileP cond body)
      (choice (test cond ;; body ;; whileP cond body)
        (test (fun s => Not (cond s)) ;; ret ())) := by
  apply Lfix_fixpoint'
  unfold whileP_f
  state_mono_cont_auto

theorem whileret_unfold {Sigma A : Type} (cond : A -> Sigma -> Prop)
    (body : A -> program Sigma A) :
    Sets.equiv (whileretP cond body)
      (fun a => choice
        (test (fun s => cond a s) ;; a' <- body a ;; whileretP cond body a')
        (test (fun s => Not (cond a s)) ;; ret a)) := by
  apply Lfix_fixpoint'
  unfold whileretP_f
  state_mono_cont_auto

theorem Repeat_unfold {Sigma : Type} (body : program Sigma Unit) :
    Sets.equiv (Repeat body) (body ;; Repeat body) := by
  apply Lfix_fixpoint'
  unfold Repeat_f
  state_mono_cont_auto

theorem repeat_break_unfold {Sigma A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) :
    Sets.equiv (repeat_break body)
      (fun a => x <- body a ;;
        match x with
        | .by_continue a' => repeat_break body a'
        | .by_break b => ret b) := by
  apply Lfix_fixpoint'
  unfold repeat_break_f
  state_mono_cont_auto

theorem repeat_break_noin_unfold {Sigma B : Type}
    (body : program Sigma (CntOrBrk Unit B)) :
    Sets.equiv (repeat_break_noin body)
      (x <- body ;;
        match x with
        | .by_continue _ => repeat_break_noin body
        | .by_break b => ret b) := by
  apply Lfix_fixpoint'
  unfold repeat_break_f_noinput
  state_mono_cont_auto

theorem forset_unfold_aux {Sigma A : Type} (body : A -> program Sigma Unit) :
    Sets.equiv (Lfix (forset_f body))
      (fun uPred => choice
        (a <- get (fun _ a => uPred a) ;;
          body a ;;
          forset (fun x => uPred x /\ x ≠ a) body)
        (test' (forall x, Not (uPred x)) ;; ret ())) := by
  apply Lfix_fixpoint'
  unfold forset_f
  state_mono_cont_auto

theorem forset_unfold {Sigma A : Type} (uPred : A -> Prop)
    (body : A -> program Sigma Unit) :
    Sets.equiv (forset uPred body)
      (choice
        (a <- get (fun _ a => uPred a) ;;
          body a ;;
          forset (fun x => uPred x /\ x ≠ a) body)
      (test' (forall x, Not (uPred x)) ;; ret ())) := by
  exact forset_unfold_aux body uPred

private theorem whileb_unfold_eq {Sigma : Type} (cond : program Sigma Bool)
    (body : program Sigma Unit) :
    «while» cond body =
      (x <- cond ;; match x with | true => body ;; «while» cond body | false => ret ()) :=
  program_eq_of_equiv (whileb_unfold cond body)

private theorem whileretb_unfold_eq {Sigma A : Type}
    (cond : A -> program Sigma Bool) (body : A -> program Sigma A) (a : A) :
    whileret cond body a =
      (x <- cond a ;;
        match x with
        | true => bind (body a) (whileret cond body)
        | false => ret a) :=
  program_eq_of_equiv (whileretb_unfold cond body a)

private theorem while_unfold_eq {Sigma : Type} (cond : Sigma -> Prop)
    (body : program Sigma Unit) :
    whileP cond body =
      choice (test cond ;; body ;; whileP cond body)
        (test (fun s => Not (cond s)) ;; ret ()) :=
  program_eq_of_equiv (while_unfold cond body)

private theorem whileret_unfold_eq {Sigma A : Type}
    (cond : A -> Sigma -> Prop) (body : A -> program Sigma A) :
    whileretP cond body =
      fun a => choice
        (test (fun s => cond a s) ;; a' <- body a ;; whileretP cond body a')
        (test (fun s => Not (cond a s)) ;; ret a) := by
  funext a
  exact program_eq_of_equiv (whileret_unfold cond body a)

private theorem Repeat_unfold_eq {Sigma : Type}
    (body : program Sigma Unit) :
    Repeat body = (body ;; Repeat body) :=
  program_eq_of_equiv (Repeat_unfold body)

private theorem repeat_break_unfold_eq {Sigma A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) :
    repeat_break body =
      fun a => x <- body a ;;
        match x with
        | .by_continue a' => repeat_break body a'
        | .by_break b => ret b := by
  funext a
  exact program_eq_of_equiv (repeat_break_unfold body a)

private theorem repeat_break_noin_unfold_eq {Sigma B : Type}
    (body : program Sigma (CntOrBrk Unit B)) :
    repeat_break_noin body =
      (x <- body ;;
        match x with
        | .by_continue _ => repeat_break_noin body
        | .by_break b => ret b) :=
  program_eq_of_equiv (repeat_break_noin_unfold body)

private theorem forset_unfold_eq {Sigma A : Type} (uPred : A -> Prop)
    (body : A -> program Sigma Unit) :
    forset uPred body =
      choice
        (a <- get (fun _ a => uPred a) ;;
          body a ;;
          forset (fun x => uPred x /\ x ≠ a) body)
        (test' (forall x, Not (uPred x)) ;; ret ()) :=
  program_eq_of_equiv (forset_unfold uPred body)

macro "state_unfold_loop" : tactic =>
  `(tactic|
    first
      | exact StateRelMonad.whileb_unfold _ _
      | exact StateRelMonad.whileretb_unfold _ _ _
      | exact StateRelMonad.while_unfold _ _
      | exact StateRelMonad.whileret_unfold _ _
      | exact StateRelMonad.Repeat_unfold _
      | exact StateRelMonad.repeat_break_unfold _
      | exact StateRelMonad.repeat_break_noin_unfold _
      | exact StateRelMonad.forset_unfold _ _
      | rw [StateRelMonad.whileb_unfold_eq]
      | rw [StateRelMonad.whileretb_unfold_eq]
      | rw [StateRelMonad.while_unfold_eq]
      | rw [StateRelMonad.whileret_unfold_eq]
      | rw [StateRelMonad.Repeat_unfold_eq]
      | rw [StateRelMonad.repeat_break_unfold_eq]
      | rw [StateRelMonad.repeat_break_noin_unfold_eq]
      | rw [StateRelMonad.forset_unfold_eq]
      | skip)

macro "state_unfold_loop" " in " loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic|
    first
      | rw [StateRelMonad.whileb_unfold_eq] at $loc
      | rw [StateRelMonad.whileretb_unfold_eq] at $loc
      | rw [StateRelMonad.while_unfold_eq] at $loc
      | rw [StateRelMonad.whileret_unfold_eq] at $loc
      | rw [StateRelMonad.Repeat_unfold_eq] at $loc
      | rw [StateRelMonad.repeat_break_unfold_eq] at $loc
      | rw [StateRelMonad.repeat_break_noin_unfold_eq] at $loc
      | rw [StateRelMonad.forset_unfold_eq] at $loc
      | skip)

end MonadLib.StateRelMonad
