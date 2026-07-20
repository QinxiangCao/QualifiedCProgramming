Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
From MonadLib Require Import StateRelBasic StateRelHoare.
From FP Require Import SetsFixedpoints.
Require Import Coq.Classes.Morphisms.
Require Import CommonTactics.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section Ghost.

Context {Σ: Type} (* program state type *)
        {G: Type} (* ghost stated type *).

(* program with ghost state *)
Notation programG  := (program (Σ * G)).

(* lift a program to programG *)          
Definition liftG {A: Type} (p: program Σ A): programG A :=
  fun '(s1, g1) a '(s2, g2) =>
    p s1 a s2 /\ g2 = g1.

Lemma liftG_bind {A B: Type} (c1: program Σ A) (c2: A -> program Σ B):
  liftG (bind c1 c2) == bind (liftG c1) (fun x => liftG (c2 x)).
Proof.
  unfold_monad.
  sets_unfold.
  intros (s0, g) b (s1, g1).
  unfold liftG; split; intros.
  - destruct H as (H & ?); subst.
    destruct H as [a [s2 [H1 H2]]].
    exists a. 
    exists (s2, g).
    tauto.
  - destruct H as [a [[s2 g2] H]].
    destruct H as ((H0 & H1) & H2 & H3).
    subst.
    split; auto.
    exists a; exists s2.
    tauto.
Qed.

Lemma liftG_choice {A: Type} (c1: program Σ A) (c2: program Σ A):
  liftG (choice c1 c2) == choice (liftG c1) (liftG c2).
Proof.
  unfold choice, liftG; sets_unfold.
  intros; tauto.
Qed.

(* ghost update *)
Definition Gupdate (f: Σ -> G -> G -> Prop) : programG unit :=
  fun '(s1, g1) _ '(s2, g2) =>
    s1 = s2 /\ f s1 g1 g2.

Definition Gupdate_live (f: Σ -> G -> G -> Prop) : Prop :=
  forall s g1, exists g2, f s g1 g2.

(* Gequiv: ghost equivalence *)

(** Consider substitute f with Σ -> program G unit *)

(* c' is truly the same program with c except additional ghost state and ghost code *)
Definition Gequiv {A:Type} (c: program Σ A) (c': programG A) :=
  forall s1 a s2 g1,
    (s1, a, s2) ∈ c  <-> (exists g2, ((s1, g1), a, (s2, g2)) ∈ c').

Lemma Gequiv_proequiv {A: Type} (c0 c1: program Σ A) (c0' c1': programG A):
  c0 == c1 ->
  c0' == c1' ->
  Gequiv c0 c0' <-> Gequiv c1 c1'.
Proof.
  unfold Gequiv; intros.
  split; intros.
  - rewrite <- H; split.
    + rewrite H1 with (g1:=g1).
      intros [g2 ?].
      rewrite H0 in H2.
      eexists; eauto.
    + intros [g2 ?].
      rewrite H1 with (g1:=g1).
      exists g2.
      rewrite H0; auto.
  - rewrite H; split.
    + rewrite H1 with (g1:=g1).
      intros [g2 ?].
      exists g2; rewrite H0; auto.
    + intros [g2 ?].
      rewrite H1 with (g1:=g1).
      exists g2.
      rewrite <- H0; auto.
Qed.

#[export] Instance Gequiv_equiv_iff_Proper {A: Type}:
  Proper (Sets.equiv ==> Sets.equiv ==> iff) (@Gequiv A).
Proof.
  unfold Proper, respectful.
  intros.
  apply Gequiv_proequiv; auto.
Qed.

(** Gequiv rules *)

Lemma Gequiv_liftG {A: Type} (c: program Σ A):
  Gequiv c (liftG c).
Proof.
  unfold Gequiv, liftG; sets_unfold; intros.
  split; intros.
  - exists g1; auto.
  - destruct H as [g2 H]; tauto.
Qed.

Lemma Gequiv_ret {A: Type} (a: A):
  Gequiv (ret a) (ret a).
Proof.
  unfold Gequiv; unfold_monad; sets_unfold.
  intros s1 b s2 g1.
  split; intros H.
  - destruct H; exists g1; subst; auto.
  - destruct H as [? [? ?]].
    inversion H0; subst; auto.
Qed.

Lemma Gequiv_bind {A B: Type} (c1: program Σ A) (c2: A -> program Σ B)
  (c1': programG A) (c2': A -> programG B):
  Gequiv c1 c1' ->
  (forall a, Gequiv (c2 a) (c2' a)) ->
  Gequiv (bind c1 c2) (bind c1' c2').
Proof.
  unfold Gequiv; unfold_monad; sets_unfold. 
  intros Hc1 Hc2 s1 b s2 g1.
  split; intros H.
  - destruct H as [a [s3 [H1 H2]]].
    apply Hc1 with (g1:=g1) in H1.
    destruct H1 as [g2 H1].
    apply Hc2 with (g1:=g2) in H2.
    destruct H2 as [g3 H2].
    exists g3, a, (s3, g2).
    tauto.
  - destruct H as [g2 [a [(s3, g3) [H1 H2]]]].
    exists a, s3.
    split.
    eapply Hc1; eexists; eauto.
    eapply Hc2; eexists; eauto.
Qed.

Lemma Gequiv_Gupdate (f: Σ -> G -> G -> Prop):
  (Gupdate_live f) ->
  Gequiv (ret tt) (Gupdate f).
Proof.
  unfold Gequiv, Gupdate_live; unfold_monad; sets_unfold; intros.
  destruct a.
  specialize (H s1 g1).
  destruct H as [g2 H].
  split; unfold Gupdate; intros.
  - exists g2; tauto.
  - destruct H0; tauto.
Qed.

Lemma ret_tt_l {A: Type} (c: program Σ A):
  c == ret tt;; c.
Proof.
  unfold_monad; sets_unfold.
  intros s0 a s1; split.
  - exists tt; exists s0; auto.
  - intros [t [s2 [[? ?] ?]]].
    subst; auto.
Qed.

Lemma ret_tt_r (c: program Σ unit):
  c == c;; ret tt.
Proof.
  unfold_monad; sets_unfold.
  intros s0 a s1; destruct a;split.
  - exists tt; exists s1; auto.
  - intros [t [s2 (? & ? & ?)]].
    destruct t.
    subst; auto.
Qed.

Lemma Gequiv_Gupdate_l {A: Type} (c: program Σ A) (c': programG A)
  (f: Σ -> G -> G -> Prop):
  Gequiv c c' ->
  (Gupdate_live f) ->
  Gequiv c (Gupdate f;; c').
Proof.
  intros.
  rewrite ret_tt_l.
  apply Gequiv_bind.
  apply Gequiv_Gupdate; auto.
  auto.
Qed.

Lemma Gequiv_Gupdate_r (c: program Σ unit) (c': programG unit)
  (f: Σ -> G -> G -> Prop):
  Gequiv c c' ->
  (Gupdate_live f) ->
  Gequiv c (c' ;; Gupdate f).
Proof.
  intros.
  rewrite ret_tt_r.
  apply Gequiv_bind; auto.
  intros; apply Gequiv_Gupdate; auto.
Qed.

Lemma Gequiv_choice {A: Type} (c1 c2: program Σ A) (c1' c2': programG A):
  Gequiv c1 c1' ->
  Gequiv c2 c2' ->
  Gequiv (choice c1 c2) (choice c1' c2').
Proof.
  unfold Gequiv, choice; sets_unfold; intros.
  split.
  - intros [? | ?].
    + eapply H in H1.
      destruct H1 as [g2 H1].
      exists g2; left; eauto.
    + eapply H0 in H1.
      destruct H1 as [g2 H1].
      exists g2; right; eauto. 
  - intros [g2 [H1 | H1]].
    + left. rewrite H.
      exists g2; eauto.
    + right. rewrite H0.
      exists g2; eauto.
Qed.

Lemma Gequiv_fix {A B: Type} 
  (f: (A -> program Σ B) -> (A -> program Σ B)) 
  (f': (A -> programG B) -> (A -> programG B)) (a: A):
  (forall W W' a, (forall a, Gequiv (W a) (W' a)) -> Gequiv (f W a) (f' W' a))->
  Gequiv (Lfix f a) (Lfix f' a).
Proof.
  intros.
  unfold Lfix; sets_unfold.
  assert (forall i, Gequiv (Nat.iter i f ∅ a) (Nat.iter i f' ∅ a)).
  2:{
    revert H0; clear H.
    unfold Gequiv; sets_unfold.
    intros H s1 b s2 g1.
    split.
    - intros [i Hi].
      apply H with (g1:=g1) in Hi.
      destruct Hi as [g2 Hi].
      exists g2, i; auto.
    - intros [g2 [i Hi]].
      exists i.
      eapply H.
      exists g2; eauto.  
  }
  intros i; revert a; induction i.
  - intros.
    unfold Gequiv; sets_unfold; simpl.
    split; intros; eauto.
    destruct H0; auto.
  - simpl; intros. 
    apply H; auto.
Qed.

Lemma Gequiv_fix' {B: Type} 
  (f: program Σ B -> program Σ B) 
  (f': programG B -> programG B):
  (forall W W', Gequiv W W' -> Gequiv (f W) (f' W'))->
  Gequiv (Lfix f) (Lfix f').
Proof.
  intros.
  unfold Lfix; sets_unfold.
  assert (forall i, Gequiv (Nat.iter i f ∅) (Nat.iter i f' ∅)).
  2:{
    revert H0; clear H.
    unfold Gequiv; sets_unfold.
    intros H s1 b s2 g1.
    split.
    - intros [i Hi].
      apply H with (g1:=g1) in Hi.
      destruct Hi as [g2 Hi].
      exists g2, i; auto.
    - intros [g2 [i Hi]].
      exists i.
      eapply H.
      exists g2; eauto.  
  }
  induction i.
  - intros.
    unfold Gequiv; sets_unfold; simpl.
    split; intros; eauto.
    destruct H0; auto.
  - simpl; intros. 
    apply H; auto.
Qed.

Lemma Gequiv_get {A: Type} (P: Σ -> A -> Prop) (P': Σ * G -> A -> Prop):
  (forall s g a, P s a <-> P' (s, g) a) ->
  Gequiv (get P) (get P').
Proof.
  unfold Gequiv, get; sets_unfold.
  intros H s a s' g'.
  split; intros H1.
  - destruct H1 as [H1 H2].
    exists g'; split; subst; auto.
    apply H; auto.
  - destruct H1 as [g2 [H1 H2]].
    inversion H2; subst.
    split; auto.
    eapply H; eauto.
Qed.

Lemma Gequiv_range_iter {A: Type}
  (body: Z -> A -> program Σ A) (body': Z -> A -> programG A) (a0: A):
  (forall i a, Gequiv (body i a) (body' i a)) ->
  forall lo hi,
    Gequiv (range_iter lo hi body a0) (range_iter lo hi body' a0).
Proof.
  intros Hbody lo hi.
  assert (Htest: forall P: Prop, Gequiv (@test' Σ P) (@test' (Σ * G) P)).
  {
    intros P.
    unfold Gequiv, test'; sets_unfold; intros s1 [] s2 g1.
    split; intros H.
    - exists g1. destruct H; subst; split; auto.
    - destruct H as [g2 [HP Heq]].
      inversion Heq; subst; split; auto.
  }
  unfold range_iter.
  apply Gequiv_fix.
  intros W W' [i a] HW.
  unfold range_iter_f; simpl.
  apply Gequiv_choice.
  - apply Gequiv_bind.
    + apply Htest.
    + intros _.
      apply Gequiv_bind.
      * apply Hbody.
      * intros a1.
        apply HW.
  - apply Gequiv_bind.
    + apply Htest.
    + intros _.
      apply Gequiv_ret.
Qed.

Lemma liftG_assume_equiv (P: Σ -> Prop):
  liftG (assume P) == assume (fun '(s, _) => P s).
Proof.
  unfold liftG, test; sets_unfold.
  intros (s, g) a (s', g').
  split; intros.
  - destruct H as [[? ?] ?]; subst; tauto.
  - destruct H as [H1 H2]; inversion H2.
    subst; auto.
Qed.

Lemma liftG_assume'_equiv (P: Prop):
  liftG (assume!! P) == assume!! (P).
Proof.
  unfold liftG, test'; sets_unfold.
  intros (s, g) a (s', g').
  split; intros.
  - destruct H as [[? ?] ?]; subst; tauto.
  - destruct H as [H1 H2]; inversion H2.
    subst; auto.
Qed.

Lemma assume_not_let (P: Σ -> Prop):
  assume (fun (x: Σ * G) => ~ (let '(s, g) := x in P s)) == assume (fun '(s, _) => ~ P s).
Proof.
  unfold test; sets_unfold.
  intros (s, g) a (s', g'). tauto.
Qed.

Local Ltac Gequiv_auto :=
  match goal with
  | |- Gequiv _ (Gupdate _;; _) => apply Gequiv_Gupdate_l; [try Gequiv_auto|]
  | |- Gequiv _ (_;; Gupdate _) => apply Gequiv_Gupdate_r; [try Gequiv_auto|]
  | |- Gequiv (bind _ _) (bind _ _) => apply Gequiv_bind; [| intros]; try Gequiv_auto
  | |- Gequiv (choice _ _) (choice _ _) => apply Gequiv_choice; try Gequiv_auto
  | |- Gequiv (Rec _ _) (Rec _ _) => unfold Rec; apply Gequiv_fix; intros; try Gequiv_auto
  | |- Gequiv (Rec _) (Rec _) => unfold Rec; apply Gequiv_fix'; intros; try Gequiv_auto
  | |- Gequiv (Lfix _ _) (Lfix _ _) => apply Gequiv_fix; intros; try Gequiv_auto
  | |- Gequiv (Lfix _) (Lfix _) => apply Gequiv_fix'; intros; try Gequiv_auto
  | |- Gequiv ?c (liftG ?c) => apply Gequiv_liftG
  | |- Gequiv (ret _) (ret _) => apply Gequiv_ret
  | |- Gequiv (match ?x with _ => _ end) _ => destruct x; try Gequiv_auto
  | |- Gequiv (assume _) (assume _) => try rewrite <- liftG_assume_equiv; apply Gequiv_liftG
  | |- Gequiv (assume!! _) (assume!! _) => try rewrite <- liftG_assume'_equiv; apply Gequiv_liftG
  | |- Gequiv _ _ => auto
  end.

Lemma Gequiv_while (c: program Σ unit) (c': programG unit)
  (P: Σ -> Prop):
  Gequiv c c' ->
  Gequiv (whileP P c) (whileP (fun '(s, _) => P s) c').
Proof.
  intros.
  unfold whileP, whileP_f.
  Gequiv_auto.
  eapply Gequiv_proequiv.
  reflexivity.
  2:apply Gequiv_liftG.
  unfold liftG, test; sets_unfold.
  intros (s, g) a (s', g').
  split; intros Hrun.
  - destruct Hrun as [Hnot Heq]; inversion Heq; subst; auto.
  - destruct Hrun as [[Hnot Heq] Hghost]; subst; auto.
Qed.

Lemma Gequiv_repeat_break {A B: Type} 
  (c: A -> program Σ (CntOrBrk A B))
  (c': A -> programG (CntOrBrk A B)) (a: A):
  (forall a, Gequiv (c a) (c' a)) ->
  Gequiv (repeat_break c a) (repeat_break c' a).
Proof.
  intros.
  unfold repeat_break, repeat_break_f.
  Gequiv_auto.
Qed.

Lemma Gequiv_forset {A: Type} (s: A -> Prop) 
  (c: A -> program Σ unit) (c': A -> programG unit):
  (forall a, Gequiv (c a) (c' a)) ->
  Gequiv (forset s c) (forset s c').
Proof.
  intros.
  unfold forset, forset_f.
  Gequiv_auto.
  apply Gequiv_get; tauto.
Qed.

(** Gequiv Hoare *)
Lemma Hoare_toG {A: Type} (c: program Σ A) (c': programG A)
  (P: Σ -> Prop) (Q: A -> Σ -> Prop) (P': Σ * G -> Prop):
  Gequiv c c' ->
  Hoare P c Q ->
  (forall s g, P' (s, g) -> P s) ->
  Hoare P' c' (fun a '(s, g) => Q a s).
Proof.
  unfold Hoare, Gequiv; sets_unfold.
  intros HG Hc HP (s0, g0) a (s1, g1) HP' Hc'.
  eapply Hc.
  eapply HP; eauto.
  eapply HG; eexists; eauto.
Qed.

Lemma Hoare_fromG {A: Type} (c: program Σ A) (c': programG A)
  (P': Σ * G -> Prop) (P: Σ -> Prop) (Q: A -> Σ -> Prop):
  Gequiv c c' ->
  Hoare P' c' (fun a '(s', _) => Q a s') ->
  (forall s, P s -> (exists g, P' (s, g))) ->
  Hoare P c Q.
Proof.
  unfold Gequiv, Hoare; sets_unfold.
  intros.
  apply H1 in H2.
  destruct H2 as [g H2].
  apply H with (g1:=g) in H3.
  destruct H3 as [g2 H3].
  eapply H0 with (s2:=(s2, g2));
  eauto.
Qed.

Lemma Hoare_liftG {A: Type} (c: program Σ A) 
  (P: G -> Σ -> Prop) (Q: G -> A -> Σ -> Prop):
    (forall g, Hoare (P g) c (Q g)) ->
    Hoare (fun '(s, g) => P g s) (liftG c) (fun a '(s, g) => Q g a s).
Proof.
  unfold Gequiv, Hoare, liftG; sets_unfold.
  intros Hc (s0, g0) a (s1, g1) HP' [Hc' ?].
  subst; eapply Hc; eauto.
Qed.

Lemma Hoare_liftG' {A: Type} (c: program Σ A) 
  (P: Σ * G -> Prop) (Q: A -> Σ * G -> Prop):
    (forall g, Hoare (fun s => P (s, g)) c (fun a s => Q a (s, g))) ->
    Hoare P (liftG c) Q.
Proof.
  unfold Gequiv, Hoare, liftG; sets_unfold.
  intros Hc (s0, g0) a (s1, g1) HP' [Hc' ?].
  subst; eapply Hc; eauto.
Qed.

Lemma Hoare_liftG_s {A:Type} (P:A -> Σ -> Prop) (c: program Σ A) (s0:Σ) (g0:G):
    (Hoare (fun s => s = s0) c P) ->
    Hoare (fun x => x = (s0, g0)) (liftG c) (fun a x => exists s1, x = (s1, g0) /\ P a s1).
Proof.
  intros.
  apply Hoare_liftG'; intros.
  apply Hoare_conseq_pre with (P2 := fun s => s = s0 /\ g = g0).
  intros s Hs; inversion Hs; subst; auto.
  stateless_intros; subst.
  hoare_cons H.
  intros a s1 HP.
  exists s1; auto.
Qed.

Lemma Hoare_Gupdate (P: Σ * G -> Prop) (f: Σ -> G -> G -> Prop):
  Hoare P (Gupdate f) (fun _ '(s, g') => exists g, P (s, g) /\ f s g g').
Proof.
  unfold Gupdate.
  eapply Hoare_conseq_post.
  2:apply Hoare_step.
  simpl.
  intros _ (s, g) [(s1, g1) [[? ?] ? ]].
  exists g1; subst; auto.
Qed.

Lemma Hoare_Gupdate_s (P: Σ -> Prop) (f: Σ -> G -> G -> Prop) (s0:Σ) (g0:G):
  Hoare (fun x => x = (s0, g0)) (Gupdate f) (fun _ x => exists g1, x = (s0, g1) /\ f s0 g0 g1).
Proof.
  hoare_cons_post Hoare_Gupdate.
  intros _ (s,g).
  intros [g1 [Hs ?]]; inversion Hs; subst.
  exists g; auto.
Qed.


(** c keeps the ghost-related prop G *)
Definition keepG {A: Type} (P: G -> Prop) (c: programG A)  :=
  Hoare (fun '(_, g) => P g) c (fun _ '(_, g) => P g).

Lemma Hoare_liftG_keepG {A: Type} (P: G -> Prop) (c: program Σ A) :
    Hoare (fun '(_, g) => P g) (liftG c) (fun _ '(_, g) => P g).
Proof.
  apply Hoare_liftG.
  intros; unfold Hoare; tauto.
Qed.

End Ghost.

Ltac intro_state_pair :=
  apply Hoare_state_intro; intros (?, ?) ?.

Ltac hoare_auto_G :=
  unfold If, if_else;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto_G
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto_G
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_left; try hoare_auto_G
    | |- Hoare _ ((liftG _);; _) _ => 
           eapply Hoare_bind; [apply Hoare_liftG_s; hoare_auto_s | ];
           simpl; intros _; apply Hoare_pre_ex; intros; stateless_intros; 
           try subst; try hoare_auto_G
    | |- Hoare _ (bind (liftG _) _) _ =>
           eapply Hoare_bind; [apply Hoare_liftG_s; hoare_auto_s | ];
           simpl; intros; apply Hoare_pre_ex; intros; stateless_intros; 
           try subst; try hoare_auto_G
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_auto_G
    | |- Hoare _ (ret _) _ => apply Hoare_ret'; intros 
    | |- Hoare _ (liftG _) _ => hoare_cons_post Hoare_liftG_s; [simpl | hoare_auto_s_disj]
  end; auto.

Ltac Gequiv_auto :=
  unfold continue, break, If, if_else;
  match goal with
  | |- Gequiv _ (Gupdate _;; _) => apply Gequiv_Gupdate_l; [try Gequiv_auto|]
  | |- Gequiv _ (_;; Gupdate _) => apply Gequiv_Gupdate_r; [try Gequiv_auto|]
  | |- Gequiv (bind _ _) (bind _ _) => apply Gequiv_bind; [| intros]; try Gequiv_auto
  | |- Gequiv (choice _ _) (choice _ _) => apply Gequiv_choice; try Gequiv_auto
  | |- Gequiv (Rec _ _) (Rec _ _) => unfold Rec; apply Gequiv_fix; intros; try Gequiv_auto
  | |- Gequiv (Rec _) (Rec _) => unfold Rec; apply Gequiv_fix'; intros; try Gequiv_auto
  | |- Gequiv (Lfix _ _) (Lfix _ _) => apply Gequiv_fix; intros; try Gequiv_auto
  | |- Gequiv (Lfix _) (Lfix _) => apply Gequiv_fix'; intros; try Gequiv_auto
  | |- Gequiv (whileP _ _) (whileP _ _) => apply Gequiv_while; intros; try Gequiv_auto
  | |- Gequiv (repeat_break _ _) (repeat_break _ _) => apply Gequiv_repeat_break; intros; 
      try Gequiv_auto
  | |- Gequiv (forset _ _) (forset _ _) => apply Gequiv_forset; intros; try Gequiv_auto
  | |- Gequiv ?c (liftG ?c) => apply Gequiv_liftG
  | |- Gequiv (ret _) (ret _) => apply Gequiv_ret
  | |- Gequiv (match ?x with _ => _ end) _ => destruct x; try Gequiv_auto
  | |- Gequiv (assume _) (assume _) => try rewrite assume_not_let; try rewrite <- liftG_assume_equiv; 
      apply Gequiv_liftG
  | |- Gequiv (assume!! _) (assume!! _) => try rewrite <- liftG_assume'_equiv; apply Gequiv_liftG
  | |- Gequiv _ _ => auto
  end.

Declare Scope ghost_scope.
Delimit Scope ghost_scope with ghost.
Notation "↑ c" := (liftG c) (at level 5): ghost_scope.
Notation programG Σ G := (program (Σ * G)) (only parsing).
