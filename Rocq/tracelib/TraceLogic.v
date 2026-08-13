Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Logic.Classical_Prop.
Local Open Scope list_scope.
Import ListNotations.

Local Theorem cons_eq_singleton_app {X: Type}: forall (x: X)(l: list X),
  x :: l = [x] ++ l.
Proof. induction l; firstorder. Qed.

Local Ltac split_r n :=
  match n with
  | O => idtac
  | S ?n' => split; [|split_r n']
  end.

Section TraceConnectives.
Context {TR: Type}.

Definition trace_and (P Q: TR -> nat -> Prop): TR -> nat -> Prop :=
  fun tr i => P tr i /\ Q tr i.

Definition trace_implies (P Q: TR -> nat -> Prop): TR -> nat -> Prop :=
  fun tr i => P tr i -> Q tr i.

End TraceConnectives.

Section TraceLogic.
Context {Σ: Type}
        {T: Type}.

Definition Atom := (T * Σ) -> Prop.
(* only specify tag *)
Definition tAtom (t: T) : Atom := fun '(t', _) => t = t'.
Coercion tAtom : T >-> Atom.
(* only specify state *)
Definition sAtom (P: Σ -> Prop) : Atom := fun '(_, s) => P s.
(* specify both *)
Definition tsAtom (t: T) (P: Σ -> Prop) : Atom := fun '(t', s) => t = t' /\ P s.

(* operators *)
(** 1-indexed to deal with nil *)
Definition lift (A: Atom): list (T * Σ) -> nat -> Prop := 
  fun tr i => match nth_error tr (i-1) with
    | Some t => A t
    | None => False
  end.
Coercion lift: Atom >-> Funclass.

(* temporal operators *)
Definition alw (P: list (T * Σ) -> nat -> Prop): list (T * Σ) -> nat -> Prop :=
  fun tr i => forall j, 1 <= j <= i -> P tr j.
Definition have (P: list (T * Σ) -> nat -> Prop): list (T * Σ) -> nat -> Prop :=
  fun tr i => exists j, 1 <= j <= i /\ P tr j.

Definition implies (P Q: list (T * Σ) -> nat -> Prop): list (T * Σ) -> nat -> Prop :=
  trace_implies P Q.

Definition both (P Q: list (T * Σ) -> nat -> Prop): list (T * Σ) -> nat -> Prop :=
  trace_and P Q.

Definition last_satisfy (P: list (T * Σ) -> nat -> Prop): list (T * Σ) -> Prop :=
	fun tr => P tr (length tr).

Definition have_first (P: list (T * Σ) -> nat -> Prop): list (T * Σ) -> nat -> Prop :=
    fun tr i => exists j, 1 <= j <= i /\ P tr j /\ (forall k, 1 <= k < j -> ~ P tr k).
Definition have_once (P: list (T * Σ) -> nat -> Prop): list (T * Σ) -> nat -> Prop :=
    fun tr i => exists ! j, 1 <= j <= i /\ P tr j.
(* P occurs before Q *)
(* 可以同时发生 *)
Definition before_eq (P: list (T * Σ) -> nat -> Prop) (Q: list (T * Σ) -> nat -> Prop): 
  list (T * Σ) -> nat -> Prop := 
  fun tr i => exists j, 1 <= j <= i /\ P tr j /\ (forall k, 1 <= k <= j -> ~ Q tr k).
(* P一定发生，Q可以不发生*)
Definition before (P: list (T * Σ) -> nat -> Prop) (Q: list (T * Σ) -> nat -> Prop): 
  list (T * Σ) -> nat -> Prop := 
  fun tr i => exists j, 1 <= j <= i /\ P tr j /\ (forall k, 1 <= k < j -> ~ Q tr k).
(* 可以P, Q同时不发生 *)
Definition before_weak (P: list (T * Σ) -> nat -> Prop) (Q: list (T * Σ) -> nat -> Prop): 
  list (T * Σ) -> nat -> Prop := 
  fun tr i => before P Q tr i \/ (~ have Q tr i).
(* P, Q同时发生*)
Definition have_both (P: list (T * Σ) -> nat -> Prop) (Q: list (T * Σ) -> nat -> Prop): 
  list (T * Σ) -> nat -> Prop := 
  fun tr i => exists j, 1 <= j <= i /\ P tr j /\ Q tr j.


(** Tradeoff between the definition of last_satisfy, alw, have and lift *)
End TraceLogic.

Section StateTraceLogic.
Context {Σ: Type}.

Definition SAtom := Σ -> Prop.

Definition sLift (A: SAtom): list Σ -> nat -> Prop :=
  fun tr i => match nth_error tr (i - 1) with
    | Some s => A s
    | None => False
  end.
Coercion sLift: SAtom >-> Funclass.

Definition alwS (P: list Σ -> nat -> Prop): list Σ -> nat -> Prop :=
  fun tr i => forall j, 1 <= j <= i -> P tr j.
Definition haveS (P: list Σ -> nat -> Prop): list Σ -> nat -> Prop :=
  fun tr i => exists j, 1 <= j <= i /\ P tr j.

Definition impliesS (P Q: list Σ -> nat -> Prop): list Σ -> nat -> Prop :=
  trace_implies P Q.

Definition bothS (P Q: list Σ -> nat -> Prop): list Σ -> nat -> Prop :=
  trace_and P Q.

Definition last_satisfyS (P: list Σ -> nat -> Prop): list Σ -> Prop :=
  fun tr => P tr (length tr).

Definition have_firstS (P: list Σ -> nat -> Prop): list Σ -> nat -> Prop :=
  fun tr i => exists j, 1 <= j <= i /\ P tr j /\ (forall k, 1 <= k < j -> ~ P tr k).
Definition have_onceS (P: list Σ -> nat -> Prop): list Σ -> nat -> Prop :=
  fun tr i => exists ! j, 1 <= j <= i /\ P tr j.

End StateTraceLogic.

Declare Scope trace_scope.
Delimit Scope trace_scope with trace.
Notation "'t↑' T" := (tAtom T) (at level 10) : trace_scope.
Notation "'s↑' P" := (sAtom P) (at level 10) : trace_scope.
Notation "'ts↑' P" := (tsAtom P) (at level 10) : trace_scope.
Notation "'S↑' P" := (sLift P) (at level 10) : trace_scope.
Notation "P 't/\\' Q" := (both P Q) (at level 40, left associativity): trace_scope.
Notation "P 's/\\' Q" := (bothS P Q) (at level 40, left associativity): trace_scope.
Notation "P 't->' Q" := (implies P Q) (at level 61): trace_scope.
Notation "P 's->' Q" := (impliesS P Q) (at level 61): trace_scope.
Notation "↑ P" := (lift P) (at level 5) : trace_scope.
Notation "l '|=' P" := (last_satisfy P l) (at level 99) : trace_scope.
Notation "l '|=S' P" := (last_satisfyS P l) (at level 99) : trace_scope.

Local Open Scope trace_scope.

Section StateTraceRule.
Context {Σ: Type}.

Local Definition STR := list Σ.

Lemma singleton_haveS_atom (a: SAtom) (x: Σ):
  (x :: nil |=S haveS (S↑ a)) <-> a x.
Proof.
  unfold last_satisfyS, haveS, sLift.
  split.
  - intros [j [Hj HP]].
    simpl in Hj.
    replace (j - 1) with 0 in HP by lia.
    exact HP.
  - intros H.
    exists 1.
    simpl.
    auto.
Qed.

Lemma singleton_alwS_atom (a: SAtom) (x: Σ):
  (x :: nil |=S alwS (S↑ a)) <-> a x.
Proof.
  unfold last_satisfyS, alwS, sLift.
  split.
  - intros H.
    specialize (H 1).
    simpl in H.
    auto.
  - intros H.
    simpl.
    intros j Hj.
    replace (j - 1) with 0 by lia.
    simpl.
    auto.
Qed.

Lemma nil_alwS (P: STR -> nat -> Prop):
  nil |=S alwS P.
Proof.
  unfold last_satisfyS, alwS; simpl; lia.
Qed.

Lemma not_nil_haveS (P: STR -> nat -> Prop):
  ~(nil |=S haveS P).
Proof.
  unfold last_satisfyS, haveS.
  simpl.
  intros [j [H _]].
  lia.
Qed.

Lemma app_lastS_atom (tr: STR) (x: Σ) (a: SAtom):
  (tr ++ x :: nil |=S S↑ a) <-> a x.
Proof.
  unfold last_satisfyS, sLift.
  rewrite length_app.
  simpl.
  rewrite nth_error_app2 by lia.
  replace (length tr + 1 - 1 - length tr) with 0 by lia.
  simpl.
  easy.
Qed.

Lemma lastS_atom_implies (tr: STR) (a0 a1: SAtom):
  (forall x, a0 x -> a1 x) ->
  tr |=S S↑ a0 ->
  tr |=S S↑ a1.
Proof.
  unfold last_satisfyS, sLift.
  intros Himpl Hlast.
  destruct (nth_error tr (length tr - 1)); auto.
Qed.

Lemma last_haveS_atom (tr: STR) (a: SAtom):
  tr |=S S↑ a ->
  tr |=S haveS (S↑ a).
Proof.
  unfold haveS, last_satisfyS, sLift.
  intros H.
  destruct tr.
  - simpl in H. tauto.
  - simpl in *.
    replace (length tr - 0) with (S (length tr) - 1) in H by lia.
    exists (S (length tr)).
    split; [lia | exact H].
Qed.

Lemma haveS_atom_conseq (tr: STR) (a0 a1: SAtom):
  (forall x, a0 x -> a1 x) ->
  tr |=S haveS (S↑ a0) ->
  tr |=S haveS (S↑ a1).
Proof.
  unfold haveS, last_satisfyS, sLift.
  intros Himpl [j [Hj HP]].
  exists j.
  split; [exact Hj |].
  destruct (nth_error tr (j - 1)); auto.
Qed.

Lemma app_haveS_atom (tr1 tr2: STR) (a: SAtom):
  (tr1 ++ tr2 |=S haveS (S↑ a)) <->
  (tr1 |=S haveS (S↑ a)) \/ (tr2 |=S haveS (S↑ a)).
Proof.
  unfold last_satisfyS, haveS, sLift.
  split.
  - intros [j [Hj HP]].
    rewrite length_app in Hj.
    destruct (le_gt_dec j (length tr1)).
    + left.
      exists j.
      rewrite nth_error_app1 in HP by lia.
      split; [lia | exact HP].
    + right.
      exists (j - length tr1).
      rewrite nth_error_app2 in HP by lia.
      replace (j - length tr1 - 1) with (j - 1 - length tr1) by lia.
      split; [lia | exact HP].
  - rewrite length_app.
    intros [[j [Hj Ht]] | [j [Hj Ht]]].
    + exists j.
      rewrite nth_error_app1 by lia.
      split; [lia | exact Ht].
    + exists (j + length tr1).
      split; [lia |].
      rewrite nth_error_app2 by lia.
      replace (j + length tr1 - 1 - length tr1) with (j - 1) by lia.
      exact Ht.
Qed.

Lemma app_last_haveS_atom (tr: STR) (x: Σ) (a: SAtom):
  a x -> (tr ++ x :: nil |=S haveS (S↑ a)).
Proof.
  intros H.
  apply last_haveS_atom.
  apply app_lastS_atom.
  exact H.
Qed.

Lemma haveS_app_l (tr1 tr2: STR) (a: SAtom):
  tr1 |=S haveS (S↑ a) ->
  tr1 ++ tr2 |=S haveS (S↑ a).
Proof.
  intros H.
  apply app_haveS_atom.
  left.
  exact H.
Qed.

Lemma haveS_app_r (tr1 tr2: STR) (a: SAtom):
  tr2 |=S haveS (S↑ a) ->
  tr1 ++ tr2 |=S haveS (S↑ a).
Proof.
  intros H.
  apply app_haveS_atom.
  right.
  exact H.
Qed.

Lemma haveS_app_single_inv (tr: STR) (x: Σ) (a: SAtom):
  tr ++ x :: nil |=S haveS (S↑ a) ->
  (tr |=S haveS (S↑ a)) \/ a x.
Proof.
  intros H.
  apply app_haveS_atom in H.
  destruct H as [H | H].
  - left. exact H.
  - right.
    apply singleton_haveS_atom.
    exact H.
Qed.

Lemma nth_error_last_nonempty {A: Type} (l: list A) (d: A):
  l <> nil ->
  nth_error l (length l - 1) = Some (last l d).
Proof.
  induction l as [|a l IH]; intros Hnn.
  - contradiction.
  - destruct l as [|b l'].
    + simpl. reflexivity.
    + destruct l' as [|c l''].
      * simpl. reflexivity.
      * simpl.
        apply IH.
        discriminate.
Qed.

Lemma nth_lastS_nonempty (l: STR) (d: Σ):
  l <> nil ->
  nth (length l - 1) l d = last l d.
Proof.
  intros Hnn.
  pose proof (nth_error_last_nonempty l d Hnn) as Hnth.
  apply nth_error_nth with (d := d) in Hnth.
  exact Hnth.
Qed.

Lemma last_state_satisfy (tr: STR) (d: Σ) (P: Σ -> Prop):
  tr <> nil ->
  P (last tr d) ->
  tr |=S S↑ P.
Proof.
  intros Hnn HP.
  unfold last_satisfyS, sLift.
  rewrite nth_error_last_nonempty with (d := d) by exact Hnn.
  exact HP.
Qed.

Lemma haveS_exists_nth (tr: STR) (P: Σ -> Prop) (d: Σ):
  tr |=S haveS (S↑ P) ->
  exists i, i < length tr /\ P (nth i tr d).
Proof.
  unfold last_satisfyS, haveS, sLift.
  intros [j [[Hjlo Hjhi] HP]].
  exists (j - 1).
  split; [lia |].
  destruct (nth_error tr (j - 1)) as [x |] eqn:Hnth.
  - apply nth_error_nth with (d := d) in Hnth.
    rewrite Hnth.
    exact HP.
  - contradiction.
Qed.

Lemma nth_haveS (tr: STR) (P: Σ -> Prop) (d: Σ) i:
  i < length tr ->
  P (nth i tr d) ->
  tr |=S haveS (S↑ P).
Proof.
  intros Hi HP.
  unfold last_satisfyS, haveS, sLift.
  exists (S i).
  split; [lia |].
  replace (S i - 1) with i by lia.
  rewrite nth_error_nth' with (d := d) by lia.
  exact HP.
Qed.

End StateTraceRule.

Section TraceRule.
Context {Σ: Type}
        {T: Type}.

Local Definition TR := list (T * Σ).

Lemma singleton_have_atom (a: Atom) (x: T * Σ):
  ( x::nil |= have ↑a) <-> a x.
Proof.
  unfold last_satisfy, have, lift.
  split.
  - intros [j [Hj HP]].
    simpl in Hj; replace (j-1) with 0 in HP by lia; auto.
  - intros H.
    exists 1. simpl; auto.
Qed.

Lemma singleton_alw_atom (a: Atom) (x: T * Σ):
  ( x::nil |= alw ↑a) <-> a x.
Proof.
  unfold last_satisfy, alw, lift.
  split.
  - intros H.
    specialize (H 1); simpl in H.
    auto.
  - intros H.
    simpl; intros j Hj.
    replace (j - 1) with 0 by lia.
    simpl; auto.
Qed.

Lemma nil_alw (P: TR -> nat -> Prop):
  nil |= alw P.
Proof.
  unfold last_satisfy, alw; simpl; lia.
Qed.

Lemma not_nil_have (P: TR -> nat -> Prop):
  ~(nil |= have P).
Proof.
  unfold last_satisfy, have.
  simpl; intros [j [H _]]; lia.
Qed.

Lemma app_last_atom (tr: TR) (x: T * Σ) (a: Atom):
  (tr ++ x::nil |= ↑a) <-> a x.
Proof.
  unfold last_satisfy, lift, tsAtom.
  subst; rewrite length_app; simpl.
  rewrite nth_error_app2 by lia.
  replace (length tr + 1 - 1 - length tr) with 0 by lia.
  simpl; easy.
Qed.

Lemma last_atom_implies (tr: TR) (a0 a1: Atom):
  (forall x, a0 x -> a1 x) ->
  tr |= a0 ->
  tr |= a1.
Proof.
  unfold last_satisfy, lift; intros.
  destruct (nth_error tr (length tr - 1)); auto.
Qed.
  
Lemma last_have_atom (tr: TR) (a: Atom):
  tr |= a ->
  tr |= have a.
Proof.
  unfold have, last_satisfy, lift; intros.
  destruct tr.
  simpl in H; tauto.
  simpl in *; replace (length tr - 0) with (S(length tr) - 1) in H by lia.
  exists (S (length tr)); split; [lia | auto].
Qed.

Lemma have_atom_conseq (tr: TR) (a0 a1: Atom):
  (forall x, a0 x -> a1 x) ->
  tr |= have a0 ->
  tr |= have a1.
Proof.
  unfold have, last_satisfy, lift; intros.
  destruct H0 as [j [Hj HP]].
  exists j; split; auto.
  destruct (nth_error tr (j - 1)); auto.
Qed.

Lemma have_tsatom_conseq (tr: TR) (a: T) (P Q: Σ -> Prop):
  (forall s, P s -> Q s) ->
  tr |= have (ts↑ a P) ->
  tr |= have (ts↑ a Q).
Proof.
  unfold have, last_satisfy, lift, tsAtom; intros.
  destruct H0 as [j [Hj HP]].
  exists j; split; auto.
  destruct (nth_error tr (j - 1)); auto.
  destruct p; firstorder.
Qed.

Lemma app_have_atom (tr1 tr2: TR) (a: Atom):
  (tr1 ++ tr2 |= have ↑a) <-> (tr1 |= have ↑a) \/ (tr2 |= have ↑a).
Proof.
  unfold last_satisfy, have, lift. 
  split.
  - intros [j [Hj HP]].
    rewrite length_app in Hj.
    destruct (le_gt_dec j (length tr1)).
    + left; exists j.
      rewrite nth_error_app1 in HP by lia.
      split; [lia | auto].
    + right; exists (j - length tr1).
      rewrite nth_error_app2 in HP by lia.
      replace (j - length tr1 - 1) with (j - 1 -length tr1) by lia.
      split; [lia | auto].
  - rewrite length_app. 
    intros [[j [Hj Ht]] | [j [Hj Ht]]].
    + exists j.
      rewrite nth_error_app1 by lia.
      split; [lia | auto].
    + exists (j + length tr1).
      split; [lia |].
      rewrite nth_error_app2 by lia.
      replace (j + length tr1 - 1 - length tr1) with (j-1) by lia.
      auto.
Qed.

Lemma app_alw_atom (tr1 tr2: TR) (a: Atom):
  (tr1 ++ tr2 |= alw ↑a) <-> (tr1 |= alw ↑a) /\ (tr2 |= alw ↑a).
Proof.
  unfold last_satisfy, alw, lift.
  rewrite length_app.
  split.
  - intros H; split; intros.
    + specialize (H j).
      rewrite nth_error_app1 in H by lia.
      apply H; lia.
    + specialize (H (j + length tr1)).
      rewrite nth_error_app2 in H by lia.
      replace (j + length tr1 - 1 - length tr1) with (j-1) in H by lia.
      apply H; lia. 
  - intros [H1  H2]; intros.
    destruct (le_gt_dec j (length tr1)).
    * rewrite nth_error_app1 by lia.
      apply H1; lia.
    * rewrite nth_error_app2 by lia.
      replace (j - 1 - length tr1) with (j - length tr1 - 1) by lia.
      apply H2; lia.
Qed.

Lemma app_last_have_atom (tr: TR) (x: T * Σ) (a: Atom):
  a x -> (tr ++ x::nil |= have ↑a).
Proof.
  intros; destruct tr. 
  apply singleton_have_atom; auto. 
  exists (length tr + 2); split.
  rewrite length_app; simpl; lia.
  induction tr; simpl.
  unfold lift; simpl; auto.
  unfold lift in *. 
  rewrite cons_eq_singleton_app.
  rewrite nth_error_app2.
  2: {simpl; try lia. }
  rewrite cons_eq_singleton_app in *.
  rewrite <- app_assoc in IHtr.
  rewrite nth_error_app2 in *; try (simpl; lia).
  simpl in *; rewrite Nat.sub_0_r; auto.
Qed.

Lemma have_tsatom_tatom (tr: TR) (a: T) (b: Σ -> Prop):
  tr |= have (ts↑ a b) -> tr |= have (t↑ a).
Proof.
  unfold last_satisfy, have, lift, tsAtom, tAtom.
  intros.
  destruct H as [n []].
  exists n; split; auto. 
  destruct (nth_error tr (n - 1)); [destruct p|]; tauto.
Qed.

Lemma have_tsatom_satom (tr: TR) (a: T) (b: Σ -> Prop):
  tr |= have (ts↑ a b) -> tr |= have (s↑ b).
Proof.
  unfold last_satisfy, have, lift, tsAtom, sAtom.
  intros.
  destruct H as [n []].
  exists n; split; auto.
  destruct (nth_error tr (n - 1)); [destruct p|]; tauto.
Qed.

Lemma have_implies_have_first (tr: TR) (a: Atom): 
  tr |= have ↑a -> tr |= have_first ↑a. 
Proof.
  induction tr.
  - intros; exfalso; eapply not_nil_have; eauto.
  - intros. rewrite cons_eq_singleton_app in *.
    apply app_have_atom in H as [].
    * rewrite singleton_have_atom in H.
      exists 1; simpl; repeat split; try lia.
      unfold lift; simpl; auto.
    * destruct (classic (a a0)).
      {
        exists 1; simpl; repeat split; try lia.
        unfold lift; simpl; auto.
      }
      {
        apply IHtr in H as [n [? []]].
        exists (S n); simpl; repeat split; try lia.
        * unfold lift in H1; unfold lift; simpl in *. 
          rewrite cons_eq_singleton_app.
          rewrite nth_error_app2; simpl; try lia. 
          rewrite Nat.sub_0_r; auto.
        * intros. unfold lift.
          destruct (classic (k = 1)).
          subst; simpl; auto.
          rewrite cons_eq_singleton_app.
          rewrite nth_error_app2; simpl; try lia.
          apply H2; lia. 
      }
Qed.


Lemma before_exclude_middle (tr: TR) (a b: Atom): 
  (tr |= have ↑a) -> (tr |= have ↑b) -> 
  (tr |= before ↑a ↑b) \/ (tr |= before ↑b ↑a).
Proof.
  unfold last. 
  intros.
  apply have_implies_have_first in H, H0.
  destruct H as [n [?[]]].
  destruct H0 as [m [?[]]].
  destruct (Nat.le_ge_cases n m).
  - left; exists n; repeat split; try lia; auto.
    intros; apply H4; lia.
  - right; exists m; repeat split; try lia; auto.
    intros; apply H2; lia.
Qed.

Lemma before_eq_exclude_middle (tr: TR) (a b: Atom): 
  (tr |= have ↑a) -> (tr |= have ↑b) -> 
  (tr |= before_eq ↑a ↑b) \/ (tr |= before_eq ↑b ↑a) \/ (tr |= have_both ↑a ↑b).
Proof.
  unfold last. 
  intros.
  apply have_implies_have_first in H, H0.
  destruct H as [n [?[]]].
  destruct H0 as [m [?[]]].
  destruct (Nat.le_gt_cases n m); [apply Nat.lt_eq_cases in H5 as []|].
  - left; exists n; repeat split; try lia; auto.
    intros; apply H4; lia.
  - right; right; subst.
    exists m; auto.
  - right; left; exists m; repeat split; try lia; auto.
    intros; apply H2; lia.
Qed. 

Lemma not_nil_before (a b: Atom):
  ~ (@nil (T * Σ) |= before ↑a ↑b ).
Proof.
  unfold not; intros.
  destruct H as [n []].
  simpl in H; lia.
Qed.

Lemma not_nil_before_eq (a b: Atom):
  ~ (@nil (T * Σ) |= before_eq ↑a ↑b ).
Proof.
  unfold not; intros.
  destruct H as [n []].
  simpl in H; lia.
Qed.

Lemma have_not_before (tr: TR) (a b: Atom):
  tr |= have ↑a ->
  ~ (tr |= have ↑ b) ->
  tr |= before ↑a ↑b.
Proof.
  intros.
  destruct H as [n []].
  exists n; split_r 2; try lia; auto.
  intros; unfold have, last_satisfy, lift in *. 
  unfold not; intros; apply H0.
  exists k; split; try lia; auto.
Qed.

Lemma before_app (tr1 tr2: TR) (a b: Atom): 
  tr1 |= before ↑a ↑b -> 
  tr1 ++ tr2 |= before ↑a ↑b.
Proof.
  intros.
  destruct H as [n [? []]].
  exists n; split_r 2.
  * rewrite length_app; lia.
  * unfold lift in *. rewrite nth_error_app1; try lia; auto. 
  * intros; apply H1 in H2 as Hb.
    unfold lift; rewrite nth_error_app1; try lia; auto. 
Qed.

Lemma before_weak_app (tr1 tr2: TR) (a b: Atom): 
  tr1  |= before_weak ↑a ↑b -> 
  ~ (tr2 |= have ↑ b) ->
  tr1 ++ tr2 |= before_weak ↑a ↑b.
Proof.
  intros.
  destruct H.
  * left; apply before_app; auto.
  * right; unfold not; intros; unfold have, lift in *.
    destruct H1 as [n []]. 
    destruct (le_gt_dec n (length tr1)).
    ** rewrite nth_error_app1 in H2; try lia; auto. 
       apply H; eexists; split; eauto; lia.
    ** rewrite nth_error_app2 in H2; try lia.
       replace (n - 1 - length tr1) with (n - length tr1 - 1) in H2 by lia.
       apply H0; rewrite length_app in H1.
       exists (n - length tr1); split; try lia; auto.
Qed.

Lemma singleton_have_once (x: T * Σ) (a: Atom):
  (x::nil |= have_once ↑a) <-> a x.
Proof.
  unfold have_once, lift; split.
  * intros [n [[]]].
    simpl in H.
    assert (n = 1) by lia; subst.
    replace (1 - 1) with 0 in H0 by lia; auto.
  * intros. exists 1; split; [split|].
    ** simpl; lia.
    ** simpl; auto.
    ** intros m []; simpl in *; lia.
Qed.

Lemma have_once_implies_have (tr: TR) (a: Atom):
  tr |= have_once ↑a ->
  tr |= have ↑a.
Proof.
  intros.
  destruct H as [n [[]]].
  exists n; split; auto.
Qed.

Lemma have_once_app_l (tr1 tr2: TR) (a: Atom):
  tr1 |= have_once ↑a ->
  ~ (tr2 |= have ↑a) ->
  tr1 ++ tr2 |= have_once ↑a.
Proof.
  intros.
  destruct H as [n [[]]]. 
  exists n; split; [split|].
  * rewrite length_app; lia.
  * unfold lift in *; rewrite nth_error_app1; try lia; auto.
  * intros; apply H2; destruct H3.
    assert (x' <= length tr1). 
    {
      destruct (le_gt_dec x' (length tr1)); auto; exfalso.
      unfold lift in H4. 
      rewrite nth_error_app2 in H4; try lia.
      replace (x' - 1 - length tr1) with (x' - length tr1 - 1) in H4 by lia.
      apply H0; exists (x' - length tr1); split; try lia; auto.
      rewrite length_app in H3; lia.
    }
    split; try lia. 
    unfold lift in H4; rewrite nth_error_app1 in H4; try lia; auto.
Qed.

Lemma have_once_app_r (tr1 tr2: TR) (a: Atom):
  tr2 |= have_once ↑a ->
  ~ (tr1 |= have ↑a) ->
  tr1 ++ tr2 |= have_once ↑a.
Proof.
  intros.
  destruct H as [n [[]]].
  exists (n + length tr1); split; [split|].
  * rewrite length_app; lia.
  * unfold lift; rewrite nth_error_app2; try lia; auto.
    replace (n + length tr1 - 1 - length tr1) with (n - 1) by lia; auto.
  * intros; destruct H3.
    assert (x' > length tr1). {
      destruct (le_gt_dec x' (length tr1)); auto; exfalso.
      unfold lift in H4.
      rewrite nth_error_app1 in H4; try lia; apply H0; exists x'.
      split; auto; lia.
    }
    rewrite length_app in H3.
    assert (1 <= x' - length tr1 <= length tr2) by lia.
    assert (↑ a tr2 (x' - length tr1)). {
      unfold lift in H4. 
      rewrite nth_error_app2 in H4; try lia.
      replace (x' - 1 - length tr1) with (x' - length tr1 - 1) in H4 by lia. auto.
    }
    specialize (H2 (x' - length tr1) ltac:(tauto)); lia.
Qed.

Lemma have_once_before_have_implies_have_both (tr: TR) (a b: Atom):
  tr |= ↑a ->
  tr |= have_once ↑a ->
  tr |= have ↑b ->
  tr |= before_weak ↑a ↑b ->
  tr |= have_both ↑a ↑b.
Proof.
  intros.
  destruct H2.
  * destruct H1 as [m []]. 
    destruct H2 as [n []].
    assert (n = length tr). {
      unfold have_once, last_satisfy, lift in H0.
      destruct H0 as [x []].
      assert (x = length tr) by (apply H5; split; auto; lia).
      assert (x = n) by (apply H5; split; try tauto; lia).
      subst; auto.
    }
    subst n; destruct H4. 
    assert (m = length tr).
    {
     destruct (classic (m = length tr)); auto. 
     exfalso; eapply H5; eauto; lia.
    }
    subst m.
    exists (length tr); repeat split; try lia; auto.
  * exfalso; auto.
Qed.

Lemma before_elim (tr1 tr2: TR) (a b: Atom): 
  tr1 ++ tr2 |= before ↑a ↑b -> 
  ~ (tr2 |= have ↑ a) ->
  tr1 |= before ↑a ↑b.
Proof.
  intros.
  destruct H as [n [? []]].
  unfold lift in H1.
  assert (n <= length tr1). 
  {
    clear - H0 H1.
    apply not_gt; unfold not; intros.
    rewrite nth_error_app2 in H1; try lia.
    destruct (le_gt_dec n (length tr1 + length tr2)).
    * apply H0.
      unfold have, last_satisfy, lift.
      exists (n - length tr1); split; try lia.
      rewrite <- Nat.sub_add_distr in *.
      rewrite Nat.add_comm; auto.
    * assert (length tr2 <= (n - 1 - length tr1)) by lia.
      apply nth_error_None in H2.
      rewrite H2 in H1; auto.
  } 
  exists n; repeat split; try lia.
  ** rewrite nth_error_app1 in H1; try lia; auto.
  ** intros; apply H2 in H4 as Hb.
      unfold not; intros; apply Hb.
      unfold lift; rewrite nth_error_app1; try lia; auto. 
Qed.

Lemma before_eq_elim (tr1 tr2: TR) (a b: Atom): 
  tr1 ++ tr2 |= before_eq ↑a ↑b -> 
  ~ (tr2 |= have ↑ a) ->
  tr1 |= before_eq ↑a ↑b.
Proof.
  intros.
  destruct H as [n [? []]].
  unfold lift in H1.
  assert (n <= length tr1). 
  {
    clear - H0 H1.
    apply not_gt; unfold not; intros.
    rewrite nth_error_app2 in H1; try lia.
    destruct (le_gt_dec n (length tr1 + length tr2)).
    * apply H0.
      unfold have, last_satisfy, lift.
      exists (n - length tr1); split; try lia.
      rewrite <- Nat.sub_add_distr in *.
      rewrite Nat.add_comm; auto.
    * assert (length tr2 <= (n - 1 - length tr1)) by lia.
      apply nth_error_None in H2.
      rewrite H2 in H1; auto.
  } 
  exists n; repeat split; try lia.
  ** rewrite nth_error_app1 in H1; try lia; auto.
  ** intros; apply H2 in H4 as Hb.
      unfold not; intros; apply Hb.
      unfold lift; rewrite nth_error_app1; try lia; auto. 
Qed.

Lemma before_weak_elim (tr1 tr2: TR) (a b: Atom): 
  tr1 ++ tr2 |= before_weak ↑a ↑b -> 
  ~ (tr2 |= have ↑ a) ->
  tr1 |= before_weak ↑a ↑b.
Proof.
  intros.
  destruct H.
  * destruct H as [n [? []]].
    unfold lift in H1.
    assert (n <= length tr1). 
    {
      clear - H0 H1.
      apply not_gt; unfold not; intros.
      rewrite nth_error_app2 in H1; try lia.
      destruct (le_gt_dec n (length tr1 + length tr2)).
      * apply H0.
        unfold have, last_satisfy, lift.
        exists (n - length tr1); split; try lia.
        rewrite <- Nat.sub_add_distr in *.
        rewrite Nat.add_comm; auto.
      * assert (length tr2 <= (n - 1 - length tr1)) by lia.
        apply nth_error_None in H2.
        rewrite H2 in H1; auto.
    } 
    left; exists n; repeat split; try lia.
    ** rewrite nth_error_app1 in H1; try lia; auto.
    ** intros; apply H2 in H4 as Hb.
       unfold not; intros; apply Hb.
       unfold lift; rewrite nth_error_app1; try lia; auto.
  * right. 
    unfold not; intros;
    apply H; destruct H1 as [n []].
    exists n; repeat split; try lia. 
    rewrite length_app; lia.
    unfold lift; rewrite nth_error_app1; try lia; auto. 
Qed.

Lemma latter_occur_not_before (tr tr': TR) (a b: Atom):
  ~ (tr |= have ↑a) -> 
  tr |= have ↑b ->
  ~ (tr ++ tr' |= before ↑a ↑b).
Proof.
  intros; unfold not; intros.
  destruct (classic (tr = nil)) as [Ht|Ht].
  { rewrite Ht in *; eapply not_nil_have; eauto. }
  destruct H1 as [n [? []]].
  assert (n > length tr). 
    {
      clear - H H2 Ht. unfold lift in H2.
      apply not_le; unfold not; intros.
      destruct (classic (n = 0)); subst.
      simpl in H2.
      * destruct tr; auto.
        simpl in H2.
        apply H; rewrite cons_eq_singleton_app; apply app_have_atom.
        left. apply singleton_have_atom; auto.
      * rewrite nth_error_app1 in H2; try lia.
        apply H. unfold have, lift, last.
        exists n; repeat split; try lia; auto.
    } 
  destruct H0 as [m []].
  apply (H3 m). lia.
  unfold lift; rewrite nth_error_app1; try lia; auto.
Qed. 

Lemma latter_occur_not_before_eq (tr tr': TR) (a b: Atom):
  ~ (tr |= have ↑a) -> 
  tr |= have ↑b ->
  ~ (tr ++ tr' |= before_eq ↑a ↑b).
Proof.
  intros; unfold not; intros.
  destruct (classic (tr = nil)) as [Ht|Ht].
  { rewrite Ht in *; eapply not_nil_have; eauto. }
  destruct H1 as [n [? []]].
  assert (n > length tr). 
    {
      clear - H H2 Ht. unfold lift in H2.
      apply not_le; unfold not; intros.
      destruct (classic (n = 0)); subst.
      simpl in H2.
      * destruct tr; auto.
        simpl in H2.
        apply H; rewrite cons_eq_singleton_app; apply app_have_atom.
        left. apply singleton_have_atom; auto.
      * rewrite nth_error_app1 in H2; try lia.
        apply H. unfold have, lift, last.
        exists n; repeat split; try lia; auto.
    } 
  destruct H0 as [m []].
  apply (H3 m). lia.
  unfold lift; rewrite nth_error_app1; try lia; auto.
Qed. 

Lemma not_before_eq_refl (tr: TR) (a: Atom): 
  ~ (tr |= before_eq ↑a ↑a).
Proof.
  unfold not; intros.
  destruct H as [n [? []]].
  eapply H1; eauto; lia.
Qed.

Lemma have_alw_have (tr: TR) (a: T) (b c: Σ -> Prop): 
  tr |= have (ts↑ a b) -> tr |= alw (s↑ c) ->
  tr |= have (ts↑ a (fun s => b s /\ c s)).
Proof.
  intros.
  destruct H as [n []]. 
  exists n; repeat split; try lia. 
  unfold last_satisfy, alw, tsAtom, sAtom, lift in *.
  specialize (H0 n H).
  destruct (nth_error tr (n - 1)); [|exfalso; auto].
  destruct p; firstorder.
Qed.

Lemma have_global_prop_s (tr: TR) (P: Prop) (b: Σ -> Prop):
  P ->
  tr |= have (s↑ b) -> 
  tr |= have (s↑ (fun s => b s /\ P)).
Proof.
  intros.
  destruct H0 as [n []].
  exists n; repeat split; try lia.
  unfold last_satisfy, sAtom, lift in *.
  destruct (nth_error tr (n - 1)); [destruct p|]; firstorder.
Qed.

Lemma have_global_prop_ts (tr: TR) (P: Prop) (a: T) (b: Σ -> Prop):
  P ->
  tr |= have (ts↑ a b) -> 
  tr |= have (ts↑ a (fun s => b s /\ P)).
Proof.
  intros.
  destruct H0 as [n []].
  exists n; repeat split; try lia.
  unfold last_satisfy, tsAtom, lift in *.
  destruct (nth_error tr (n - 1)); [destruct p|]; firstorder.
Qed.

Lemma have_tsatom_exclude_middle (tr: TR) (a: T) (b: Σ -> Prop):
  (tr |= have (t↑ a)) ->
  (tr |= have (ts↑ a (fun s => b s))) \/ (tr |= have (ts↑ a (fun s => ~ b s))).
Proof.
  intros.
  destruct H as [n []].
  unfold lift in H0.
  destruct (nth_error tr (n - 1)) eqn:Heq; [destruct p|].
  * destruct (classic (b σ)); [left|right];
    exists n; unfold tsAtom, lift; split; try lia; auto; rewrite Heq; split; auto.
  * left; exists n; unfold tsAtom, lift; split; try lia; auto.
Qed.

Lemma have_once_satom_conj (tr: TR) (a: T) (b c: Σ -> Prop):
  tr |= have_once (t↑ a) ->
  tr |= have (ts↑ a b) ->
  tr |= have (ts↑ a c) -> 
  tr |= have (ts↑ a (fun s => b s /\ c s)).
Proof.
  intros.
  destruct H as [n [[]]].
  destruct H0 as [m []].
  assert (n = m). {
    apply H3; split; auto.
    unfold tsAtom, lift in H4; unfold tAtom, lift.
    destruct (nth_error tr (m - 1)); [destruct p|]; tauto.
  } subst m.
  destruct H1 as [m []].
  assert (n = m). {
    apply H3; split; auto.
    unfold tsAtom, lift in H5; unfold tAtom, lift.
    destruct (nth_error tr (m - 1)); [destruct p|]; tauto.
  } subst m.
  exists n; repeat split; try lia; auto.
  unfold tsAtom, lift in *.
  destruct (nth_error tr (n - 1)); [destruct p|]; tauto.
Qed.

End TraceRule.



Definition trace_nat: @TR nat nat:= (1, 1) ::(2, 2) ::(3, 3) ::(4, 4) :: nil.

Example trace_nat_prop1:
  trace_nat |= alw (↑ (fun '(t, s) => t = s)).
Proof.
  unfold last_satisfy, alw, lift, trace_nat; simpl.
  intros.
  do 5 (destruct j; simpl; auto); lia.
Qed.
