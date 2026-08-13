Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Local Open Scope Z_scope.

(** * 通用有限求和接口 *)

(** ** 通用定义 *)

Axiom prop_dec : forall P : Prop, {P} + {~P}.

Class Finite {A : Type} (P : A -> Prop) := {
  enum : list A;
  enum_ok : forall x, P x <-> In x enum;
  enum_nodup : NoDup enum
}.

Definition sum {A : Type} (P : A -> Prop) {_finite : Finite P} (f : A -> Z) : Z :=
  fold_right (fun x acc => f x + acc) 0 enum.

(** ** 内部辅助引理 *)

Lemma NoDup_filter_bool {A : Type} (p : A -> bool) :
  forall xs, NoDup xs -> NoDup (filter p xs).
Proof.
  induction xs as [|x xs IH]; intros Hnodup; simpl.
  - constructor.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    destruct (p x) eqn:Hp.
    + constructor.
      * intro Hin.
        apply filter_In in Hin as [Hin _].
        contradiction.
      * apply IH. exact Hnodup'.
    + apply IH. exact Hnodup'.
Qed.

(** ** 公开求和性质 *)

Lemma sum_ext {A : Type} (P : A -> Prop) {_finite : Finite P} (f g : A -> Z) :
  (forall x, P x -> f x = g x) ->
  sum P f = sum P g.
Proof.
  intros Hext.
  unfold sum.
  assert (Hfold : forall xs,
    (forall x, In x xs -> P x) ->
    fold_right (fun x acc => f x + acc) 0 xs =
    fold_right (fun x acc => g x + acc) 0 xs).
  {
    induction xs as [|x xs IH]; intros Hmem; simpl; auto.
    rewrite (Hext x (Hmem x (or_introl eq_refl))).
    rewrite IH.
    - reflexivity.
    - intros y Hy. apply Hmem. right. exact Hy.
  }
  apply Hfold.
  intros x Hin.
  apply (proj2 (enum_ok x)).
  exact Hin.
Qed.

Lemma sum_zero {A : Type} (P : A -> Prop) {_finite : Finite P} :
  sum P (fun _ => 0) = 0.
Proof.
  unfold sum.
  induction enum; simpl; auto.
Qed.

Lemma sum_factor_l {A : Type} (P : A -> Prop) {_finite : Finite P} c (f : A -> Z) :
  sum P (fun x => c * f x) = c * sum P f.
Proof.
  unfold sum.
  induction enum as [|x xs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_factor_r {A : Type} (P : A -> Prop) {_finite : Finite P} c (f : A -> Z) :
  sum P (fun x => f x * c) = sum P f * c.
Proof.
  unfold sum.
  induction enum as [|x xs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_add {A : Type} (P : A -> Prop) {_finite : Finite P} (f g : A -> Z) :
  sum P (fun x => f x + g x) = sum P f + sum P g.
Proof.
  unfold sum.
  induction enum as [|x xs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_opp {A : Type} (P : A -> Prop) {_finite : Finite P} (f : A -> Z) :
  sum P (fun x => - f x) = - sum P f.
Proof.
  unfold sum.
  induction enum as [|x xs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_sub {A : Type} (P : A -> Prop) {_finite : Finite P} (f g : A -> Z) :
  sum P (fun x => f x - g x) = sum P f - sum P g.
Proof.
  unfold sum.
  induction enum as [|x xs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_nonneg {A : Type} (P : A -> Prop) {_finite : Finite P} (f : A -> Z) :
  (forall x, P x -> 0 <= f x) ->
  0 <= sum P f.
Proof.
  intros Hnonneg.
  unfold sum.
  assert (Hfold : forall xs,
    (forall x, In x xs -> P x) ->
    0 <= fold_right (fun x acc => f x + acc) 0 xs).
  {
    induction xs as [|x xs IH]; intros Hmem; simpl.
    - lia.
    - specialize (IH ltac:(intros y Hy; apply Hmem; right; exact Hy)).
      pose proof (Hnonneg x (Hmem x (or_introl eq_refl))).
      lia.
  }
  apply Hfold.
  intros x Hin.
  apply (proj2 (enum_ok x)).
  exact Hin.
Qed.

Lemma sum_le {A : Type} (P : A -> Prop) {_finite : Finite P} (f g : A -> Z) :
  (forall x, P x -> f x <= g x) ->
  sum P f <= sum P g.
Proof.
  intros Hle.
  unfold sum.
  assert (Hfold : forall xs,
    (forall x, In x xs -> P x) ->
    fold_right (fun x acc => f x + acc) 0 xs <=
    fold_right (fun x acc => g x + acc) 0 xs).
  {
    induction xs as [|x xs IH]; intros Hmem; simpl.
    - lia.
    - specialize (IH ltac:(intros y Hy; apply Hmem; right; exact Hy)).
      pose proof (Hle x (Hmem x (or_introl eq_refl))).
      lia.
  }
  apply Hfold.
  intros x Hin.
  apply (proj2 (enum_ok x)).
  exact Hin.
Qed.

Lemma sum_nonneg_eq_zero_elim {A : Type} (P : A -> Prop) {_finite : Finite P} (f : A -> Z) :
  (forall x, P x -> 0 <= f x) ->
  sum P f = 0 ->
  forall x, P x -> f x = 0.
Proof.
  intros Hnonneg Hsum x HP.
  unfold sum in Hsum.
  assert (Hfold_nonneg : forall xs,
    (forall y, In y xs -> P y) ->
    0 <= fold_right (fun y acc => f y + acc) 0 xs).
  {
    induction xs as [|y ys IH]; intros Hmem; simpl.
    - lia.
    - specialize (IH ltac:(intros z Hz; apply Hmem; right; exact Hz)).
      pose proof (Hnonneg y (Hmem y (or_introl eq_refl))).
      lia.
  }
  assert (Hall : forall y, In y enum -> f y = 0).
  {
    set (xs := enum).
    assert (Hmem : forall y, In y xs -> P y).
    {
      intros y Hy.
      unfold xs in Hy.
      apply (proj2 (enum_ok y)).
      exact Hy.
    }
    change (fold_right (fun y acc => f y + acc) 0 xs = 0) in Hsum.
    change (forall y, In y xs -> f y = 0).
    clearbody xs.
    clear x HP.
    revert Hsum Hmem.
    induction xs as [|y ys IH]; intros Hsum Hmem z Hz; simpl in *.
    - contradiction.
    - assert (Htail_nonneg : 0 <= fold_right (fun y acc => f y + acc) 0 ys).
      { apply Hfold_nonneg. intros u Hu. apply Hmem. right. exact Hu. }
      assert (Hy_nonneg : 0 <= f y) by (apply Hnonneg, Hmem; left; reflexivity).
      assert (Hy_zero : f y = 0) by lia.
      assert (Htail_zero : fold_right (fun y acc => f y + acc) 0 ys = 0) by lia.
      destruct Hz as [Hz | Hz].
      + subst z. exact Hy_zero.
      + eapply IH.
        * exact Htail_zero.
        * intros u Hu. apply Hmem. right. exact Hu.
        * exact Hz.
  }
  apply Hall.
  apply (proj1 (enum_ok x)).
  exact HP.
Qed.
