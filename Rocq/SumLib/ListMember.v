Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SumLib Require Import Sum.

Import ListNotations.

Local Open Scope Z_scope.

(** * 列表成员集合 *)

(** ** 注册的 Instance *)

#[export] Instance finite_list_member
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l : list A) :
  Finite (fun x : A => In x l).
Proof.
  refine {| enum := nodup eq_dec l |}.
  - intros x.
    rewrite nodup_In.
    tauto.
  - apply NoDup_nodup.
Defined.

#[export] Instance finite_list_member'
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l : list A)
    (P : A -> Prop) :
  Finite (fun x : A => In x l /\ P x).
Proof.
  refine {| enum :=
    filter
      (fun x => if prop_dec (P x) then true else false)
      (nodup eq_dec l) |}.
  - intros x.
    rewrite filter_In.
    rewrite nodup_In.
    split.
    + intros [Hin HP].
      split; [exact Hin |].
      destruct (prop_dec (P x)) as [_ | Hnot]; [reflexivity | contradiction].
    + intros [Hin Htest].
      split; [exact Hin |].
      destruct (prop_dec (P x)) as [HP | Hnot]; [exact HP | discriminate].
  - apply NoDup_filter_bool.
    apply NoDup_nodup.
Defined.

(** ** 内部辅助引理 *)

(** ** 公开求和性质 *)

Lemma sum_list_member_remove
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l : list A) (x : A) (f : A -> Z) :
  NoDup l ->
  In x l ->
  @sum A (fun y : A => In y l) (finite_list_member eq_dec l) f =
  f x +
  @sum A
       (fun y : A => In y (remove eq_dec x l))
       (finite_list_member eq_dec (remove eq_dec x l))
       f.
Proof.
  intros Hnodup Hin.
  unfold sum; simpl.
  rewrite nodup_fixed_point by exact Hnodup.
  assert (Hremove_nodup : NoDup (remove eq_dec x l)).
  {
    clear Hin.
    induction Hnodup as [| y l' Hnotin Hnodup IH]; simpl.
    - constructor.
    - destruct (eq_dec x y).
      + exact IH.
      + constructor; auto.
        intro Hy.
        apply in_remove in Hy as [Hy _].
        contradiction.
  }
  rewrite nodup_fixed_point by exact Hremove_nodup.
  induction l as [| y l' IH]; simpl in Hin; [contradiction |].
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  simpl.
  destruct (eq_dec x y) as [Heq | Hneq].
  - subst.
    rewrite notin_remove by exact Hnotin.
    reflexivity.
  - destruct Hin as [Hin | Hin]; [subst; contradiction |].
    assert (Hremove_tail : NoDup (remove eq_dec x l')).
    {
      simpl in Hremove_nodup.
      destruct (eq_dec x y) as [Heq | _]; [contradiction |].
      inversion Hremove_nodup; auto.
    }
    rewrite (IH Hnodup_tail Hin Hremove_tail).
    simpl.
    destruct (eq_dec x y) as [Heq | _]; [contradiction |].
    lia.
Qed.

(** ** 与旧 [ListLib.sum] 的桥接 *)

Lemma list_sum_map_as_list_member_sum
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l : list A) (f : A -> Z) :
  NoDup l ->
  ListLib.sum (map f l) =
  @sum A (fun x : A => In x l) (finite_list_member eq_dec l) f.
Proof.
  intros Hnodup.
  unfold sum; simpl.
  rewrite nodup_fixed_point by exact Hnodup.
  induction l as [| x l IH]; simpl.
  - reflexivity.
  - inversion Hnodup; subst.
    rewrite IH by auto.
    reflexivity.
Qed.
