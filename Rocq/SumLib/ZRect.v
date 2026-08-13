Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SumLib Require Import Sum ZRange.

Import ListNotations.

Local Open Scope Z_scope.

(** * 整数二维矩形 *)

(** ** 注册的 Instance *)

Lemma NoDup_app_intro {A : Type} : forall (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> In x l2 -> False) ->
  NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2 Hnodup1 Hnodup2 Hdisj; simpl.
  - exact Hnodup2.
  - inversion Hnodup1 as [|? ? Hnotin Hnodup1']; subst.
    constructor.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * contradiction.
      * eapply Hdisj.
        -- left. reflexivity.
        -- exact Hin.
    + apply IH.
      * exact Hnodup1'.
      * exact Hnodup2.
      * intros y Hy1 Hy2.
        eapply Hdisj.
        -- right. exact Hy1.
        -- exact Hy2.
Qed.

Lemma NoDup_map_pair_r : forall (x : Z) (ys : list Z),
  NoDup ys ->
  NoDup (map (fun y => (x, y)) ys).
Proof.
  intros x ys.
  induction ys as [|y ys IH]; intros Hnodup; simpl.
  - constructor.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin as [y' [Hpair Hy']].
      inversion Hpair; subst.
      contradiction.
    + apply IH. exact Hnodup'.
Qed.

Lemma NoDup_flat_map_rect : forall (xs ys : list Z),
  NoDup xs ->
  NoDup ys ->
  NoDup (flat_map (fun x => map (fun y => (x, y)) ys) xs).
Proof.
  induction xs as [|x xs IH]; intros ys Hnodup_xs Hnodup_ys; simpl.
  - constructor.
  - inversion Hnodup_xs as [|? ? Hnotin Hnodup_xs']; subst.
    apply NoDup_app_intro.
    + apply NoDup_map_pair_r. exact Hnodup_ys.
    + apply IH; assumption.
    + intros p Hp_left Hp_right.
      apply in_map_iff in Hp_left as [y [Hp Hy]].
      subst p.
      apply in_flat_map in Hp_right as [x' [Hx' Hmap]].
      apply in_map_iff in Hmap as [y' [Hpair Hy']].
      inversion Hpair; subst.
      contradiction.
Qed.

Definition Zrect (x_low x_high y_low y_high : Z) : list (Z * Z) :=
  flat_map
    (fun x => map (fun y => (x, y)) (Zrange y_low y_high))
    (Zrange x_low x_high).

#[export] Instance finite_Z_rect (x_low x_high y_low y_high : Z) :
  Finite (fun p : Z * Z => x_low <= fst p < x_high /\ y_low <= snd p < y_high).
Proof.
  refine {| enum := Zrect x_low x_high y_low y_high |}.
  - intros [x y].
    unfold Zrect.
    rewrite in_flat_map.
    split.
    + intros [Hx Hy].
      exists x.
      split.
      * rewrite <- In_Zrange. exact Hx.
      * apply in_map_iff.
        exists y.
        split.
        -- reflexivity.
        -- rewrite <- In_Zrange. exact Hy.
    + intros [x' [Hx' Hmap]].
      apply in_map_iff in Hmap as [y' [Hp Hy']].
      inversion Hp; subst.
      split.
      * rewrite <- In_Zrange in Hx'. exact Hx'.
      * rewrite <- In_Zrange in Hy'. exact Hy'.
  - unfold Zrect.
    apply NoDup_flat_map_rect; apply NoDup_Zrange.
Defined.

#[export] Instance finite_Z_rect'
    (x_low x_high y_low y_high : Z)
    (P : Z * Z -> Prop) :
  Finite
    (fun p : Z * Z =>
       x_low <= fst p < x_high /\
       y_low <= snd p < y_high /\
       P p).
Proof.
  refine {| enum :=
    filter
      (fun p => if prop_dec (P p) then true else false)
      (Zrect x_low x_high y_low y_high) |}.
  - intros [x y].
    rewrite filter_In.
    unfold Zrect.
    rewrite in_flat_map.
    split.
    + intros [Hx [Hy HP]].
      split.
      * exists x.
        split.
        -- rewrite <- In_Zrange. exact Hx.
        -- apply in_map_iff.
           exists y.
           split.
           ++ reflexivity.
           ++ rewrite <- In_Zrange. exact Hy.
      * destruct (prop_dec (P (x, y))) as [_ | Hnot]; [reflexivity | contradiction].
    + intros [Henum Htest].
      split.
      * destruct Henum as [x' [Hx' Hmap]].
        apply in_map_iff in Hmap as [y' [Hp Hy']].
        inversion Hp; subst.
        rewrite <- In_Zrange in Hx'. exact Hx'.
      * split.
        -- destruct Henum as [x' [Hx' Hmap]].
           apply in_map_iff in Hmap as [y' [Hp Hy']].
           inversion Hp; subst.
           rewrite <- In_Zrange in Hy'. exact Hy'.
        -- destruct (prop_dec (P (x, y))) as [HP | Hnot]; [exact HP | discriminate].
  - apply NoDup_filter_bool.
    unfold Zrect.
    apply NoDup_flat_map_rect; apply NoDup_Zrange.
Defined.

(** ** 内部辅助引理 *)

Lemma fold_sum_app {A : Type} : forall l1 l2 (f : A -> Z),
  fold_right (fun x acc => f x + acc) 0 (l1 ++ l2) =
  fold_right (fun x acc => f x + acc) 0 l1 +
  fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 f; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma fold_Zsum_map_pair : forall x ys (f : Z -> Z -> Z),
  fold_right (fun p acc => f (fst p) (snd p) + acc) 0
    (map (fun y => (x, y)) ys) =
  fold_right (fun y acc => f x y + acc) 0 ys.
Proof.
  intros x ys.
  induction ys as [|y ys IH]; intros f; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma fold_Zsum_flat_map_rect : forall xs ys (f : Z -> Z -> Z),
  fold_right (fun p acc => f (fst p) (snd p) + acc) 0
    (flat_map (fun x => map (fun y => (x, y)) ys) xs) =
  fold_right
    (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
    0 xs.
Proof.
  induction xs as [|x xs IH]; intros ys f; simpl.
  - reflexivity.
  - rewrite fold_sum_app.
    rewrite fold_Zsum_map_pair.
    rewrite IH.
    reflexivity.
Qed.

Lemma fold_sum_zero {A : Type} : forall (xs : list A),
  fold_right (fun _ acc => 0 + acc) 0 xs = 0.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

Lemma fold_sum_add {A : Type} : forall (xs : list A) (f g : A -> Z),
  fold_right (fun x acc => (f x + g x) + acc) 0 xs =
  fold_right (fun x acc => f x + acc) 0 xs +
  fold_right (fun x acc => g x + acc) 0 xs.
Proof.
  induction xs as [|x xs IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma fold_Zsum_nested_swap : forall xs ys (f : Z -> Z -> Z),
  fold_right
    (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
    0 xs =
  fold_right
    (fun y acc => fold_right (fun x acc => f x y + acc) 0 xs + acc)
    0 ys.
Proof.
  induction xs as [|x xs IH]; intros ys f; simpl.
  - rewrite fold_sum_zero. reflexivity.
  - rewrite IH.
    rewrite <- fold_sum_add.
    reflexivity.
Qed.

(** ** 公开的二维矩形求和性质 *)

(** 用户侧推荐把二维求和写成嵌套的 [sum]。
    基于 pair 的矩形 instance 主要作为这些引理内部使用的桥。 *)
Lemma sum_Z_rect_nested : forall x_low x_high y_low y_high f,
  sum (fun p : Z * Z => x_low <= fst p < x_high /\ y_low <= snd p < y_high)
      (fun p => f (fst p) (snd p)) =
  sum (fun x => x_low <= x < x_high)
      (fun x => sum (fun y => y_low <= y < y_high)
                    (fun y => f x y)).
Proof.
  intros x_low x_high y_low y_high f.
  unfold sum. simpl.
  unfold Zrect.
  apply fold_Zsum_flat_map_rect.
Qed.

Lemma sum_Z_rect_swap : forall x_low x_high y_low y_high f,
  sum (fun x => x_low <= x < x_high)
      (fun x => sum (fun y => y_low <= y < y_high)
                    (fun y => f x y)) =
  sum (fun y => y_low <= y < y_high)
      (fun y => sum (fun x => x_low <= x < x_high)
                    (fun x => f x y)).
Proof.
  intros x_low x_high y_low y_high f.
  unfold sum. simpl.
  apply fold_Zsum_nested_swap.
Qed.

Lemma sum_Z_rect_pair_swap : forall x_low x_high y_low y_high f,
  sum (fun p : Z * Z => x_low <= fst p < x_high /\ y_low <= snd p < y_high)
      (fun p => f (fst p) (snd p)) =
  sum (fun p : Z * Z => y_low <= fst p < y_high /\ x_low <= snd p < x_high)
      (fun p => f (snd p) (fst p)).
Proof.
  intros x_low x_high y_low y_high f.
  rewrite (sum_Z_rect_nested x_low x_high y_low y_high f).
  rewrite (sum_Z_rect_nested y_low y_high x_low x_high (fun y x => f x y)).
  apply sum_Z_rect_swap.
Qed.
