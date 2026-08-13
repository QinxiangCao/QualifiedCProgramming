Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SumLib Require Import Sum.

Import ListNotations.

Local Open Scope Z_scope.

(** * 整数区间 *)

(** ** 注册的 Instance *)

(** [Zrange low high] 枚举半开区间 [[low, high)]。 *)
Fixpoint Zrange_aux (low : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => low :: Zrange_aux (low + 1) n'
  end.

Definition Zrange (low high : Z) : list Z :=
  Zrange_aux low (Z.to_nat (high - low)).

Lemma In_Zrange_aux : forall n low x,
  In x (Zrange_aux low n) <-> low <= x < low + Z.of_nat n.
Proof.
  induction n as [|n' IH]; intros low x; simpl.
  - split; [tauto | lia].
  - rewrite IH. lia.
Qed.

Lemma In_Zrange : forall low high x,
  low <= x < high <-> In x (Zrange low high).
Proof.
  intros. unfold Zrange. rewrite In_Zrange_aux. lia.
Qed.

Lemma NoDup_Zrange_aux : forall n low,
  NoDup (Zrange_aux low n).
Proof.
  induction n as [|n IH]; intros low; simpl.
  - constructor.
  - constructor.
    + rewrite In_Zrange_aux. lia.
    + apply IH.
Qed.

Lemma NoDup_Zrange : forall low high,
  NoDup (Zrange low high).
Proof.
  intros low high.
  unfold Zrange.
  apply NoDup_Zrange_aux.
Qed.

#[export] Instance finite_Z_range (low high : Z) : Finite (fun x => low <= x < high).
Proof.
  refine {| enum := Zrange low high |}.
  - apply In_Zrange.
  - apply NoDup_Zrange.
Defined.

#[export] Instance finite_Z_range' (low high : Z) (P : Z -> Prop) :
  Finite (fun x => low <= x < high /\ P x).
Proof.
  refine {| enum := filter (fun x => if prop_dec (P x) then true else false) (Zrange low high) |}.
  - intros x.
    rewrite filter_In.
    rewrite <- In_Zrange.
    split.
    + intros [Hrange HP].
      split; [exact Hrange |].
      destruct (prop_dec (P x)) as [_ | Hnot]; [reflexivity | contradiction].
    + intros [Hrange Htest].
      split; [exact Hrange |].
      destruct (prop_dec (P x)) as [HP | Hnot]; [exact HP | discriminate].
  - apply NoDup_filter_bool.
    apply NoDup_Zrange.
Defined.

(** ** 区间枚举上的辅助 fold 引理 *)

Lemma sum_range_unfold : forall low high f,
  sum (fun x => low <= x < high) f
  = fold_right (fun x acc => f x + acc) 0 (Zrange low high).
Proof. reflexivity. Qed.

Lemma fold_Zrange_aux_shift : forall n low f,
  fold_right (fun x acc => f x + acc) 0 (Zrange_aux (low + 1) n)
  = fold_right (fun x acc => f (x + 1) + acc) 0 (Zrange_aux low n).
Proof.
  induction n as [|n IH]; intros; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma Zrange_aux_app : forall n m low,
  Zrange_aux low (n + m)%nat =
  Zrange_aux low n ++ Zrange_aux (low + Z.of_nat n) m.
Proof.
  induction n as [|n IH]; intros m low; simpl.
  - replace (low + 0) with low by lia.
    reflexivity.
  - rewrite IH.
    replace (low + 1 + Z.of_nat n) with (low + Z.of_nat (S n)) by lia.
    reflexivity.
Qed.

Lemma fold_Zsum_app : forall l1 l2 (f : Z -> Z),
  fold_right (fun x acc => f x + acc) 0 (l1 ++ l2) =
  fold_right (fun x acc => f x + acc) 0 l1 +
  fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 f; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma fold_Zrange_aux_shift_by : forall n low k f,
  fold_right (fun x acc => f x + acc) 0 (Zrange_aux (low + k) n) =
  fold_right (fun x acc => f (x + k) + acc) 0 (Zrange_aux low n).
Proof.
  induction n as [|n IH]; intros low k f; simpl.
  - reflexivity.
  - replace (low + k + 1) with (low + 1 + k) by lia.
    rewrite IH.
    reflexivity.
Qed.

Lemma fold_Zsum_ext_in : forall l (f g : Z -> Z),
  (forall x, In x l -> f x = g x) ->
  fold_right (fun x acc => f x + acc) 0 l
  = fold_right (fun x acc => g x + acc) 0 l.
Proof.
  induction l as [|x l IH]; intros; simpl; auto.
  rewrite (H x) by (left; auto).
  rewrite (IH f g); auto.
  intros. apply H. right. auto.
Qed.

Lemma In_Zrange_aux_lb : forall n low x,
  In x (Zrange_aux low n) -> low <= x.
Proof.
  induction n; intros; simpl in *; try contradiction.
  destruct H. lia.
  apply IHn in H. lia.
Qed.

(** ** 公开的区间求和性质 *)
(** 本节的 [sum_Z_range_*] 只处理整数区间本身，不绑定具体数据结构。 *)

Lemma sum_Z_range_empty : forall low high f,
  high <= low ->
  sum (fun x => low <= x < high) f = 0.
Proof.
  intros low high f Hle.
  rewrite sum_range_unfold.
  unfold Zrange.
  replace (Z.to_nat (high - low)) with 0%nat by lia.
  reflexivity.
Qed.

Lemma sum_Z_range_cons : forall low high f,
  low < high ->
  sum (fun x => low <= x < high) f =
  f low + sum (fun x => low + 1 <= x < high) f.
Proof.
  intros low high f Hlt.
  rewrite !sum_range_unfold.
  unfold Zrange.
  replace (Z.to_nat (high - low))
    with (S (Z.to_nat (high - (low + 1)))) by lia.
  reflexivity.
Qed.

Lemma sum_Z_range_shift_1 : forall low high f,
  sum (fun x => low + 1 <= x < high + 1) f =
  sum (fun x => low <= x < high) (fun x => f (x + 1)).
Proof.
  intros low high f.
  rewrite !sum_range_unfold.
  unfold Zrange.
  replace (Z.to_nat (high + 1 - (low + 1)))
    with (Z.to_nat (high - low)) by lia.
  apply fold_Zrange_aux_shift.
Qed.

Lemma sum_Z_range_shift : forall low high k f,
  sum (fun x => low + k <= x < high + k) f =
  sum (fun x => low <= x < high) (fun x => f (x + k)).
Proof.
  intros low high k f.
  rewrite !sum_range_unfold.
  unfold Zrange.
  replace (Z.to_nat (high + k - (low + k)))
    with (Z.to_nat (high - low)) by lia.
  apply fold_Zrange_aux_shift_by.
Qed.

Lemma sum_Z_range_factor_l : forall low high c f,
  sum (fun x => low <= x < high) (fun x => c * f x) =
  c * sum (fun x => low <= x < high) f.
Proof.
  intros low high c f.
  apply sum_factor_l.
Qed.

Lemma sum_Z_range_factor_r : forall low high c f,
  sum (fun x => low <= x < high) (fun x => f x * c) =
  sum (fun x => low <= x < high) f * c.
Proof.
  intros low high c f.
  apply sum_factor_r.
Qed.

Lemma sum_Z_range_ext : forall low high f g,
  (forall x, low <= x < high -> f x = g x) ->
  sum (fun x => low <= x < high) f =
  sum (fun x => low <= x < high) g.
Proof.
  intros low high f g Hext. apply sum_ext. exact Hext.
Qed.

Lemma sum_Z_range_zero : forall low high,
  sum (fun x => low <= x < high) (fun _ => 0) = 0.
Proof.
  intros low high. apply sum_zero.
Qed.

Lemma sum_Z_range_eq_zero : forall low high f,
  (forall x, low <= x < high -> f x = 0) ->
  sum (fun x => low <= x < high) f = 0.
Proof.
  intros low high f Hzero.
  transitivity (sum (fun x => low <= x < high) (fun _ => 0)).
  - apply sum_Z_range_ext.
    exact Hzero.
  - apply sum_Z_range_zero.
Qed.

Lemma sum_Z_range_single : forall i f,
  sum (fun x => i <= x < i + 1) f = f i.
Proof.
  intros i f.
  rewrite sum_Z_range_cons by lia.
  rewrite sum_Z_range_empty by lia.
  ring.
Qed.

Lemma sum_Z_range_add : forall low high f g,
  sum (fun x => low <= x < high) (fun x => f x + g x) =
  sum (fun x => low <= x < high) f +
  sum (fun x => low <= x < high) g.
Proof.
  intros low high f g.
  apply sum_add.
Qed.

Lemma sum_Z_range_sub : forall low high f g,
  sum (fun x => low <= x < high) (fun x => f x - g x) =
  sum (fun x => low <= x < high) f -
  sum (fun x => low <= x < high) g.
Proof.
  intros low high f g.
  apply sum_sub.
Qed.

Lemma sum_Z_range_le : forall low high f g,
  (forall x, low <= x < high -> f x <= g x) ->
  sum (fun x => low <= x < high) f <=
  sum (fun x => low <= x < high) g.
Proof.
  intros low high f g Hle.
  apply sum_le.
  exact Hle.
Qed.

Lemma sum_Z_range_const : forall low high c,
  low <= high ->
  sum (fun x => low <= x < high) (fun _ => c) = (high - low) * c.
Proof.
  intros low high c Hrange.
  rewrite sum_range_unfold.
  unfold Zrange.
  assert (Hfold : forall n start,
    fold_right (fun _ acc => c + acc) 0 (Zrange_aux start n) =
    c * Z.of_nat n).
  {
    induction n as [|n IH]; intros start; simpl.
    - ring.
    - rewrite IH.
      replace (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat n + 1) by lia.
      ring.
  }
  rewrite Hfold.
  replace (Z.of_nat (Z.to_nat (high - low))) with (high - low) by lia.
  ring.
Qed.

Lemma sum_Z_range_upper_bound : forall low high f b,
  low <= high ->
  (forall x, low <= x < high -> f x <= b) ->
  sum (fun x => low <= x < high) f <= (high - low) * b.
Proof.
  intros low high f b Hrange Hbound.
  eapply Z.le_trans.
  - apply sum_Z_range_le. exact Hbound.
  - rewrite sum_Z_range_const by lia.
    reflexivity.
Qed.

Lemma sum_Z_range_lower_bound : forall low high f b,
  low <= high ->
  (forall x, low <= x < high -> b <= f x) ->
  (high - low) * b <= sum (fun x => low <= x < high) f.
Proof.
  intros low high f b Hrange Hbound.
  eapply Z.le_trans with
    (m := sum (fun x => low <= x < high) (fun _ => b)).
  - rewrite sum_Z_range_const by lia.
    reflexivity.
  - apply sum_Z_range_le. exact Hbound.
Qed.

Lemma sum_Z_range_bounds : forall low high f lb ub,
  low <= high ->
  (forall x, low <= x < high -> lb <= f x <= ub) ->
  (high - low) * lb <=
  sum (fun x => low <= x < high) f <=
  (high - low) * ub.
Proof.
  intros low high f lb ub Hrange Hbound.
  split.
  - apply sum_Z_range_lower_bound.
    + exact Hrange.
    + intros x Hx. specialize (Hbound x Hx). lia.
  - apply sum_Z_range_upper_bound.
    + exact Hrange.
    + intros x Hx.
      specialize (Hbound x Hx).
      lia.
Qed.

Lemma sum_Z_range_split : forall low mid high f,
  low <= mid <= high ->
  sum (fun x => low <= x < high) f =
  sum (fun x => low <= x < mid) f +
  sum (fun x => mid <= x < high) f.
Proof.
  intros low mid high f Hmid.
  rewrite !sum_range_unfold.
  unfold Zrange.
  replace (Z.to_nat (high - low))
    with (Z.to_nat (mid - low) + Z.to_nat (high - mid))%nat by lia.
  rewrite Zrange_aux_app.
  rewrite fold_Zsum_app.
  replace (low + Z.of_nat (Z.to_nat (mid - low))) with mid by lia.
  reflexivity.
Qed.

Lemma sum_Z_range_extend_right : forall low high f,
  low <= high ->
  sum (fun x => low <= x < high + 1) f =
  sum (fun x => low <= x < high) f + f high.
Proof.
  intros low high f Hrange.
  rewrite (sum_Z_range_split low high (high + 1)) by lia.
  rewrite sum_Z_range_single.
  reflexivity.
Qed.

Lemma sum_Z_range_extend_left : forall low high f,
  low <= high ->
  sum (fun x => low - 1 <= x < high) f =
  f (low - 1) + sum (fun x => low <= x < high) f.
Proof.
  intros low high f Hrange.
  rewrite sum_Z_range_cons by lia.
  replace (low - 1 + 1) with low by lia.
  reflexivity.
Qed.

(** ** 区间与列表下标 *)
(** 本节的 [sum_Z_range_Znth_*] 表示用整数区间遍历列表下标。 *)

Lemma Znth_In_Zlength {A : Type} :
  forall (l : list A) (default : A) i,
  0 <= i < Zlength l ->
  In (Znth i l default) l.
Proof.
  intros l default i Hi.
  unfold Znth.
  apply nth_In.
  replace (List.length l) with (Z.to_nat (Zlength l)).
  - apply Z2Nat.inj_lt; lia.
  - rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma Forall_Znth_Zlength {A : Type} :
  forall (P : A -> Prop) (l : list A) (default : A) i,
  Forall P l ->
  0 <= i < Zlength l ->
  P (Znth i l default).
Proof.
  intros P l default i HForall Hi.
  apply Forall_forall with (x := Znth i l default) in HForall.
  - exact HForall.
  - apply Znth_In_Zlength. exact Hi.
Qed.

Lemma sum_Z_range_Znth_cons_indexed {A : Type} :
  forall (default a : A) (l : list A) (F : Z -> A -> Z),
  sum (fun i => 0 <= i < Zlength (a :: l))
      (fun i => F i (Znth i (a :: l) default)) =
  F 0 a +
  sum (fun i => 0 <= i < Zlength l)
      (fun i => F (i + 1) (Znth i l default)).
Proof.
  intros default a l F.
  rewrite Zlength_cons.
  replace (Z.succ (Zlength l)) with (Zlength l + 1) by lia.
  rewrite (sum_Z_range_cons 0 (Zlength l + 1)
    (fun i : Z => F i (Znth i (a :: l) default)))
    by (pose proof (Zlength_nonneg l); lia).
  rewrite Znth0_cons.
  f_equal.
  change (fun x : Z => 0 + 1 <= x < Zlength l + 1)
    with (fun x : Z => 1 <= x < Zlength l + 1).
  change (fun x : Z => 1 <= x < Zlength l + 1)
    with (fun x : Z => 0 + 1 <= x < Zlength l + 1).
  rewrite sum_Z_range_shift_1.
  apply sum_Z_range_ext.
  intros i Hi.
  rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  reflexivity.
Qed.

Lemma sum_Z_range_Znth_cons {A : Type} :
  forall (default a : A) (l : list A) (f : A -> Z),
  sum (fun i => 0 <= i < Zlength (a :: l))
      (fun i => f (Znth i (a :: l) default)) =
  f a +
  sum (fun i => 0 <= i < Zlength l)
      (fun i => f (Znth i l default)).
Proof.
  intros default a l f.
  rewrite (sum_Z_range_Znth_cons_indexed default a l (fun _ x => f x)).
  reflexivity.
Qed.

Lemma sum_Z_range_Znth_app_indexed {A : Type} :
  forall (default : A) (l1 l2 : list A) (F : Z -> A -> Z),
  sum (fun i => 0 <= i < Zlength (l1 ++ l2))
      (fun i => F i (Znth i (l1 ++ l2) default)) =
  sum (fun i => 0 <= i < Zlength l1)
      (fun i => F i (Znth i l1 default)) +
  sum (fun i => 0 <= i < Zlength l2)
      (fun i => F (i + Zlength l1) (Znth i l2 default)).
Proof.
  intros default l1 l2 F.
  pose proof (Zlength_nonneg l1) as Hlen1.
  pose proof (Zlength_nonneg l2) as Hlen2.
  rewrite Zlength_app.
  rewrite (sum_Z_range_split 0 (Zlength l1) (Zlength l1 + Zlength l2)) by lia.
  f_equal.
  - apply sum_Z_range_ext.
    intros i Hi.
    rewrite app_Znth1 by lia.
    reflexivity.
  - pose proof (sum_Z_range_shift 0 (Zlength l2) (Zlength l1)
      (fun i => F i (Znth i (l1 ++ l2) default))) as Hshift.
    change (0 + Zlength l1) with (Zlength l1) in Hshift.
    replace (Zlength l2 + Zlength l1) with (Zlength l1 + Zlength l2) in Hshift by lia.
    rewrite Hshift.
    apply sum_Z_range_ext.
    intros i Hi.
    rewrite app_Znth2 by lia.
    replace (i + Zlength l1 - Zlength l1) with i by lia.
    reflexivity.
Qed.

Lemma sum_Z_range_Znth_app {A : Type} :
  forall (default : A) (l1 l2 : list A) (f : A -> Z),
  sum (fun i => 0 <= i < Zlength (l1 ++ l2))
      (fun i => f (Znth i (l1 ++ l2) default)) =
  sum (fun i => 0 <= i < Zlength l1)
      (fun i => f (Znth i l1 default)) +
  sum (fun i => 0 <= i < Zlength l2)
      (fun i => f (Znth i l2 default)).
Proof.
  intros default l1 l2 f.
  rewrite (sum_Z_range_Znth_app_indexed default l1 l2 (fun _ x => f x)).
  reflexivity.
Qed.

Lemma sum_Z_range_Znth_app_single_indexed {A : Type} :
  forall (default x : A) (l : list A) (F : Z -> A -> Z),
  sum (fun i => 0 <= i < Zlength (l ++ x :: nil))
      (fun i => F i (Znth i (l ++ x :: nil) default)) =
  sum (fun i => 0 <= i < Zlength l)
      (fun i => F i (Znth i l default)) +
  F (Zlength l) x.
Proof.
  intros default x l F.
  rewrite (sum_Z_range_Znth_app_indexed default l (x :: nil) F).
  rewrite Zlength_cons, Zlength_nil.
  rewrite sum_Z_range_single.
  rewrite Znth0_cons.
  replace (0 + Zlength l) with (Zlength l) by lia.
  reflexivity.
Qed.

Lemma sum_Z_range_Znth_app_single {A : Type} :
  forall (default x : A) (l : list A) (f : A -> Z),
  sum (fun i => 0 <= i < Zlength (l ++ x :: nil))
      (fun i => f (Znth i (l ++ x :: nil) default)) =
  sum (fun i => 0 <= i < Zlength l)
      (fun i => f (Znth i l default)) +
  f x.
Proof.
  intros default x l f.
  rewrite (sum_Z_range_Znth_app_single_indexed default x l (fun _ y => f y)).
  reflexivity.
Qed.

Lemma sum_Z_range_Znth_repeat_indexed {A : Type} :
  forall (default x : A) (n : nat) (F : Z -> A -> Z),
  sum (fun i => 0 <= i < Zlength (repeat x n))
      (fun i => F i (Znth i (repeat x n) default)) =
  sum (fun i => 0 <= i < Z.of_nat n)
      (fun i => F i x).
Proof.
  intros default x n F.
  rewrite Zlength_correct, repeat_length.
  apply sum_Z_range_ext.
  intros i Hi.
  rewrite Znth_repeat_lt by lia.
  reflexivity.
Qed.

Lemma sum_Z_range_Znth_repeat {A : Type} :
  forall (default x : A) (n : nat) (f : A -> Z),
  sum (fun i => 0 <= i < Zlength (repeat x n))
      (fun i => f (Znth i (repeat x n) default)) =
  Z.of_nat n * f x.
Proof.
  intros default x n f.
  rewrite (sum_Z_range_Znth_repeat_indexed default x n (fun _ y => f y)).
  rewrite sum_Z_range_const by lia.
  ring.
Qed.

(** ** 与旧 [ListLib.sum] 的桥接 *)

Lemma list_sum_as_Z_range_sum : forall l,
  ListLib.sum l =
  sum (fun i => 0 <= i < Zlength l)
      (fun i => Znth i l 0).
Proof.
  induction l as [|a l IH]; simpl.
  - rewrite Zlength_nil.
    rewrite sum_Z_range_empty by lia.
    reflexivity.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg l) as Hlen.
    rewrite sum_Z_range_cons by lia.
    rewrite Znth0_cons.
    f_equal.
    replace (Z.succ (Zlength l)) with (Zlength l + 1) by lia.
    change 1 with (0 + 1).
    rewrite sum_Z_range_shift_1.
    rewrite IH.
    apply sum_Z_range_ext.
    intros i Hi.
    rewrite Znth_cons by lia.
    replace (i + 1 - 1) with i by lia.
    reflexivity.
Qed.

Lemma list_sum_sublist_as_Z_range_sum : forall l lo hi,
  0 <= lo <= hi ->
  hi <= Zlength l ->
  ListLib.sum (sublist lo hi l) =
  sum (fun i => lo <= i < hi)
      (fun i => Znth i l 0).
Proof.
  intros l lo hi Hlo Hhi.
  rewrite list_sum_as_Z_range_sum.
  rewrite Zlength_sublist by lia.
  transitivity
    (sum (fun i => 0 <= i < hi - lo)
         (fun i => Znth (i + lo) l 0)).
  - apply sum_Z_range_ext.
    intros i Hi.
    rewrite Znth_sublist by lia.
    reflexivity.
  - rewrite <- (sum_Z_range_shift 0 (hi - lo) lo (fun i => Znth i l 0)).
    change (0 + lo) with lo.
    replace (hi - lo + lo) with hi by lia.
    reflexivity.
Qed.

Lemma list_sum_map_as_Z_range_sum {A : Type} :
  forall (default : A) (f : A -> Z) (l : list A),
  ListLib.sum (map f l) =
  sum (fun i => 0 <= i < Zlength l)
      (fun i => f (Znth i l default)).
Proof.
  intros default f l.
  induction l as [|a l IH]; simpl.
  - rewrite Zlength_nil.
    rewrite sum_Z_range_empty by lia.
    reflexivity.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg l) as Hlen.
    rewrite sum_Z_range_cons by lia.
    rewrite Znth0_cons.
    f_equal.
    replace (Z.succ (Zlength l)) with (Zlength l + 1) by lia.
    change 1 with (0 + 1).
    rewrite sum_Z_range_shift_1.
    rewrite IH.
    apply sum_Z_range_ext.
    intros i Hi.
    rewrite Znth_cons by lia.
    replace (i + 1 - 1) with i by lia.
    reflexivity.
Qed.

Lemma list_sum_map_combine_as_Z_range_sum {A B : Type} :
  forall (default_a : A) (default_b : B)
         (f : A -> B -> Z) (l1 : list A) (l2 : list B),
  ListLib.sum (map (fun p => f (fst p) (snd p)) (combine l1 l2)) =
  sum (fun i => 0 <= i < Z.min (Zlength l1) (Zlength l2))
      (fun i => f (Znth i l1 default_a) (Znth i l2 default_b)).
Proof.
  intros default_a default_b f l1.
  induction l1 as [|a l1 IH]; intros [|b l2].
  - simpl combine.
    rewrite !Zlength_nil.
    change (Z.min 0 0) with 0.
    rewrite sum_Z_range_empty by lia.
    reflexivity.
  - rewrite Zlength_nil.
    rewrite Z.min_l by (apply Zlength_nonneg).
    rewrite sum_Z_range_empty by lia.
    reflexivity.
  - simpl combine.
    rewrite Zlength_nil.
    rewrite Z.min_r by (rewrite Zlength_cons; pose proof (Zlength_nonneg l1); lia).
    rewrite sum_Z_range_empty by lia.
    reflexivity.
  - simpl.
    rewrite IH.
    rewrite !Zlength_cons.
    replace (Z.min (Z.succ (Zlength l1)) (Z.succ (Zlength l2)))
      with (Z.min (Zlength l1) (Zlength l2) + 1).
    2: {
      destruct (Z_le_dec (Zlength l1) (Zlength l2)).
      - rewrite !Z.min_l by lia. lia.
      - rewrite !Z.min_r by lia. lia.
    }
    assert (Hmin_nonneg : 0 <= Z.min (Zlength l1) (Zlength l2)).
    {
      destruct (Z_le_dec (Zlength l1) (Zlength l2)).
      - rewrite Z.min_l by lia. apply Zlength_nonneg.
      - rewrite Z.min_r by lia. apply Zlength_nonneg.
    }
    rewrite (sum_Z_range_cons 0 (Z.min (Zlength l1) (Zlength l2) + 1)
      (fun i : Z => f (Znth i (a :: l1) default_a)
                       (Znth i (b :: l2) default_b))) by lia.
    rewrite !Znth0_cons.
    f_equal.
    change 1 with (0 + 1).
    rewrite sum_Z_range_shift_1.
    apply sum_Z_range_ext.
    intros i Hi.
    rewrite !Znth_cons by lia.
    replace (i + 1 - 1) with i by lia.
    reflexivity.
Qed.
