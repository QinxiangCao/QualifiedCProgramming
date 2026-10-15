From AUXLib Require Import ListLib.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition CaveOrderWorks (caves:list(list Z)) (power:Z) : Prop :=
  exists order:list Z, (Permutation order (Zrange 1 ((Zlength caves) + 1))) /\
    forall ci j,0 <= ci < Zlength caves ->
      0 <= j < Zlength (Znth (Znth ci order 1 - 1) caves []) ->
      power + sum_range 0 (ci-1)
        (fun q=>Zlength(Znth(Znth q order 1 - 1)caves[])) + j >
      Znth j (Znth (Znth ci order 1 - 1) caves []) 0.
Definition Pre (caves:list(list Z)) : Prop :=
  (* Every clause below is stated explicitly in the P032 solver Require, which
     therefore omits the Pre(caves) call:
       1 <= Zlength caves <= 100000 /\
       Forall
         (fun c =>
            1 <= Zlength c <= 100000 /\
            Forall (fun x => 1 <= x <= 1000000000) c)
         caves /\
       Zlength (concat caves) <= 100000. *)
  True.
Definition Spec (caves:list(list Z)) (out:Z) : Prop := (min_value_of_subset Z.le (CaveOrderWorks caves) (fun x => x)) out.

(* Representation bridge for the normalized solver, which receives one cave per
   entry of two parallel arrays instead of the jagged cave contents: gains[i] is
   cave i's monster count, and requirements[i] is the least power that clears
   cave i, characterized as an upper bound of a_{i,j} + 1 - j that some j
   attains.  Well defined because every cave is non-empty. *)
Definition CaveSummaryBridge
    (caves : list (list Z)) (requirements gains : list Z) : Prop :=
  Zlength requirements = Zlength caves /\
  Zlength gains = Zlength caves /\
  forall i, 0 <= i < Zlength caves ->
    Znth i gains 0 = Zlength (Znth i caves []) /\
    (forall j, 0 <= j < Zlength (Znth i caves []) ->
       Znth j (Znth i caves []) 0 + 1 - j <= Znth i requirements 0) /\
    (exists j, 0 <= j < Zlength (Znth i caves []) /\
       Znth i requirements 0 = Znth j (Znth i caves []) 0 + 1 - j).

(* The two implementation arrays are one mathematical sequence of cave
   summaries.  Keeping the permutation on [combine] records that every swap
   moves a requirement together with its corresponding gain. *)
Definition ParallelPermutation
    (requirements gains requirements' gains' : list Z) : Prop :=
  Permutation (combine requirements gains) (combine requirements' gains').

Definition HeapParentsFrom (requirements : list Z) (lo hi : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    Znth child requirements 0 <=
    Znth ((child - 1) / 2) requirements 0.

(* During sift-down every heap edge in the relevant suffix is ordered except
   possibly the two edges leaving the current hole. *)
Definition HeapOrderedExceptAtFrom
    (requirements : list Z) (lo hi bad : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    (child - 1) / 2 <> bad ->
    Znth child requirements 0 <=
    Znth ((child - 1) / 2) requirements 0.

Definition SelectedLargerChild
    (requirements : list Z) (root hi child : Z) : Prop :=
  (child = 2 * root + 1 \/ child = 2 * root + 2) /\
  child <= hi /\
  (2 * root + 1 <= hi ->
     Znth (2 * root + 1) requirements 0 <= Znth child requirements 0) /\
  (2 * root + 2 <= hi ->
     Znth (2 * root + 2) requirements 0 <= Znth child requirements 0).

Definition HeapSortState
    (requirements0 gains0 requirements gains : list Z) (hi : Z) : Prop :=
  Zlength requirements = Zlength requirements0 /\
  Zlength gains = Zlength gains0 /\
  ParallelPermutation requirements0 gains0 requirements gains /\
  HeapParentsFrom requirements 0 hi /\
  ListLib.increasing
    (sublist (hi + 1) (Zlength requirements) requirements) /\
  (forall p q,
     0 <= p <= hi ->
     hi < q < Zlength requirements ->
     Znth p requirements 0 <= Znth q requirements 0).

Definition GreedyNeed
    (requirements gains : list Z) (done need : Z) : Prop :=
  0 <= need /\
  (forall k, 0 <= k < done ->
     Znth k requirements 0 - ListLib.sum (sublist 0 k gains) <= need) /\
  (need = 0 \/
   exists k, 0 <= k < done /\
     need = Znth k requirements 0 - ListLib.sum (sublist 0 k gains)).

Definition SortedCaveSummaries
    (caves : list (list Z))
    (requirements0 gains0 requirements gains : list Z) : Prop :=
  CaveSummaryBridge caves requirements0 gains0 /\
  ParallelPermutation requirements0 gains0 requirements gains /\
  ListLib.increasing requirements.

Definition CaveInputBounds (caves : list (list Z)) : Prop :=
  1 <= Zlength caves <= 100000 /\
  (forall i, 0 <= i < Zlength caves ->
     0 < Zlength (Znth i caves []) <= 100000) /\
  Zlength (concat caves) <= 100000 /\
  (forall k, 0 <= k < Zlength (concat caves) ->
     1 <= Znth k (concat caves) 0 <= 1000000000).

Definition CaveSummaryBounds (requirements gains : list Z) : Prop :=
  Zlength requirements = Zlength gains /\
  0 <= ListLib.sum gains <= 100000 /\
  (forall i, 0 <= i < Zlength requirements ->
     1 <= Znth i requirements 0 <= 1000000001 /\
     1 <= Znth i gains 0 <= 100000).

Require Import Coq.micromega.Lia.
Lemma double_replace_suffix__sift_swap :
  forall {A : Type} (l : list A) (vi vj : A) i j lo hi,
    0 <= i < lo ->
    0 <= j < lo ->
    0 <= lo <= hi ->
    hi <= Zlength l ->
    sublist lo hi (replace_Znth j vj (replace_Znth i vi l)) =
    sublist lo hi l.
Proof.
  intros A l vi vj i j lo hi Hi Hj Hlohi Hhi.
  apply (proj2 (list_eq_ext _ _ vi)). split.
  - rewrite !Zlength_sublist by
      (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by
      (repeat rewrite Zlength_replace_Znth; lia).
    rewrite !Znth_sublist by lia.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.
Lemma replace_Znth_swap_form__sift_swap :
  forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros A l1 l2 l3 xi xj.
  pose proof (Zlength_nonneg l2).
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  change (replace_Znth 0 xj (xi :: l2 ++ xj :: l3))
    with (xj :: l2 ++ xj :: l3).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A)
    (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__sift_swap :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < j ->
    j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hij Hj.
  remember (Znth i l d) as xi.
  remember (Znth j l d) as xj.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2: { rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi. reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni. rewrite length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj with (nth nj lr d).
    2: {
      subst nj lr ni. rewrite Heqxj. unfold Znth.
      rewrite nth_skipn.
      assert ((Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat =
              Z.to_nat j).
      {
        apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia. lia.
      }
      rewrite Nat.add_comm, H. reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi :: l2 ++ xj :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace l with (l1 ++ xi :: l2 ++ xj :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2: {
    subst l1 ni. rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2: {
    subst l1 l2 lr ni nj. rewrite !Zlength_correct.
    rewrite !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  rewrite replace_Znth_swap_form__sift_swap.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma replace_nth_comm__sift_swap :
  forall {A : Type} ni nj (l : list A) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni. induction ni as [|ni IH]; intros nj l a b Hneq;
    destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl; [contradiction Hneq; reflexivity | reflexivity].
  - destruct nj; reflexivity.
  - destruct nj; simpl; [reflexivity |].
    f_equal. apply IH. intros Heq. apply Hneq. now f_equal.
Qed.
Lemma permutation_swap_Znth__sift_swap :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hij].
  - apply permutation_swap_Znth_lt__sift_swap; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + assert (Hcomm : forall a b,
        replace_Znth j b (replace_Znth i a l) =
        replace_Znth i a (replace_Znth j b l)).
      {
        intros a b. unfold replace_Znth.
        apply replace_nth_comm__sift_swap. intro Heq.
        apply Z2Nat.inj in Heq; lia.
      }
      rewrite Hcomm.
      apply permutation_swap_Znth_lt__sift_swap; lia.
    + assert (i = j) by lia. subst j.
      rewrite replace_Znth_Znth, replace_Znth_Znth.
      apply Permutation_refl.
Qed.
Lemma combine_replace_Znth_both__sift_swap :
  forall {A B : Type} (xs : list A) (ys : list B) i x y,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    combine (replace_Znth i x xs) (replace_Znth i y ys) =
    replace_Znth i (x, y) (combine xs ys).
Proof.
  intros A B xs. induction xs as [|a xs IH]; intros ys i x y Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|b ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !replace_Znth_cons by lia. simpl. f_equal.
        apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_combine_eq__sift_swap :
  forall {A B : Type} (xs : list A) (ys : list B),
    Zlength xs = Zlength ys ->
    Zlength (combine xs ys) = Zlength xs.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Znth_combine__sift_swap :
  forall {A B : Type} (xs : list A) (ys : list B) i da db,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    Znth i (combine xs ys) (da, db) = (Znth i xs da, Znth i ys db).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys i da db Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma parallel_permutation_swap__sift_swap :
  forall requirements gains requirements_now gains_now root child,
    ParallelPermutation requirements gains requirements_now gains_now ->
    Zlength requirements_now = Zlength gains_now ->
    0 <= root < Zlength requirements_now ->
    0 <= child < Zlength requirements_now ->
    ParallelPermutation requirements gains
      (replace_Znth child (Znth root requirements_now 0)
        (replace_Znth root (Znth child requirements_now 0) requirements_now))
      (replace_Znth child (Znth root gains_now 0)
        (replace_Znth root (Znth child gains_now 0) gains_now)).
Proof.
  intros requirements gains requirements_now gains_now root child
    Hperm Hlen Hroot Hchild.
  unfold ParallelPermutation in *.
  eapply Permutation_trans; [exact Hperm |].
  rewrite combine_replace_Znth_both__sift_swap
    by (repeat rewrite Zlength_replace_Znth; lia).
  rewrite combine_replace_Znth_both__sift_swap
    by lia.
  rewrite <- (@Znth_combine__sift_swap Z Z requirements_now gains_now
    root 0 0 Hlen Hroot).
  rewrite <- (@Znth_combine__sift_swap Z Z requirements_now gains_now
    child 0 0 Hlen Hchild).
  apply permutation_swap_Znth__sift_swap;
    rewrite Zlength_combine_eq__sift_swap by lia; lia.
Qed.
Lemma heap_parent_bounds__sift_swap :
  forall child,
    0 < child ->
    0 <= (child - 1) / 2 < child.
Proof.
  intros child Hchild. split.
  - apply Z_div_nonneg_nonneg; lia.
  - assert ((child - 1) / 2 <= child - 1) by
      (apply Z.div_le_upper_bound; lia).
    lia.
Qed.
Lemma heap_children_characterization__sift_swap :
  forall root child,
    0 <= root ->
    0 < child ->
    (child - 1) / 2 = root ->
    child = 2 * root + 1 \/ child = 2 * root + 2.
Proof.
  intros root child Hroot Hchild Hparent.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hrem.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hquot.
  rewrite Hparent in Hquot.
  assert (Z.modulo (child - 1) 2 = 0 \/ Z.modulo (child - 1) 2 = 1)
    as [Hr | Hr] by lia; lia.
Qed.
Lemma selected_child_parent__sift_swap :
  forall requirements root hi child,
    0 <= root ->
    SelectedLargerChild requirements root hi child ->
    (child - 1) / 2 = root.
Proof.
  intros requirements root hi child Hroot
    [[Hleft | Hright] _]; subst child.
  - replace (2 * root + 1 - 1) with (root * 2) by ring.
    rewrite Z.div_mul by lia. reflexivity.
  - replace (2 * root + 2 - 1) with (root * 2 + 1) by ring.
    pose proof (Z.mod_pos_bound (root * 2 + 1) 2 ltac:(lia)) as Hrem.
    pose proof (Z.div_mod (root * 2 + 1) 2 ltac:(lia)) as Hquot.
    assert (Z.modulo (root * 2 + 1) 2 = 1) by lia. lia.
Qed.
Lemma heap_except_after_selected_swap__sift_swap :
  forall requirements root_pre root hi child,
    0 <= root_pre <= root ->
    root <= hi ->
    hi < Zlength requirements ->
    SelectedLargerChild requirements root hi child ->
    Znth root requirements 0 < Znth child requirements 0 ->
    HeapOrderedExceptAtFrom requirements root_pre hi root ->
    (1 <= root ->
      root_pre <= (root - 1) / 2 ->
      Znth child requirements 0 <=
      Znth ((root - 1) / 2) requirements 0) ->
    HeapOrderedExceptAtFrom
      (replace_Znth child (Znth root requirements 0)
        (replace_Znth root (Znth child requirements 0) requirements))
      root_pre hi child.
Proof.
  intros requirements root_pre root hi child Hroots Hroot_hi Hhi
    Hselected Hrise Hheap Henter.
  destruct Hselected as
    [Hchild_shape [Hchild_hi [Hleft Hright]]].
  assert (Hroot_range : 0 <= root < Zlength requirements) by lia.
  assert (Hchild_parent : (child - 1) / 2 = root).
  {
    apply selected_child_parent__sift_swap with
      (requirements := requirements) (hi := hi).
    - lia.
    - repeat split; assumption.
  }
  assert (Hroot_child : root < child).
  { destruct Hchild_shape as [-> | ->]; lia. }
  assert (Hchild_range : 0 <= child < Zlength requirements) by lia.
  set (swapped :=
    replace_Znth child (Znth root requirements 0)
      (replace_Znth root (Znth child requirements 0) requirements)).
  assert (Hswap_root :
    Znth root swapped 0 = Znth child requirements 0).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by exact Hroot_range.
    reflexivity.
  }
  assert (Hswap_child :
    Znth child swapped 0 = Znth root requirements 0).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth; exact Hchild_range).
    reflexivity.
  }
  assert (Hswap_other : forall k,
    0 <= k < Zlength requirements ->
    k <> root -> k <> child ->
    Znth k swapped 0 = Znth k requirements 0).
  {
    intros k Hk Hkr Hkc. unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  unfold HeapOrderedExceptAtFrom in Hheap |- *.
  intros k Hk Hparent Hparent_not_child.
  pose proof (heap_parent_bounds__sift_swap k ltac:(lia)) as Hp_bounds.
  assert (Hk_range : 0 <= k < Zlength requirements) by lia.
  assert (Hp_range : 0 <= (k - 1) / 2 < Zlength requirements) by lia.
  destruct (Z.eq_dec ((k - 1) / 2) root)
    as [Hparent_root | Hparent_not_root].
  - destruct (Z.eq_dec k child) as [Hk_child | Hk_not_child].
    + subst k. rewrite Hswap_child, Hchild_parent, Hswap_root. lia.
    + assert (Hk_not_root : k <> root) by lia.
      rewrite Hparent_root, Hswap_root.
      rewrite Hswap_other by assumption.
      destruct (heap_children_characterization__sift_swap
        root k ltac:(lia) ltac:(lia) Hparent_root) as [-> | ->].
      * apply Hleft. lia.
      * apply Hright. lia.
  - destruct (Z.eq_dec k root) as [Hk_root | Hk_not_root].
    + subst k.
      rewrite Hswap_root.
      rewrite Hswap_other by (try assumption; lia).
      apply Henter; [lia | exact Hparent].
    + assert (Hk_not_child : k <> child).
      { intro Heq. subst k. apply Hparent_not_root. exact Hchild_parent. }
      rewrite Hswap_other by assumption.
      rewrite Hswap_other by (try assumption; lia).
      apply Hheap; assumption.
Qed.
Lemma selected_swap_descendant_edge__sift_swap :
  forall requirements root_pre root hi child descendant,
    0 <= root_pre <= root ->
    root <= hi ->
    hi < Zlength requirements ->
    SelectedLargerChild requirements root hi child ->
    HeapOrderedExceptAtFrom requirements root_pre hi root ->
    (descendant = 2 * child + 1 \/ descendant = 2 * child + 2) ->
    descendant <= hi ->
    Znth descendant
      (replace_Znth child (Znth root requirements 0)
        (replace_Znth root (Znth child requirements 0) requirements)) 0 <=
    Znth ((child - 1) / 2)
      (replace_Znth child (Znth root requirements 0)
        (replace_Znth root (Znth child requirements 0) requirements)) 0.
Proof.
  intros requirements root_pre root hi child descendant Hroots Hroot_hi Hhi
    Hselected Hheap Hdesc_shape Hdesc_hi.
  assert (Hchild_parent : (child - 1) / 2 = root).
  { eapply selected_child_parent__sift_swap; eauto; lia. }
  assert (Hroot_child : root < child).
  {
    unfold SelectedLargerChild in Hselected.
    destruct Hselected as [[-> | ->] _]; lia.
  }
  assert (Hdesc_parent : (descendant - 1) / 2 = child).
  {
    destruct Hdesc_shape as [-> | ->].
    - replace (2 * child + 1 - 1) with (child * 2) by ring.
      rewrite Z.div_mul by lia. reflexivity.
    - replace (2 * child + 2 - 1) with (child * 2 + 1) by ring.
      pose proof (Z.mod_pos_bound (child * 2 + 1) 2 ltac:(lia)) as Hrem.
      pose proof (Z.div_mod (child * 2 + 1) 2 ltac:(lia)) as Hdiv.
      assert (Z.modulo (child * 2 + 1) 2 = 1) by lia. lia.
  }
  assert (Hroot_range : 0 <= root < Zlength requirements) by lia.
  assert (Hchild_range : 0 <= child < Zlength requirements) by lia.
  assert (Hdesc_range : 0 <= descendant < Zlength requirements) by
    (destruct Hdesc_shape as [-> | ->]; lia).
  pose proof (Hheap descendant ltac:(lia) ltac:(lia) ltac:(lia)) as Hedge.
  rewrite Hdesc_parent in Hedge.
  rewrite Hchild_parent.
  rewrite Znth_replace_Znth_Diff by
    (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff by lia.
  rewrite Znth_replace_Znth_Diff by
    (repeat rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Same by exact Hroot_range.
  exact Hedge.
Qed.
Lemma heap_child_of_parent__sift_returns :
  forall child parent,
    1 <= child ->
    (child - 1) / 2 = parent ->
    child = 2 * parent + 1 \/ child = 2 * parent + 2.
Proof.
  intros child parent Hchild Hparent.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmod.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdecomp.
  rewrite Hparent in Hdecomp.
  assert ((child - 1) mod 2 = 0 \/ (child - 1) mod 2 = 1) by lia.
  destruct H as [H | H]; [left | right]; lia.
Qed.
Lemma heap_parents_after_selected_stop__sift_returns :
  forall requirements lo hi root selected,
    SelectedLargerChild requirements root hi selected ->
    Znth selected requirements 0 <= Znth root requirements 0 ->
    HeapOrderedExceptAtFrom requirements lo hi root ->
    HeapParentsFrom requirements lo hi.
Proof.
  intros requirements lo hi root selected Hselected Hstop Hordered.
  unfold HeapParentsFrom.
  intros current Hcurrent Hlo.
  destruct (Z.eq_dec ((current - 1) / 2) root) as [Hparent | Hparent].
  - rewrite Hparent.
    destruct Hselected as [_ [Hselected_hi [Hleft_max Hright_max]]].
    pose proof (heap_child_of_parent__sift_returns current root
      ltac:(lia) Hparent) as [Hleft | Hright].
    + subst current.
      eapply Z.le_trans; [apply Hleft_max; lia | exact Hstop].
    + subst current.
      eapply Z.le_trans; [apply Hright_max; lia | exact Hstop].
  - unfold HeapOrderedExceptAtFrom in Hordered.
    eapply Hordered; eauto.
Qed.
Lemma heap_parents_after_leaf_stop__sift_returns :
  forall requirements lo hi root,
    2 * root + 1 > hi ->
    HeapOrderedExceptAtFrom requirements lo hi root ->
    HeapParentsFrom requirements lo hi.
Proof.
  intros requirements lo hi root Hleaf Hordered.
  unfold HeapParentsFrom.
  intros current Hcurrent Hlo.
  destruct (Z.eq_dec ((current - 1) / 2) root) as [Hparent | Hparent].
  - pose proof (heap_child_of_parent__sift_returns current root
      ltac:(lia) Hparent) as [Hleft | Hright]; lia.
  - unfold HeapOrderedExceptAtFrom in Hordered.
    eapply Hordered; eauto.
Qed.
Lemma heap_parents_vacuous_above_last_parent__sort_heapify :
  forall requirements n,
    1 <= n ->
    HeapParentsFrom requirements (n / 2) (n - 1).
Proof.
  intros requirements n Hn.
  unfold HeapParentsFrom.
  intros child Hchild Hparent.
  exfalso.
  pose proof (Z.div_mod n 2 ltac:(lia)) as Hdiv_n.
  pose proof (Z.mod_pos_bound n 2 ltac:(lia)) as Hmod_n.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdiv_child.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmod_child.
  lia.
Qed.
Lemma heap_parents_to_ordered_except__sort_heapify :
  forall requirements root hi,
    HeapParentsFrom requirements (root + 1) hi ->
    HeapOrderedExceptAtFrom requirements root hi root.
Proof.
  intros requirements root hi Hparents.
  unfold HeapParentsFrom in Hparents.
  unfold HeapOrderedExceptAtFrom.
  intros child Hchild Hroot Hnot_root.
  apply Hparents; lia.
Qed.
Lemma heapify_exit_state__sort_heapify :
  forall requirements0 gains0 requirements gains n root,
    Zlength requirements0 = n ->
    Zlength gains0 = n ->
    Zlength requirements = n ->
    Zlength gains = n ->
    root < 0 ->
    -1 <= root ->
    ParallelPermutation requirements0 gains0 requirements gains ->
    HeapParentsFrom requirements (root + 1) (n - 1) ->
    HeapSortState requirements0 gains0 requirements gains (n - 1).
Proof.
  intros requirements0 gains0 requirements gains n root
    Hrequirements0 Hgains0 Hrequirements Hgains Hroot_upper Hroot_lower
    Hperm Hparents.
  assert (Hroot : root = -1) by lia.
  subst root.
  unfold HeapSortState.
  split; [lia |].
  split; [lia |].
  split; [exact Hperm |].
  split.
  - replace (-1 + 1) with 0 in Hparents by lia.
    exact Hparents.
  - split.
    + replace (n - 1 + 1) with n by lia.
      rewrite Zsublist_nil by lia.
      exact I.
    + intros p q Hp Hq.
      rewrite Hrequirements in Hq.
      lia.
Qed.
Lemma heap_root_upper_bound__sort_extraction :
  forall requirements hi i,
    HeapParentsFrom requirements 0 hi ->
    0 <= i <= hi ->
    Znth i requirements 0 <= Znth 0 requirements 0.
Proof.
  intros requirements hi i Hheap Hi.
  remember (Z.to_nat i) as ni eqn:Hni.
  assert (Heq : i = Z.of_nat ni).
  { subst ni. symmetry. apply Z2Nat.id. lia. }
  subst i. clear Hni.
  revert Hi.
  induction ni as [ni IH] using lt_wf_ind.
  intros Hi.
  destruct ni as [|ni].
  - simpl. lia.
  - set (child := Z.of_nat (S ni)).
    set (parent := (child - 1) / 2).
    assert (Hchild_pos : 1 <= child) by (subst child; lia).
    assert (Hparent_nonneg : 0 <= parent).
    { subst parent. apply Z.div_pos; lia. }
    assert (Hparent_lt : parent < child).
    { subst parent. apply Z.div_lt_upper_bound; lia. }
    assert (Hparent_nat_lt : (Z.to_nat parent < S ni)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. subst child. lia. }
    specialize (IH (Z.to_nat parent) Hparent_nat_lt).
    assert (Hparent_range : 0 <= Z.of_nat (Z.to_nat parent) <= hi).
    { rewrite Z2Nat.id by lia. subst child. lia. }
    specialize (IH Hparent_range).
    rewrite Z2Nat.id in IH by lia.
    assert (Hchild_hi : child <= hi).
    { unfold child. exact (proj2 Hi). }
    pose proof (Hheap child (conj Hchild_pos Hchild_hi)
      Hparent_nonneg) as Hedge.
    fold parent in Hedge.
    eapply Z.le_trans; eauto.
Qed.
Lemma Znth_swap_root_hi__sort_extraction :
  forall (A : Type) (d : A) (requirements : list A) hi k,
    0 < hi < Zlength requirements ->
    0 <= k < Zlength requirements ->
    Znth k
      (replace_Znth hi (Znth 0 requirements d)
        (replace_Znth 0 (Znth hi requirements d) requirements)) d =
    if Z.eq_dec k 0 then Znth hi requirements d
    else if Z.eq_dec k hi then Znth 0 requirements d
    else Znth k requirements d.
Proof.
  intros A d requirements hi k Hhi Hk.
  destruct (Z.eq_dec k 0) as [-> | Hk0].
  - destruct (Z.eq_dec 0 0); [|contradiction].
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - destruct (Z.eq_dec k 0); [contradiction |].
    destruct (Z.eq_dec k hi) as [-> | Hkhi].
    + destruct (Z.eq_dec hi hi); [|contradiction].
      rewrite Znth_replace_Znth_Same by
        (rewrite Zlength_replace_Znth; lia).
      reflexivity.
    + destruct (Z.eq_dec k hi); [contradiction |].
      rewrite Znth_replace_Znth_Diff by
        (repeat rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity.
Qed.
Lemma heap_extract_cross__sort_extraction :
  forall requirements0 gains0 requirements gains n hi,
    Zlength requirements = n ->
    hi > 0 ->
    hi < n ->
    HeapSortState requirements0 gains0 requirements gains hi ->
    forall p q,
      0 <= p < hi -> hi <= q < n ->
      Znth p
        (replace_Znth hi (Znth 0 requirements 0)
          (replace_Znth 0 (Znth hi requirements 0) requirements)) 0 <=
      Znth q
        (replace_Znth hi (Znth 0 requirements 0)
          (replace_Znth 0 (Znth hi requirements 0) requirements)) 0.
Proof.
  intros requirements0 gains0 requirements gains n hi Hlen Hhi Hhin Hstate p q Hp Hq.
  destruct Hstate as [_ [_ [_ [Hheap [_ Hcross]]]]].
  rewrite !Znth_swap_root_hi__sort_extraction by lia.
  destruct (Z.eq_dec p 0) as [-> | Hp0].
  - destruct (Z.eq_dec 0 0); [|contradiction].
    destruct (Z.eq_dec q 0); [lia |].
    destruct (Z.eq_dec q hi) as [-> | Hqhi].
    + eapply heap_root_upper_bound__sort_extraction; eauto; lia.
    + apply Hcross; lia.
  - destruct (Z.eq_dec p 0); [contradiction |].
    destruct (Z.eq_dec p hi); [lia |].
    destruct (Z.eq_dec q 0); [lia |].
    destruct (Z.eq_dec q hi) as [-> | Hqhi].
    + eapply heap_root_upper_bound__sort_extraction; eauto; lia.
    + apply Hcross; lia.
Qed.
Lemma heap_extract_suffix__sort_extraction :
  forall requirements0 gains0 requirements gains n hi,
    Zlength requirements = n ->
    hi > 0 ->
    hi < n ->
    HeapSortState requirements0 gains0 requirements gains hi ->
    ListLib.increasing
      (sublist hi n
        (replace_Znth hi (Znth 0 requirements 0)
          (replace_Znth 0 (Znth hi requirements 0) requirements))).
Proof.
  intros requirements0 gains0 requirements gains n hi Hlen Hhi Hhin Hstate.
  destruct Hstate as [_ [_ [_ [_ [Hinc Hcross]]]]].
  rewrite Hlen in Hinc.
  apply (proj2 (increasing_iff_chain _)).
  apply (proj2 (mono_chain_iff_index Z.le _)).
  intros i j Hi Hij Hj.
  assert (Hnewlen :
    Zlength
      (replace_Znth hi (Znth 0 requirements 0)
        (replace_Znth 0 (Znth hi requirements 0) requirements)) = n).
  { repeat rewrite Zlength_replace_Znth. exact Hlen. }
  rewrite Zlength_sublist in Hj by lia.
  rewrite !Znth_sublist by lia.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - replace (0 + hi) with hi by lia.
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by
      (try rewrite Zlength_replace_Znth; try lia).
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hcross; lia.
  - assert (Hchain : mono_chain Z.le (sublist (hi + 1) n requirements)).
    { apply (proj1 (increasing_iff_chain _)). exact Hinc. }
    apply (proj1 (mono_chain_iff_index Z.le _))
      with (i := i - 1) (j := j - 1) in Hchain; try lia.
    + rewrite !Znth_sublist in Hchain by lia.
      replace (i - 1 + (hi + 1)) with (i + hi) in Hchain by lia.
      replace (j - 1 + (hi + 1)) with (j + hi) in Hchain by lia.
      rewrite !Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth; try lia).
      exact Hchain.
    + rewrite Zlength_sublist by lia. lia.
Qed.
Lemma heap_extract_except__sort_extraction :
  forall requirements hi,
    Zlength requirements > hi ->
    hi > 0 ->
    HeapParentsFrom requirements 0 hi ->
    HeapOrderedExceptAtFrom
      (replace_Znth hi (Znth 0 requirements 0)
        (replace_Znth 0 (Znth hi requirements 0) requirements))
      0 (hi - 1) 0.
Proof.
  intros requirements hi Hlen Hhi Hheap.
  unfold HeapOrderedExceptAtFrom.
  intros child Hchildlo Hparentlo Hparentneq.
  assert (Hchild : 0 <= child < Zlength requirements) by lia.
  assert (Hparent_child : (child - 1) / 2 < child).
  { apply Z.div_lt_upper_bound; lia. }
  assert (Hparent : 0 <= (child - 1) / 2 < Zlength requirements).
  { split; [exact Hparentlo | lia]. }
  rewrite !Znth_replace_Znth_Diff by
    (repeat rewrite Zlength_replace_Znth; lia).
  apply Hheap; lia.
Qed.
Lemma replace_Znth_swap_form__sort_extraction :
  forall (A : Type) (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj
        (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros A l1 l2 l3 xi xj.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
    xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A)
    (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with
    (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  reflexivity.
Qed.
Lemma permutation_swap_Znth_lt__sort_extraction :
  forall (A : Type) (l : list A) i j (d : A),
    0 <= i < j -> j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d)
        (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hij Hj.
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  { subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2: { rewrite Zlength_correct in Hj; lia. }
    rewrite Heqxi0. reflexivity. }
  assert (Hj_lr : (nj < length lr)%nat).
  { subst nj lr ni. rewrite length_skipn.
    rewrite Zlength_correct in Hj. lia. }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  { subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2: { subst nj lr ni. rewrite Heqxj0. unfold Znth.
      rewrite nth_skipn.
      assert (Hnat :
        (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      { apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia. lia. }
      rewrite Nat.add_comm, Hnat. reflexivity. }
    reflexivity. }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3)
    by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2: { subst l1 ni. rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia. }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2: { subst l1 l2 lr ni nj. rewrite !Zlength_correct.
    rewrite !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj. lia. }
  rewrite replace_Znth_swap_form__sort_extraction.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma Zlength_combine_eq__sort_extraction :
  forall (xs ys : list Z),
    Zlength xs = Zlength ys ->
    Zlength (combine xs ys) = Zlength xs.
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Znth_combine__sort_extraction :
  forall (xs ys : list Z) i,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    Znth i (combine xs ys) (0, 0) = (Znth i xs 0, Znth i ys 0).
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys i Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hi0].
      * simpl. rewrite !Znth0_cons. reflexivity.
      * simpl. rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma combine_swap_root_hi__sort_extraction :
  forall requirements gains hi,
    Zlength requirements = Zlength gains ->
    0 < hi < Zlength requirements ->
    combine
      (replace_Znth hi (Znth 0 requirements 0)
        (replace_Znth 0 (Znth hi requirements 0) requirements))
      (replace_Znth hi (Znth 0 gains 0)
        (replace_Znth 0 (Znth hi gains 0) gains)) =
    replace_Znth hi (Znth 0 (combine requirements gains) (0, 0))
      (replace_Znth 0 (Znth hi (combine requirements gains) (0, 0))
        (combine requirements gains)).
Proof.
  intros requirements gains hi Hlen Hhi.
  apply (proj2 (list_eq_ext _ _ (0, 0))). split.
  - rewrite Zlength_combine_eq__sort_extraction by
      (repeat rewrite Zlength_replace_Znth; exact Hlen).
    repeat rewrite Zlength_replace_Znth.
    symmetry. apply Zlength_combine_eq__sort_extraction. exact Hlen.
  - intros k Hk.
    assert (Hnewlens :
      Zlength
        (replace_Znth hi (Znth 0 requirements 0)
          (replace_Znth 0 (Znth hi requirements 0) requirements)) =
      Zlength
        (replace_Znth hi (Znth 0 gains 0)
          (replace_Znth 0 (Znth hi gains 0) gains))).
    { repeat rewrite Zlength_replace_Znth. exact Hlen. }
    rewrite Zlength_combine_eq__sort_extraction in Hk by exact Hnewlens.
    repeat rewrite Zlength_replace_Znth in Hk.
    rewrite (Znth_combine__sort_extraction _ _ _ Hnewlens
      ltac:(repeat rewrite Zlength_replace_Znth; exact Hk)).
    rewrite !Znth_swap_root_hi__sort_extraction by lia.
    rewrite (@Znth_swap_root_hi__sort_extraction
      (Z * Z) (0, 0) (combine requirements gains) hi k).
    2: { rewrite Zlength_combine_eq__sort_extraction by exact Hlen. lia. }
    2: { rewrite Zlength_combine_eq__sort_extraction by exact Hlen. lia. }
    rewrite !Znth_combine__sort_extraction by
      (first [exact Hlen | lia]).
    destruct (Z.eq_dec k 0); destruct (Z.eq_dec k hi); try lia; reflexivity.
Qed.
Lemma parallel_permutation_swap__sort_extraction :
  forall requirements0 gains0 requirements gains hi,
    Zlength requirements = Zlength gains ->
    0 < hi < Zlength requirements ->
    ParallelPermutation requirements0 gains0 requirements gains ->
    ParallelPermutation requirements0 gains0
      (replace_Znth hi (Znth 0 requirements 0)
        (replace_Znth 0 (Znth hi requirements 0) requirements))
      (replace_Znth hi (Znth 0 gains 0)
        (replace_Znth 0 (Znth hi gains 0) gains)).
Proof.
  intros requirements0 gains0 requirements gains hi Hlen Hhi Hperm.
  unfold ParallelPermutation in *.
  eapply Permutation_trans; [exact Hperm |].
  rewrite combine_swap_root_hi__sort_extraction by assumption.
  apply permutation_swap_Znth_lt__sort_extraction; try lia.
  rewrite Zlength_combine_eq__sort_extraction by exact Hlen. lia.
Qed.
Lemma map_fst_combine__sort_extraction :
  forall (requirements gains : list Z),
    Zlength requirements = Zlength gains ->
    map fst (combine requirements gains) = requirements.
Proof.
  intros requirements. induction requirements as [|r rs IH];
    intros gains Hlen.
  - destruct gains; reflexivity.
  - destruct gains as [|g gs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma parallel_requirements_permutation__sort_extraction :
  forall requirements gains requirements' gains',
    Zlength requirements = Zlength gains ->
    Zlength requirements' = Zlength gains' ->
    ParallelPermutation requirements gains requirements' gains' ->
    Permutation requirements requirements'.
Proof.
  intros requirements gains requirements' gains' Hlen Hlen' Hparallel.
  unfold ParallelPermutation in Hparallel.
  pose proof (Permutation_map fst Hparallel) as Hperm.
  rewrite !map_fst_combine__sort_extraction in Hperm by assumption.
  exact Hperm.
Qed.
Lemma prefix_permutation_from_suffix__sort_extraction :
  forall (before after : list Z) n cut,
    Zlength before = n ->
    Zlength after = n ->
    0 <= cut <= n ->
    Permutation before after ->
    sublist cut n after = sublist cut n before ->
    Permutation (sublist 0 cut before) (sublist 0 cut after).
Proof.
  intros before after n cut Hbefore Hafter Hcut Hperm Hsuffix.
  assert (Hbefore_split :
    before = sublist 0 cut before ++ sublist cut n before).
  { transitivity (sublist 0 n before).
    - symmetry. apply sublist_self. symmetry. exact Hbefore.
    - apply sublist_split; lia. }
  assert (Hafter_split :
    after = sublist 0 cut after ++ sublist cut n after).
  { transitivity (sublist 0 n after).
    - symmetry. apply sublist_self. symmetry. exact Hafter.
    - apply sublist_split; lia. }
  rewrite Hbefore_split, Hafter_split in Hperm.
  rewrite Hsuffix in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.
Lemma cross_preserved_after_sift__sort_extraction :
  forall requirements_now requirements_after n hi,
    Zlength requirements_now = n ->
    Zlength requirements_after = n ->
    1 <= hi <= n ->
    Permutation requirements_now requirements_after ->
    sublist hi n requirements_after = sublist hi n requirements_now ->
    (forall p q,
      0 <= p < hi -> hi <= q < n ->
      Znth p requirements_now 0 <= Znth q requirements_now 0) ->
    forall p q,
      0 <= p < hi -> hi <= q < n ->
      Znth p requirements_after 0 <= Znth q requirements_after 0.
Proof.
  intros requirements_now requirements_after n hi Hnow Hafter Hhi
    Hperm Hsuffix Hcross p q Hp Hq.
  pose proof (prefix_permutation_from_suffix__sort_extraction
    requirements_now requirements_after n hi Hnow Hafter ltac:(lia)
    Hperm Hsuffix) as Hprefixperm.
  assert (Hqeq : Znth q requirements_after 0 =
    Znth q requirements_now 0).
  { pose proof (f_equal (fun l => Znth (q - hi) l 0) Hsuffix) as H.
    cbn in H.
    rewrite !Znth_sublist in H by lia.
    replace (q - hi + hi) with q in H by lia. exact H. }
  assert (Hbefore_forall :
    Forall (fun x => x <= Znth q requirements_now 0)
      (sublist 0 hi requirements_now)).
  { apply (proj2 (Forall_Znth _ 0 _)). intros k Hk.
    rewrite Zlength_sublist0 in Hk by lia.
    rewrite Znth_sublist0 by lia.
    apply Hcross; lia. }
  assert (Hafter_forall :
    Forall (fun x => x <= Znth q requirements_now 0)
      (sublist 0 hi requirements_after)).
  { eapply Permutation_Forall; eauto. }
  apply (proj1 (Forall_Znth _ 0 _)) with (i := p) in Hafter_forall.
  2: { rewrite Zlength_sublist0 by lia. lia. }
  rewrite Znth_sublist0 in Hafter_forall by lia.
  rewrite Hqeq. exact Hafter_forall.
Qed.
Lemma heap_state_after_sift__sort_extraction :
  forall requirements0 gains0 requirements_now gains_now
    requirements_after gains_after n hi,
    Zlength requirements0 = n ->
    Zlength gains0 = n ->
    Zlength requirements_now = n ->
    Zlength gains_now = n ->
    Zlength requirements_after = n ->
    Zlength gains_after = n ->
    1 <= hi <= n ->
    ParallelPermutation requirements0 gains0 requirements_now gains_now ->
    ParallelPermutation requirements_now gains_now
      requirements_after gains_after ->
    HeapParentsFrom requirements_after 0 (hi - 1) ->
    sublist hi n requirements_after = sublist hi n requirements_now ->
    ListLib.increasing (sublist hi n requirements_now) ->
    (forall p q,
      0 <= p < hi -> hi <= q < n ->
      Znth p requirements_now 0 <= Znth q requirements_now 0) ->
    HeapSortState requirements0 gains0 requirements_after gains_after (hi - 1).
Proof.
  intros requirements0 gains0 requirements_now gains_now
    requirements_after gains_after n hi Hreq0 Hgain0 Hreqnow Hgainnow
    Hreqafter Hgainafter Hhi Hperm0 Hperm1 Hheap Hsuffix Hinc Hcross.
  unfold HeapSortState.
  repeat split.
  - lia.
  - lia.
  - unfold ParallelPermutation in *. eapply Permutation_trans; eauto.
  - exact Hheap.
  - replace (hi - 1 + 1) with hi by lia.
    rewrite Hreqafter. rewrite Hsuffix. exact Hinc.
  - intros p q Hp Hq.
    assert (Hreqperm : Permutation requirements_now requirements_after).
    { eapply parallel_requirements_permutation__sort_extraction.
      - rewrite Hreqnow, Hgainnow. reflexivity.
      - rewrite Hreqafter, Hgainafter. reflexivity.
      - exact Hperm1. }
    apply (cross_preserved_after_sift__sort_extraction
      requirements_now requirements_after n hi Hreqnow Hreqafter
      ltac:(lia) Hreqperm Hsuffix Hcross p q ltac:(lia)).
    lia.
Qed.
Lemma heap_state_zero_increasing__sort_extraction :
  forall requirements0 gains0 requirements gains n,
    Zlength requirements = n ->
    1 <= n ->
    HeapSortState requirements0 gains0 requirements gains 0 ->
    ListLib.increasing requirements.
Proof.
  intros requirements0 gains0 requirements gains n Hlen Hn Hstate.
  destruct Hstate as [_ [_ [_ [_ [Hinc Hcross]]]]].
  apply (proj2 (increasing_iff_chain _)).
  apply (proj2 (mono_chain_iff_index Z.le _)).
  intros i j Hi Hij Hj.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - apply Hcross; lia.
  - assert (Hchain : mono_chain Z.le (sublist 1 n requirements)).
    { rewrite <- Hlen. apply (proj1 (increasing_iff_chain _)). exact Hinc. }
    apply (proj1 (mono_chain_iff_index Z.le _))
      with (i := i - 1) (j := j - 1) in Hchain; try lia.
    + rewrite !Znth_sublist in Hchain by lia.
      replace (i - 1 + 1) with i in Hchain by lia.
      replace (j - 1 + 1) with j in Hchain by lia.
      exact Hchain.
    + rewrite Zlength_sublist by lia. lia.
Qed.
Lemma summary_pointwise_bounds__solver_bounds :
  forall requirements gains i,
    CaveSummaryBounds requirements gains ->
    0 <= i < Zlength requirements ->
    Zlength requirements = Zlength gains /\
    1 <= Znth i requirements 0 <= 1000000001 /\
    1 <= Znth i gains 0 <= 100000.
Proof.
  intros requirements gains i [Hlength [_ Hpointwise]] Hi.
  specialize (Hpointwise i Hi).
  tauto.
Qed.
Lemma map_snd_combine__solver_greedy :
  forall (A B : Type) (xs : list A) (ys : list B),
    length xs = length ys ->
    map snd (combine xs ys) = ys.
Proof.
  intros A B xs.
  induction xs as [|x xs IH]; intros ys Hlen; destruct ys; simpl in *;
    try discriminate; auto.
  f_equal. apply IH. lia.
Qed.
Lemma sum_permutation__solver_greedy :
  forall xs ys : list Z,
    Permutation xs ys -> ListLib.sum xs = ListLib.sum ys.
Proof.
  intros xs ys Hperm. induction Hperm; simpl; lia.
Qed.
Lemma sum_map_Zlength_concat__solver_greedy :
  forall xss : list (list Z),
    ListLib.sum (map (@Zlength Z) xss) = Zlength (concat xss).
Proof.
  induction xss as [|xs xss IH]; simpl; auto.
  rewrite Zlength_app. lia.
Qed.
Lemma member_summary_bounds__solver_greedy :
  forall caves requirements gains,
    CaveInputBounds caves ->
    CaveSummaryBridge caves requirements gains ->
    (forall r, In r requirements -> 1 <= r <= 1000000001) /\
    (forall g, In g gains -> 1 <= g <= 100000).
Proof.
  intros caves requirements gains Hinput Hbridge.
  destruct Hinput as [Hcaves_len [Hcave_len [Hflat_len Hflat_bounds]]].
  destruct Hbridge as [Hreq_len [Hgain_len Hsummary]].
  assert (Hflat_forall :
    Forall (fun x => 1 <= x <= 1000000000) (concat caves)).
  {
    apply Forall_forall. intros x Hx.
    apply In_nth with (d := 0) in Hx.
    destruct Hx as [k [Hk Hx]].
    specialize (Hflat_bounds (Z.of_nat k)).
    unfold Znth in Hflat_bounds.
    rewrite Nat2Z.id in Hflat_bounds.
    rewrite <- Hx. apply Hflat_bounds. rewrite Zlength_correct. lia.
  }
  rewrite Forall_forall in Hflat_forall.
  split.
  - intros r Hr.
    apply In_nth with (d := 0) in Hr.
    destruct Hr as [ki [Hki Hr]].
    assert (Hi : 0 <= Z.of_nat ki < Zlength caves).
    { rewrite <- Hreq_len, !Zlength_correct. lia. }
    specialize (Hsummary (Z.of_nat ki) Hi).
    destruct Hsummary as [Hgain [Hupper [j [Hj Hrmax]]]].
    unfold Znth in Hupper, Hrmax.
    rewrite Nat2Z.id in Hupper, Hrmax.
    rewrite Hr in Hupper, Hrmax.
    assert (Hrow_in : In (nth ki caves []) caves).
    { apply nth_In. rewrite !Zlength_correct in Hreq_len. lia. }
    assert (Hfirst_in : In (nth 0 (nth ki caves []) 0) (nth ki caves [])).
    {
      apply nth_In. simpl.
      pose proof (Hcave_len (Z.of_nat ki) Hi) as Hclen.
      unfold Znth in Hclen. rewrite Nat2Z.id in Hclen.
      rewrite Zlength_correct in Hclen. lia.
    }
    assert (Hfirst_flat : In (nth 0 (nth ki caves []) 0) (concat caves)).
    { apply in_concat. exists (nth ki caves []). auto. }
    pose proof (Hflat_forall _ Hfirst_flat) as Hfirst_bounds.
    specialize (Hupper 0).
    assert (Hrow_pos : 0 < Zlength (nth ki caves [])).
    {
      pose proof (Hcave_len (Z.of_nat ki) Hi) as Hclen.
      unfold Znth in Hclen. rewrite Nat2Z.id in Hclen. lia.
    }
    specialize (Hupper ltac:(lia)).
    simpl in Hupper.
    assert (Hj_in : In (nth (Z.to_nat j) (nth ki caves []) 0)
                         (nth ki caves [])).
    {
      apply nth_In. apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia. rewrite <- Zlength_correct.
      unfold Znth in Hj. rewrite Nat2Z.id in Hj. lia.
    }
    assert (Hj_flat : In (nth (Z.to_nat j) (nth ki caves []) 0)
                           (concat caves)).
    { apply in_concat. exists (nth ki caves []). auto. }
    pose proof (Hflat_forall _ Hj_flat) as Hj_bounds.
    lia.
  - intros g Hg.
    apply In_nth with (d := 0) in Hg.
    destruct Hg as [ki [Hki Hg]].
    assert (Hi : 0 <= Z.of_nat ki < Zlength caves).
    { rewrite <- Hgain_len, !Zlength_correct. lia. }
    specialize (Hsummary (Z.of_nat ki) Hi).
    destruct Hsummary as [Hglen _].
    unfold Znth in Hglen. rewrite Nat2Z.id in Hglen. rewrite Hg in Hglen.
    specialize (Hcave_len (Z.of_nat ki) Hi).
    unfold Znth in Hcave_len. rewrite Nat2Z.id in Hcave_len. lia.
Qed.
Lemma summary_bounds_preserved_by_pair_permutation__solver_greedy :
  forall caves requirements gains requirements' gains',
    CaveInputBounds caves ->
    CaveSummaryBridge caves requirements gains ->
    ParallelPermutation requirements gains requirements' gains' ->
    Zlength requirements' = Zlength gains' ->
    CaveSummaryBounds requirements' gains'.
Proof.
  intros caves requirements gains requirements' gains'
    Hinput Hbridge Hperm Houtlen.
  destruct Hbridge as [Hreq_len [Hgain_len Hsummary]].
  assert (Hinlen : length requirements = length gains).
  { rewrite !Zlength_correct in *. lia. }
  assert (Houtlen_nat : length requirements' = length gains').
  { rewrite !Zlength_correct in *. lia. }
  pose proof (member_summary_bounds__solver_greedy caves requirements gains
    Hinput (conj Hreq_len (conj Hgain_len Hsummary))) as [Hreq_bounds Hgain_bounds].
  assert (Hpairs :
    Forall (fun p => 1 <= fst p <= 1000000001 /\
                       1 <= snd p <= 100000)
      (combine requirements gains)).
  {
    apply Forall_forall. intros [r g] Hrg. split.
    - apply Hreq_bounds. eapply in_combine_l; eauto.
    - apply Hgain_bounds. eapply in_combine_r; eauto.
  }
  assert (Hpairs' :
    Forall (fun p => 1 <= fst p <= 1000000001 /\
                       1 <= snd p <= 100000)
      (combine requirements' gains')).
  { eapply Permutation_Forall; eauto. }
  rewrite Forall_forall in Hpairs'.
  assert (Hgains_perm : Permutation gains gains').
  {
    pose proof (Permutation_map snd Hperm) as H.
    rewrite (map_snd_combine__solver_greedy _ _ _ _ Hinlen) in H.
    rewrite (map_snd_combine__solver_greedy _ _ _ _ Houtlen_nat) in H.
    exact H.
  }
  assert (Hgains_eq_lengths : gains = map (@Zlength Z) caves).
  {
    apply nth_ext with (d := 0) (d' := 0).
    - rewrite length_map. rewrite !Zlength_correct in *. lia.
    - intros k Hk.
      specialize (Hsummary (Z.of_nat k)).
      assert (Hki : 0 <= Z.of_nat k < Zlength caves).
      { rewrite <- Hgain_len, !Zlength_correct. lia. }
      specialize (Hsummary Hki). destruct Hsummary as [Hg _].
      unfold Znth in Hg. rewrite Nat2Z.id in Hg.
      change (nth k gains 0 =
        nth k (map (@Zlength Z) caves) ((@Zlength Z) [])).
      rewrite map_nth. exact Hg.
  }
  unfold CaveSummaryBounds. split; [exact Houtlen|]. split.
  - assert (Hsum : ListLib.sum gains = ListLib.sum gains')
      by (eapply sum_permutation__solver_greedy; eauto).
    rewrite <- Hsum, Hgains_eq_lengths,
      sum_map_Zlength_concat__solver_greedy.
    destruct Hinput as [_ [_ [Hflat _]]].
    rewrite Zlength_correct in *. lia.
  - intros i Hi.
    assert (Hpair_in :
      In (Znth i requirements' 0, Znth i gains' 0)
        (combine requirements' gains')).
    {
      unfold Znth.
      assert (Hin : In
        (nth (Z.to_nat i) (combine requirements' gains') (0, 0))
        (combine requirements' gains')).
      {
        apply nth_In. rewrite length_combine.
        rewrite Zlength_correct in Hi. lia.
      }
      rewrite combine_nth in Hin by exact Houtlen_nat. exact Hin.
    }
    pose proof (Hpairs' _ Hpair_in) as Hbounds.
    exact Hbounds.
Qed.
Lemma sum_sublist_snoc__solver_greedy :
  forall xs i,
    0 <= i < Zlength xs ->
    ListLib.sum (sublist 0 (i + 1) xs) =
    ListLib.sum (sublist 0 i xs) + Znth i xs 0.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single 0 i xs) by lia.
  rewrite ListLib.sum_app. simpl. lia.
Qed.
Lemma sum_firstn_le__solver_greedy :
  forall xs n,
    Forall (fun x : Z => 0 <= x) xs ->
    ListLib.sum (firstn n xs) <= ListLib.sum xs.
Proof.
  intros xs n Hnonneg. unfold ListLib.sum. revert n Hnonneg.
  induction xs as [|x xs IH]; intros n Hnonneg.
  - destruct n; simpl; lia.
  - inversion Hnonneg as [|? ? Hx Hxs]; subst. destruct n as [|n].
    + specialize (IH 0%nat Hxs). simpl in IH |- *. lia.
    + simpl. apply Z.add_le_mono_l. apply IH. exact Hxs.
Qed.
Lemma sum_sublist_prefix_le_total__solver_greedy :
  forall xs i,
    Forall (fun x : Z => 0 <= x) xs ->
    ListLib.sum (sublist 0 i xs) <= ListLib.sum xs.
Proof.
  intros xs i Hnonneg. unfold sublist. simpl.
  apply sum_firstn_le__solver_greedy. exact Hnonneg.
Qed.
Lemma greedy_need_step_raise__solver_greedy :
  forall requirements gains i need gained,
    0 <= i ->
    gained = ListLib.sum (sublist 0 i gains) ->
    GreedyNeed requirements gains i need ->
    Znth i requirements 0 - gained > need ->
    GreedyNeed requirements gains (i + 1)
      (Znth i requirements 0 - gained).
Proof.
  intros requirements gains i need gained Hi Hgained Hneed Hraise.
  destruct Hneed as [Hneed0 [Hprefix Hwitness]].
  unfold GreedyNeed. split; [lia|]. split.
  - intros k Hk. destruct (Z.eq_dec k i) as [->|Hne].
    + rewrite <- Hgained. lia.
    + pose proof (Hprefix k ltac:(lia)) as Hkold. lia.
  - right. exists i. split; [lia|]. rewrite Hgained. reflexivity.
Qed.
Lemma greedy_need_step_keep__solver_greedy :
  forall requirements gains i need gained,
    0 <= i ->
    gained = ListLib.sum (sublist 0 i gains) ->
    GreedyNeed requirements gains i need ->
    Znth i requirements 0 - gained <= need ->
    GreedyNeed requirements gains (i + 1) need.
Proof.
  intros requirements gains i need gained Hi Hgained Hneed Hkeep.
  destruct Hneed as [Hneed0 [Hprefix Hwitness]].
  unfold GreedyNeed. split; [exact Hneed0|]. split.
  - intros k Hk. destruct (Z.eq_dec k i) as [->|Hne].
    + rewrite <- Hgained. exact Hkeep.
    + apply Hprefix. lia.
  - destruct Hwitness as [Hzero|[k [Hk Heq]]].
    + left. exact Hzero.
    + right. exists k. split; [lia|exact Heq].
Qed.
Lemma Zlength_map__solver_final : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Permutation_Zlength__solver_final : forall {A : Type} (l1 l2 : list A),
  Permutation l1 l2 -> Zlength l1 = Zlength l2.
Proof.
  intros A l1 l2 Hperm. rewrite !Zlength_correct.
  rewrite (Permutation_length Hperm). reflexivity.
Qed.
Lemma Znth_map__solver_final : forall {A B : Type}
    (f : A -> B) l (da : A) (db : B) i,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l. induction l as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_In__solver_final : forall {A : Type} (l : list A) d i,
  0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l d i Hi. unfold Znth.
  apply nth_In. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma map_sublist0__solver_final : forall {A B : Type}
    (f : A -> B) (l : list A) hi,
  map f (sublist 0 hi l) = sublist 0 hi (map f l).
Proof.
  intros. unfold sublist. simpl. symmetry. apply firstn_map.
Qed.
Lemma map_fst_combine__solver_final : forall (requirements gains : list Z),
  Zlength requirements = Zlength gains ->
  map fst (combine requirements gains) = requirements.
Proof.
  intros requirements. induction requirements as [|r rs IH]; intros gains Hlen.
  - destruct gains; [reflexivity |].
    rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct gains as [|g gs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma map_snd_combine__solver_final : forall (requirements gains : list Z),
  Zlength requirements = Zlength gains ->
  map snd (combine requirements gains) = gains.
Proof.
  intros requirements. induction requirements as [|r rs IH]; intros gains Hlen.
  - destruct gains; [reflexivity |].
    rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct gains as [|g gs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Zlength_combine_eq__solver_final : forall (requirements gains : list Z),
  Zlength requirements = Zlength gains ->
  Zlength (combine requirements gains) = Zlength requirements.
Proof.
  intros requirements. induction requirements as [|r rs IH]; intros gains Hlen.
  - reflexivity.
  - destruct gains as [|g gs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Znth_combine__solver_final : forall (requirements gains : list Z) i,
  Zlength requirements = Zlength gains ->
  0 <= i < Zlength requirements ->
  Znth i (combine requirements gains) (0, 0) =
    (Znth i requirements 0, Znth i gains 0).
Proof.
  intros requirements. induction requirements as [|r rs IH];
    intros gains i Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct gains as [|g gs].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * simpl. rewrite !Znth0_cons. reflexivity.
      * simpl. rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma pair_works_thresholds__solver_final : forall ps power,
  (let fix pair_works (qs : list (Z * Z)) (p : Z) {struct qs} : Prop :=
     match qs with
     | [] => True
     | (requirement, gain) :: tl =>
         requirement <= p /\ pair_works tl (p + gain)
     end
   in pair_works ps power) <->
  (forall k, 0 <= k < Zlength ps ->
    fst (Znth k ps (0, 0)) <=
    power + ListLib.sum (map snd (sublist 0 k ps))).
Proof.
  induction ps as [|[r g] ps IH]; intros power; split.
  - intros _ k Hk. rewrite Zlength_nil in Hk. lia.
  - intros _. exact I.
  - intros [Hr Htail] k Hk.
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + simpl. unfold sublist. simpl. lia.
    + rewrite Zlength_cons in Hk.
      rewrite Znth_cons by lia.
      rewrite sublist_cons1 by lia. simpl.
      pose proof (proj1 (IH (power + g)) Htail) as HtailT.
      specialize (HtailT (k - 1) ltac:(lia)). lia.
  - intros H. split.
    + specialize (H 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg ps); lia)).
      simpl in H. unfold sublist in H. simpl in H. lia.
    + apply (proj2 (IH (power + g))). intros k Hk.
      specialize (H (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in H by lia.
      replace (k + 1 - 1) with k in H by lia.
      rewrite (sublist_cons1 (k + 1) (r, g) ps) in H by lia.
      replace (k + 1 - 1) with k in H by lia.
      simpl in H. lia.
Qed.
Lemma pair_works_move_front__solver_final :
  forall prefix x suffix power,
  (let fix pair_works (qs : list (Z * Z)) (p : Z) {struct qs} : Prop :=
     match qs with
     | [] => True
     | (requirement, gain) :: tl =>
         requirement <= p /\ pair_works tl (p + gain)
     end
   in pair_works (prefix ++ x :: suffix) power) ->
  Forall (fun y => fst x <= fst y) prefix ->
  0 <= snd x ->
  (let fix pair_works (qs : list (Z * Z)) (p : Z) {struct qs} : Prop :=
     match qs with
     | [] => True
     | (requirement, gain) :: tl =>
         requirement <= p /\ pair_works tl (p + gain)
     end
   in pair_works (x :: prefix ++ suffix) power).
Proof.
  induction prefix as [|y prefix IH]; intros [rx gx] suffix power Hwork Hmin Hgx;
    simpl in *.
  - exact Hwork.
  - inversion Hmin as [|? ? Hxy Hmin']; subst.
    destruct y as [ry gy]. simpl in *.
    destruct Hwork as [Hry Hrest].
    specialize (IH (rx, gx) suffix (power + gy) Hrest Hmin' Hgx).
    simpl in IH. destruct IH as [Hrx Htail].
    split; [lia |]. split; [lia |].
    replace (power + gx + gy) with (power + gy + gx) by lia.
    exact Htail.
Qed.
Lemma pair_works_sorted_permutation__solver_final :
  forall target source power,
  mono_nondec (map fst target) ->
  Forall (fun x => 0 <= snd x) target ->
  Permutation source target ->
  (let fix pair_works (qs : list (Z * Z)) (p : Z) {struct qs} : Prop :=
     match qs with
     | [] => True
     | (requirement, gain) :: tl =>
         requirement <= p /\ pair_works tl (p + gain)
     end
   in pair_works source power) ->
  (let fix pair_works (qs : list (Z * Z)) (p : Z) {struct qs} : Prop :=
     match qs with
     | [] => True
     | (requirement, gain) :: tl =>
         requirement <= p /\ pair_works tl (p + gain)
     end
   in pair_works target power).
Proof.
  induction target as [|x xs IH]; intros source power Hsorted Hgains Hperm Hwork.
  - assert (source = []).
    { apply Permutation_nil. apply Permutation_sym. exact Hperm. }
    subst. exact I.
  - simpl in Hsorted.
    apply mono_nondec_cons in Hsorted as [Hxmin Hsorted].
    inversion Hgains as [|? ? Hxgain Hgainstail]; subst.
    destruct (Permutation_vs_cons_inv Hperm) as [l1 [l2 Hsource]].
    subst source.
    assert (Hrestperm : Permutation (l1 ++ l2) xs).
    { apply Permutation_sym. eapply Permutation_cons_app_inv.
      apply Permutation_sym. exact Hperm. }
    assert (Hminprefix : Forall (fun y => fst x <= fst y) l1).
    { rewrite Forall_forall in *. intros y Hy.
      apply Hxmin. apply in_map. eapply Permutation_in; [exact Hrestperm |].
      apply in_or_app. left. exact Hy. }
    pose proof (pair_works_move_front__solver_final
      l1 x l2 power Hwork Hminprefix Hxgain) as Hmoved.
    simpl in Hmoved. destruct x as [rx gx]. simpl in *.
    destruct Hmoved as [Hrx Htail]. split; [exact Hrx |].
    eapply IH; eauto.
Qed.
Lemma Zlength_Zrange_aux__solver_final : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__solver_final : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__solver_final. lia.
Qed.
Lemma Znth_Zrange_aux__solver_final : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__solver_final : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__solver_final by lia. lia.
Qed.
Lemma Zrange_shift_plus__solver_final : forall n,
  0 <= n -> map (fun i => i + 1) (Zrange 0 n) = Zrange 1 (n + 1).
Proof.
  intros n Hn. apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite Zlength_map__solver_final, !Zlength_Zrange__solver_final by lia. lia.
  - intros i Hi. rewrite Zlength_map__solver_final,
      Zlength_Zrange__solver_final in Hi by lia.
    rewrite (@Znth_map__solver_final Z Z (fun i => i + 1)
      (Zrange 0 n) 0 0 i) by
      (rewrite Zlength_Zrange__solver_final by lia; lia).
    rewrite !Znth_Zrange__solver_final by lia. lia.
Qed.
Lemma Zrange_shift_minus__solver_final : forall n,
  0 <= n -> map (fun i => i - 1) (Zrange 1 (n + 1)) = Zrange 0 n.
Proof.
  intros n Hn. apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite Zlength_map__solver_final, !Zlength_Zrange__solver_final by lia. lia.
  - intros i Hi. rewrite Zlength_map__solver_final,
      Zlength_Zrange__solver_final in Hi by lia.
    rewrite (@Znth_map__solver_final Z Z (fun i => i - 1)
      (Zrange 1 (n + 1)) 0 0 i) by
      (rewrite Zlength_Zrange__solver_final by lia; lia).
    rewrite !Znth_Zrange__solver_final by lia. lia.
Qed.
Lemma map_plus_after_minus__solver_final : forall l : list Z,
  map (fun i => i + 1) (map (fun i => i - 1) l) = l.
Proof.
  induction l as [|x xs IH]; simpl; [reflexivity |].
  f_equal; [lia | exact IH].
Qed.
Lemma combine_as_indexed_pairs__solver_final : forall requirements gains,
  Zlength requirements = Zlength gains ->
  combine requirements gains =
  map (fun i => (Znth i requirements 0, Znth i gains 0))
      (Zrange 0 (Zlength requirements)).
Proof.
  intros requirements gains Hlen.
  apply (proj2 (list_eq_ext _ _ (0, 0))). split.
  - rewrite Zlength_combine_eq__solver_final by exact Hlen.
    rewrite Zlength_map__solver_final, Zlength_Zrange__solver_final;
      pose proof (Zlength_nonneg requirements); lia.
  - intros i Hi.
    rewrite Zlength_combine_eq__solver_final in Hi by exact Hlen.
    rewrite Znth_combine__solver_final by assumption.
    rewrite (@Znth_map__solver_final Z (Z * Z)
      (fun i => (Znth i requirements 0, Znth i gains 0))
      (Zrange 0 (Zlength requirements)) 0 (0, 0) i).
    + rewrite Znth_Zrange__solver_final by
        (pose proof (Zlength_nonneg requirements); lia).
      reflexivity.
    + rewrite Zlength_Zrange__solver_final;
        pose proof (Zlength_nonneg requirements); lia.
Qed.
Lemma prefix_gains_match_caves__solver_final :
  forall caves requirements gains idxs ci,
  CaveSummaryBridge caves requirements gains ->
  Permutation idxs (Zrange 0 (Zlength caves)) ->
  0 <= ci <= Zlength caves ->
  ListLib.sum
    (map snd
      (sublist 0 ci
        (map (fun i => (Znth i requirements 0, Znth i gains 0)) idxs))) =
  sum_range 0 (ci - 1)
    (fun q =>
       Zlength
         (Znth (Znth q (map (fun i => i + 1) idxs) 1 - 1) caves [])).
Proof.
  intros caves requirements gains idxs ci Hbridge Hperm Hci.
  destruct Hbridge as [Hreq [Hgain Hbridge]].
  assert (Hidxlen : Zlength idxs = Zlength caves).
  { rewrite (Permutation_Zlength__solver_final _ _ Hperm).
    rewrite Zlength_Zrange__solver_final by
      (pose proof (Zlength_nonneg caves); lia). lia. }
  rewrite map_sublist0__solver_final, map_map. simpl.
  rewrite list_sum_sublist_as_Z_range_sum.
  2: { lia. }
  2: { rewrite Zlength_map__solver_final, Hidxlen. lia. }
  unfold sum_range. replace (ci - 1 + 1) with ci by lia.
  apply sum_Z_range_ext. intros q Hq.
  rewrite (@Znth_map__solver_final Z Z (fun i => Znth i gains 0)
    idxs 0 0 q) by (rewrite Hidxlen; lia).
  rewrite (@Znth_map__solver_final Z Z (fun i => i + 1)
    idxs 0 1 q) by (rewrite Hidxlen; lia).
  set (idx := Znth q idxs 0).
  assert (Hidx : 0 <= idx < Zlength caves).
  { apply In_Zrange. eapply Permutation_in.
    - exact Hperm.
    - apply Znth_In__solver_final. rewrite Hidxlen. lia. }
  specialize (Hbridge idx Hidx) as [Hgi _].
  replace (idx + 1 - 1) with idx by lia. exact Hgi.
Qed.
Lemma indexed_thresholds_make_cave_order__solver_final :
  forall caves requirements gains idxs power,
  CaveSummaryBridge caves requirements gains ->
  Permutation idxs (Zrange 0 (Zlength caves)) ->
  (forall k, 0 <= k < Zlength
      (map (fun i => (Znth i requirements 0, Znth i gains 0)) idxs) ->
    fst (Znth k
      (map (fun i => (Znth i requirements 0, Znth i gains 0)) idxs) (0, 0)) <=
    power + ListLib.sum (map snd (sublist 0 k
      (map (fun i => (Znth i requirements 0, Znth i gains 0)) idxs)))) ->
  CaveOrderWorks caves power.
Proof.
  intros caves requirements gains idxs power Hbridge Hperm Hthreshold.
  exists (map (fun i => i + 1) idxs). split.
  - eapply Permutation_trans.
    + apply Permutation_map. exact Hperm.
    + rewrite Zrange_shift_plus__solver_final by
        (pose proof (Zlength_nonneg caves); lia). apply Permutation_refl.
  - intros ci j Hci Hj.
    assert (Hidxlen : Zlength idxs = Zlength caves).
    { rewrite (Permutation_Zlength__solver_final _ _ Hperm).
      rewrite Zlength_Zrange__solver_final by
        (pose proof (Zlength_nonneg caves); lia). lia. }
    specialize (Hthreshold ci).
    rewrite Zlength_map__solver_final in Hthreshold.
    specialize (Hthreshold ltac:(rewrite Hidxlen; lia)).
    rewrite (@Znth_map__solver_final Z (Z * Z)
      (fun i => (Znth i requirements 0, Znth i gains 0))
      idxs 0 (0, 0) ci) in Hthreshold by (rewrite Hidxlen; lia).
    set (idx := Znth ci idxs 0) in *.
    assert (Hidx : 0 <= idx < Zlength caves).
    { apply In_Zrange. eapply Permutation_in.
      - exact Hperm.
      - apply Znth_In__solver_final. rewrite Hidxlen. lia. }
    destruct Hbridge as [Hreq [Hgain Hbridge]].
    pose proof (Hbridge idx Hidx) as [Hgi [Hupper Hattain]].
    specialize (Hupper j).
    rewrite (@Znth_map__solver_final Z Z (fun i => i + 1)
      idxs 0 1 ci) in Hj |- * by (rewrite Hidxlen; lia).
    replace (Znth ci idxs 0 + 1 - 1) with idx in Hj by (unfold idx; lia).
    replace (Znth ci idxs 0 + 1 - 1) with idx in |- * by (unfold idx; lia).
    specialize (Hupper Hj).
    pose proof (prefix_gains_match_caves__solver_final
      caves requirements gains idxs ci (conj Hreq (conj Hgain Hbridge))
      Hperm ltac:(lia)) as Hprefix.
    assert (Hreqpower : Znth idx requirements 0 <=
      power + sum_range 0 (ci - 1)
        (fun q => Zlength
          (Znth (Znth q (map (fun i => i + 1) idxs) 1 - 1) caves []))).
    { simpl in Hthreshold. rewrite Hprefix in Hthreshold. exact Hthreshold. }
    assert (Hmonster : Znth j (Znth idx caves []) 0 <
      Znth idx requirements 0 + j) by lia.
    assert (Hpowered : Znth idx requirements 0 + j <=
      power + sum_range 0 (ci - 1)
        (fun q => Zlength
          (Znth (Znth q (map (fun i => i + 1) idxs) 1 - 1) caves [])) + j)
      by lia.
    Z.swap_greater. eapply Z.lt_le_trans; eauto.
Qed.
Lemma cave_order_gives_indexed_thresholds__solver_final :
  forall caves requirements gains power,
  CaveSummaryBridge caves requirements gains ->
  CaveOrderWorks caves power ->
  exists idxs,
    Permutation idxs (Zrange 0 (Zlength caves)) /\
    (forall k, 0 <= k < Zlength
        (map (fun i => (Znth i requirements 0, Znth i gains 0)) idxs) ->
      fst (Znth k
        (map (fun i => (Znth i requirements 0, Znth i gains 0)) idxs) (0, 0)) <=
      power + ListLib.sum (map snd (sublist 0 k
        (map (fun i => (Znth i requirements 0, Znth i gains 0)) idxs)))).
Proof.
  intros caves requirements gains power Hbridge [order [Horder Hworks]].
  exists (map (fun i => i - 1) order). split.
  - eapply Permutation_trans.
    + apply Permutation_map. exact Horder.
    + rewrite Zrange_shift_minus__solver_final by
        (pose proof (Zlength_nonneg caves); lia). apply Permutation_refl.
  - intros ci Hci.
    assert (Horderlen : Zlength order = Zlength caves).
    { rewrite (Permutation_Zlength__solver_final _ _ Horder).
      rewrite Zlength_Zrange__solver_final by
        (pose proof (Zlength_nonneg caves); lia). lia. }
    rewrite Zlength_map__solver_final in Hci.
    set (idxs := map (fun i => i - 1) order).
    fold idxs in Hci.
    assert (Hidxperm : Permutation idxs (Zrange 0 (Zlength caves))).
    { subst idxs. eapply Permutation_trans.
      - apply Permutation_map. exact Horder.
      - rewrite Zrange_shift_minus__solver_final by
          (pose proof (Zlength_nonneg caves); lia). apply Permutation_refl. }
    assert (Hidxlen : Zlength idxs = Zlength caves).
    { rewrite (Permutation_Zlength__solver_final _ _ Hidxperm).
      rewrite Zlength_Zrange__solver_final by
        (pose proof (Zlength_nonneg caves); lia). lia. }
    rewrite (@Znth_map__solver_final Z (Z * Z)
      (fun i => (Znth i requirements 0, Znth i gains 0))
      idxs 0 (0, 0) ci) by (rewrite Hidxlen; lia).
    set (idx := Znth ci idxs 0).
    assert (Hidx : 0 <= idx < Zlength caves).
    { apply In_Zrange. eapply Permutation_in.
      - exact Hidxperm.
      - apply Znth_In__solver_final. rewrite Hidxlen. lia. }
    destruct Hbridge as [Hreq [Hgain Hbridge]].
    pose proof (Hbridge idx Hidx) as [Hgi [Hupper [j [Hj Hreqattain]]]].
    specialize (Hworks ci j ltac:(lia)).
    assert (Hordernth : Znth ci order 1 = idx + 1).
    { subst idxs idx.
      rewrite (@Znth_map__solver_final Z Z (fun i => i - 1)
        order 1 0 ci) by (rewrite Horderlen; lia). lia. }
    specialize (Hworks ltac:(rewrite Hordernth; replace (idx + 1 - 1) with idx by lia; exact Hj)).
    pose proof (prefix_gains_match_caves__solver_final
      caves requirements gains idxs ci (conj Hreq (conj Hgain Hbridge))
      Hidxperm ltac:(lia)) as Hprefix.
    assert (Horderback : map (fun i => i + 1) idxs = order).
    { subst idxs. apply map_plus_after_minus__solver_final. }
    rewrite Horderback in Hprefix.
    rewrite Hprefix. simpl. rewrite Hreqattain.
    rewrite Hordernth in Hworks. replace (idx + 1 - 1) with idx in Hworks by lia.
    apply Z.gt_lt in Hworks.
    lia.
Qed.
Lemma sorted_greedy_need_characterizes_spec__solver_final :
  forall caves requirements0 gains0 requirements gains need,
  CaveInputBounds caves ->
  SortedCaveSummaries caves requirements0 gains0 requirements gains ->
  CaveSummaryBounds requirements gains ->
  GreedyNeed requirements gains (Zlength caves) need ->
  Spec caves need.
Proof.
  intros caves requirements0 gains0 requirements gains need
    Hinput Hsorted Hbounds Hgreedy.
  destruct Hsorted as [Hbridge0 [Hparallel Hincreasing]].
  destruct Hbridge0 as [Hreq0 [Hgain0 Hbridge0]].
  destruct Hbounds as [Hlen [Hsum Hentry]].
  assert (Hreq : Zlength requirements = Zlength caves).
  { unfold ParallelPermutation in Hparallel.
    pose proof (Permutation_length Hparallel).
    rewrite !length_combine in H.
    rewrite !Zlength_correct in Hreq0, Hgain0, Hlen |- *.
    lia. }
  assert (Hgain : Zlength gains = Zlength caves) by lia.
  set (target := combine requirements gains).
  assert (Htarget_indexed : exists idxs,
    target = map (fun i => (Znth i requirements0 0, Znth i gains0 0)) idxs /\
    Permutation idxs (Zrange 0 (Zlength caves))).
  { assert (Horig : combine requirements0 gains0 =
        map (fun i => (Znth i requirements0 0, Znth i gains0 0))
          (Zrange 0 (Zlength caves))).
    { rewrite <- Hreq0. apply combine_as_indexed_pairs__solver_final. lia. }
    assert (HP : Permutation target
      (map (fun i => (Znth i requirements0 0, Znth i gains0 0))
        (Zrange 0 (Zlength caves)))).
    { eapply Permutation_trans.
      - apply Permutation_sym. exact Hparallel.
      - rewrite <- Horig. apply Permutation_refl. }
    destruct (@Permutation_map_inv Z (Z * Z)
      (fun i => (Znth i requirements0 0, Znth i gains0 0))
      target (Zrange 0 (Zlength caves)) HP)
      as [idxs [Heq Hidx]].
    exists idxs. split; [exact Heq | apply Permutation_sym; exact Hidx]. }
  assert (Htarget_thresholds : forall k, 0 <= k < Zlength target ->
    fst (Znth k target (0, 0)) <=
    need + ListLib.sum (map snd (sublist 0 k target))).
  { intros k Hk. subst target.
    rewrite Zlength_combine_eq__solver_final in Hk by exact Hlen.
    rewrite Znth_combine__solver_final by assumption. simpl.
    rewrite map_sublist0__solver_final, map_snd_combine__solver_final by exact Hlen.
    destruct Hgreedy as [Hneed [Hmax Hwit]].
    specialize (Hmax k ltac:(rewrite <- Hreq; exact Hk)). lia. }
  unfold Spec, min_value_of_subset, min_object_of_subset. exists need. split.
  - split.
    + destruct Htarget_indexed as [idxs [Htargeteq Hidxperm]].
      eapply indexed_thresholds_make_cave_order__solver_final.
      * exact (conj Hreq0 (conj Hgain0 Hbridge0)).
      * exact Hidxperm.
      * rewrite <- Htargeteq. exact Htarget_thresholds.
    + intros power Hpower.
      destruct (cave_order_gives_indexed_thresholds__solver_final
        caves requirements0 gains0 power
        (conj Hreq0 (conj Hgain0 Hbridge0)) Hpower)
        as [idxs [Hidxperm Hsource_thresholds]].
      set (source := map
        (fun i => (Znth i requirements0 0, Znth i gains0 0)) idxs).
      assert (Hsource_target : Permutation source target).
      { assert (Horig : combine requirements0 gains0 =
          map (fun i => (Znth i requirements0 0, Znth i gains0 0))
            (Zrange 0 (Zlength caves))).
        { rewrite <- Hreq0. apply combine_as_indexed_pairs__solver_final. lia. }
        eapply Permutation_trans.
        - subst source. apply Permutation_map. exact Hidxperm.
        - eapply Permutation_trans.
          + rewrite <- Horig. apply Permutation_refl.
          + exact Hparallel. }
      assert (Htarget_sorted : mono_nondec (map fst target)).
      { subst target. rewrite map_fst_combine__solver_final by exact Hlen.
        apply (proj2 (mono_nondec_iff_increasing requirements)). exact Hincreasing. }
      assert (Htarget_gains : Forall (fun x => 0 <= snd x) target).
      { subst target. rewrite Forall_forall. intros [r g] Hin.
        assert (HgIn : In g gains).
        { rewrite <- (map_snd_combine__solver_final requirements gains Hlen).
          apply in_map with (f := snd) in Hin. simpl in Hin. exact Hin. }
        apply In_nth with (d := 0) in HgIn as [n [Hn Hg]].
        assert (Hlen_nat : length requirements = length gains).
        { apply Nat2Z.inj. rewrite <- !Zlength_correct. exact Hlen. }
        specialize (Hentry (Z.of_nat n) ltac:(rewrite Zlength_correct, Hlen_nat; lia)).
        unfold Znth in Hentry.
        rewrite Nat2Z.id in Hentry. rewrite Hg in Hentry. simpl. lia. }
      pose proof (proj2 (pair_works_thresholds__solver_final source power)
        Hsource_thresholds) as Hsource_work.
      pose proof (pair_works_sorted_permutation__solver_final
        target source power Htarget_sorted Htarget_gains Hsource_target
        Hsource_work) as Htarget_work0.
      pose proof (proj1 (pair_works_thresholds__solver_final target power)
        Htarget_work0) as Htarget_work.
      destruct Hgreedy as [Hneed [Hmax Hwit]]. destruct Hwit as [-> | [k [Hk Heq]]].
      * assert (Hk0 : 0 <= 0 < Zlength target).
        { subst target. rewrite Zlength_combine_eq__solver_final by exact Hlen.
          rewrite Hreq. destruct Hinput as [Hn _]. lia. }
        specialize (Htarget_work 0 Hk0).
        subst target.
        assert (H0req : 0 <= 0 < Zlength requirements).
        { rewrite <- (Zlength_combine_eq__solver_final requirements gains Hlen).
          exact Hk0. }
        rewrite (Znth_combine__solver_final requirements gains 0 Hlen H0req)
          in Htarget_work.
        simpl in Htarget_work. unfold sublist in Htarget_work. simpl in Htarget_work.
        specialize (Hentry 0 ltac:(rewrite Hreq; destruct Hinput as [Hn _]; lia)). lia.
      * assert (Hktarget : 0 <= k < Zlength target).
        { subst target. rewrite Zlength_combine_eq__solver_final by exact Hlen.
          rewrite Hreq. exact Hk. }
        specialize (Htarget_work k Hktarget).
        subst target.
        assert (Hkreq : 0 <= k < Zlength requirements).
        { rewrite <- (Zlength_combine_eq__solver_final requirements gains Hlen).
          exact Hktarget. }
        rewrite (Znth_combine__solver_final requirements gains k Hlen Hkreq)
          in Htarget_work.
        simpl in Htarget_work.
        rewrite map_sublist0__solver_final,
          map_snd_combine__solver_final in Htarget_work by exact Hlen.
        lia.
  - reflexivity.
Qed.
