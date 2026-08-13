Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import MonadLib.MonadErr.StateRelMonadErr.

Local Open Scope Z_scope.
Import ListNotations.

Export MonadNotation.
Local Open Scope monad.

Definition elem := Z.

Record uf_state := {
  uf_size : Z;
  uf_parent : elem -> elem;
  uf_rank : elem -> Z;
}.

Definition valid (s : uf_state) (x : elem) : Prop :=
  0 <= x < uf_size s.

Definition same_class (repr_of : elem -> elem) (x y : elem) : Prop :=
  repr_of x = repr_of y.

Definition parent_closed (s : uf_state) : Prop :=
  forall x, valid s x -> valid s (uf_parent s x).

Definition rank_nonnegative (s : uf_state) : Prop :=
  forall x, valid s x -> 0 <= uf_rank s x.

Definition rank_increases_along_parent (s : uf_state) : Prop :=
  forall x, valid s x -> uf_parent s x <> x ->
    uf_rank s x < uf_rank s (uf_parent s x).

Definition uf_inv (s : uf_state) : Prop :=
  parent_closed s /\
  rank_nonnegative s /\
  rank_increases_along_parent s.

Inductive parent_chain (s : uf_state) : elem -> elem -> Prop :=
| parent_chain_refl :
    forall x,
      valid s x ->
      parent_chain s x x
| parent_chain_step :
    forall x y z,
      valid s x ->
      uf_parent s x = y ->
      parent_chain s y z ->
      parent_chain s x z.

Definition root_of (s : uf_state) (x r : elem) : Prop :=
  valid s x /\
  parent_chain s x r /\
  valid s r /\
  uf_parent s r = r.

Definition legal (s : uf_state) (repr_of : elem -> elem) : Prop :=
  forall x, valid s x ->
    valid s (repr_of x) /\
    repr_of (repr_of x) = repr_of x.

Definition enum_elems (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

Fixpoint count_if (l : list Z) (P : Z -> bool) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if P x then 1 else 0) + count_if xs P
  end.

Definition class_test (repr_of : elem -> elem) (r z : elem) : bool :=
  if Z.eq_dec (repr_of z) r then true else false.

Definition class_size (s : uf_state) (repr_of : elem -> elem) (r : elem) : Z :=
  count_if (enum_elems (uf_size s)) (class_test repr_of r).

Definition root_rank_lt_class_size (s : uf_state) (repr_of : elem -> elem) : Prop :=
  forall r, valid s r -> repr_of r = r -> uf_rank s r < class_size s repr_of r.

Definition uf_models (s : uf_state) (repr_of : elem -> elem) : Prop :=
  forall x, valid s x -> root_of s x (repr_of x).

Definition uf_abstract (s : uf_state) (repr_of : elem -> elem) : Prop :=
  legal s repr_of /\
  uf_inv s /\
  uf_models s repr_of /\
  root_rank_lt_class_size s repr_of.

Definition merge
  (D : elem -> Prop)
  (repr_of : elem -> elem)
  (x y : elem)
  (repr_of' : elem -> elem) : Prop :=
  forall a b, D a -> D b ->
    same_class repr_of' a b <->
      same_class repr_of a b \/
      (same_class repr_of a x /\ same_class repr_of b y) \/
      (same_class repr_of a y /\ same_class repr_of b x).

Definition set_parent_state (x p : elem) (s : uf_state) : uf_state :=
  {|
    uf_size := uf_size s;
    uf_parent := fun z => if Z.eq_dec z x then p else uf_parent s z;
    uf_rank := uf_rank s;
  |}.

Definition set_rank_state (x k : elem) (s : uf_state) : uf_state :=
  {|
    uf_size := uf_size s;
    uf_parent := uf_parent s;
    uf_rank := fun z => if Z.eq_dec z x then k else uf_rank s z;
  |}.

Definition inc_rank_state (x : elem) (s : uf_state) : uf_state :=
  set_rank_state x (uf_rank s x + 1) s.

Definition parent_write_safe (s : uf_state) (x p : elem) : Prop :=
  valid s x /\ valid s p.

Definition rank_bump_safe (s : uf_state) (x : elem) : Prop :=
  valid s x /\
  0 <= uf_rank s x /\
  uf_rank s x + 1 <= uf_size s.

Section union_find_programs.

Definition read_parent (x : elem) : program uf_state elem :=
  p <- (assertS (fun s => valid s x);;
        get' (fun s => uf_parent s x));;
  assertS (fun s => valid s p);;
  ret p.

Definition read_rank (x : elem) : program uf_state Z :=
  assertS (fun s => valid s x);;
  get' (fun s => uf_rank s x).

Definition write_parent (x p : elem) : program uf_state unit :=
  assertS (fun s => parent_write_safe s x p);;
  update' (set_parent_state x p).

Definition bump_rank (x : elem) : program uf_state unit :=
  assertS (fun s => rank_bump_safe s x);;
  update' (inc_rank_state x).

Definition uf_find_f
  (W : elem -> program uf_state elem)
  : elem -> program uf_state elem :=
  fun x =>
    p <- read_parent x;;
    choice
      (assume!! (p = x);;
       ret x)
      (assume!! (p <> x);;
       y <- W p;;
       write_parent x y;;
       ret y).

Definition uf_find : elem -> program uf_state elem :=
  BW_fix uf_find_f.

Definition uf_union (x y : elem) : program uf_state unit :=
  rx <- uf_find x;;
  ry <- uf_find y;;
  choice
    (assume!! (rx = ry);;
     ret tt)
    (assume!! (rx <> ry);;
     rx_rank <- read_rank rx;;
     ry_rank <- read_rank ry;;
     choice
       (assume!! (ry_rank < rx_rank);;
        write_parent ry rx)
       (choice
          (assume!! (rx_rank < ry_rank);;
           write_parent rx ry)
          (assume!! (rx_rank = ry_rank);;
           write_parent rx ry;;
           bump_rank ry))).

End union_find_programs.

Section union_find_specs.

Definition uf_find_spec (x : elem) : Prop :=
  forall repr_of,
    Hoare
      (fun s => uf_abstract s repr_of /\ valid s x)
      (uf_find x)
      (fun y s =>
         y = repr_of x /\
         uf_abstract s repr_of).

Definition uf_union_spec (x y : elem) : Prop :=
  forall repr_of,
    Hoare
      (fun s => uf_abstract s repr_of /\ valid s x /\ valid s y)
      (uf_union x y)
      (fun _ s =>
         exists repr_of',
           uf_abstract s repr_of' /\
           merge (valid s) repr_of x y repr_of').

End union_find_specs.

Section union_find_proofs.

Lemma uf_abstract_legal :
  forall s repr_of,
    uf_abstract s repr_of ->
    legal s repr_of.
Proof. firstorder. Qed.

Lemma uf_abstract_inv :
  forall s repr_of,
    uf_abstract s repr_of ->
    uf_inv s.
Proof. firstorder. Qed.

Lemma uf_abstract_models :
  forall s repr_of,
    uf_abstract s repr_of ->
    uf_models s repr_of.
Proof. firstorder. Qed.

Lemma uf_abstract_rank_class_bound :
  forall s repr_of,
    uf_abstract s repr_of ->
    root_rank_lt_class_size s repr_of.
Proof. firstorder. Qed.

Lemma uf_inv_parent_closed :
  forall s,
    uf_inv s ->
    parent_closed s.
Proof. firstorder. Qed.

Lemma uf_inv_rank_nonnegative :
  forall s,
    uf_inv s ->
    rank_nonnegative s.
Proof. firstorder. Qed.

Lemma uf_inv_rank_increases :
  forall s,
    uf_inv s ->
    rank_increases_along_parent s.
Proof. firstorder. Qed.

Lemma legal_repr_valid :
  forall s repr_of x,
    legal s repr_of ->
    valid s x ->
    valid s (repr_of x).
Proof. firstorder. Qed.

Lemma legal_repr_idem :
  forall s repr_of x,
    legal s repr_of ->
    valid s x ->
    repr_of (repr_of x) = repr_of x.
Proof. firstorder. Qed.

Lemma enum_elems_length :
  forall n,
    0 <= n ->
    length (enum_elems n) = Z.to_nat n.
Proof.
  intros n Hn.
  unfold enum_elems.
  rewrite length_map, length_seq.
  reflexivity.
Qed.

Lemma enum_elems_In :
  forall n z,
    0 <= z < n ->
    In z (enum_elems n).
Proof.
  intros n z Hz.
  unfold enum_elems.
  apply in_map_iff.
  exists (Z.to_nat z).
  split.
  - rewrite Z2Nat.id by lia.
    reflexivity.
  - apply in_seq.
    split.
    + lia.
    + apply Z2Nat.inj_lt; lia.
Qed.

Lemma count_if_nonnegative :
  forall l P,
    0 <= count_if l P.
Proof.
  induction l as [| x xs IH]; intros P; simpl.
  - lia.
  - specialize (IH P).
    destruct (P x); lia.
Qed.

Lemma count_if_le_length :
  forall l P,
    count_if l P <= Z.of_nat (length l).
Proof.
  induction l as [| x xs IH]; intros P; simpl.
  - lia.
  - specialize (IH P).
    destruct (P x); nia.
Qed.

Lemma count_if_contains :
  forall l P x,
    In x l ->
    P x = true ->
    1 <= count_if l P.
Proof.
  induction l as [| a l IH]; intros P x Hin HP; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + rewrite HP.
      pose proof (count_if_nonnegative l P).
      lia.
    + specialize (IH P x Hin HP).
      destruct (P a) eqn:Ha.
      * pose proof (count_if_nonnegative l P). lia.
      * pose proof (count_if_nonnegative l P). lia.
Qed.

Lemma count_if_ext :
  forall l P Q,
    (forall x, In x l -> P x = Q x) ->
    count_if l P = count_if l Q.
Proof.
  induction l as [| a l IH]; intros P Q Heq; simpl.
  - reflexivity.
  - assert (P a = Q a) as Hhead.
    { apply Heq. left. reflexivity. }
    assert (count_if l P = count_if l Q) as Htail.
    {
      apply IH.
      intros x Hin.
      apply Heq.
      right. exact Hin.
    }
    rewrite Hhead, Htail.
    reflexivity.
Qed.

Lemma count_if_or_disjoint :
  forall l P Q,
    (forall x, In x l -> P x = true -> Q x = true -> False) ->
    count_if l (fun x => orb (P x) (Q x)) = count_if l P + count_if l Q.
Proof.
  induction l as [| a l IH]; intros P Q Hdisj; simpl.
  - reflexivity.
  - assert (Htail :
      forall x : Z, In x l -> P x = true -> Q x = true -> False).
    {
      intros x Hin HP HQ.
      eapply Hdisj; eauto.
      right. exact Hin.
    }
    specialize (IH P Q Htail).
    destruct (P a) eqn:HPa; destruct (Q a) eqn:HQa; simpl in *.
    + exfalso.
      eapply (Hdisj a); [left; reflexivity | exact HPa | exact HQa].
    + rewrite IH.
      change (1 + (count_if l P + count_if l Q) =
              1 + count_if l P + count_if l Q).
      lia.
    + rewrite IH.
      change (1 + (count_if l P + count_if l Q) =
              count_if l P + (1 + count_if l Q)).
      lia.
    + exact IH.
Qed.

Lemma class_size_upper :
  forall s repr_of r,
    0 <= uf_size s ->
    class_size s repr_of r <= uf_size s.
Proof.
  intros s repr_of r Hsize.
  unfold class_size.
  apply (Z.le_trans _ (Z.of_nat (length (enum_elems (uf_size s))))).
  - apply count_if_le_length.
  - rewrite enum_elems_length by exact Hsize.
    rewrite Z2Nat.id by exact Hsize.
    lia.
Qed.

Lemma class_size_root_positive :
  forall s repr_of r,
    valid s r ->
    repr_of r = r ->
    1 <= class_size s repr_of r.
Proof.
  intros s repr_of r Hr_valid Hr_root.
  unfold class_size, valid in *.
  apply (count_if_contains
           (enum_elems (uf_size s))
           (class_test repr_of r)
           r).
  - apply enum_elems_In.
    exact Hr_valid.
  - unfold class_test.
    destruct (Z.eq_dec (repr_of r) r); [reflexivity | congruence].
Qed.

Lemma parent_chain_valid_end :
  forall s x y,
    parent_chain s x y ->
    valid s y.
Proof.
  intros s x y Hchain.
  induction Hchain; auto.
Qed.

Lemma parent_chain_from_root :
  forall s x y,
    parent_chain s x y ->
    uf_parent s x = x ->
    y = x.
Proof.
  intros s x y Hchain.
  induction Hchain; intros Hroot.
  - reflexivity.
  - rewrite Hroot in H0. subst y.
    auto.
Qed.

Lemma parent_chain_root_unique :
  forall s x r1 r2,
    parent_chain s x r1 ->
    uf_parent s r1 = r1 ->
    parent_chain s x r2 ->
    uf_parent s r2 = r2 ->
    r1 = r2.
Proof.
  intros s x r1 r2 Hchain1.
  revert r2.
  induction Hchain1 as [x Hvalidx | x y r1 Hvalidx Hxy Hchain1 IH];
    intros r2 Hroot1 Hchain2 Hroot2.
  - apply parent_chain_from_root in Hchain2; auto.
  - inversion Hchain2 as [x0 Hvalid0 | x0 y0 r20 Hvalid0 Hxy0 Hchain20].
    + subst x0 r2.
      rewrite Hroot2 in Hxy. subst y.
      apply parent_chain_from_root in Hchain1; auto.
    + subst x0 r20.
      rewrite Hxy in Hxy0. inversion Hxy0. subst y0.
      eapply IH; eauto.
Qed.

Lemma root_of_unique :
  forall s x r1 r2,
    root_of s x r1 ->
    root_of s x r2 ->
    r1 = r2.
Proof.
  intros s x r1 r2 [_ [Hchain1 [_ Hroot1]]] [_ [Hchain2 [_ Hroot2]]].
  eapply parent_chain_root_unique; eauto.
Qed.

Lemma root_chain_tail :
  forall s x r,
    parent_chain s x r ->
    uf_parent s r = r ->
    uf_parent s x <> x ->
    parent_chain s (uf_parent s x) r.
Proof.
  intros s x r Hchain Hroot Hneq.
  inversion Hchain as [x0 Hvalid0 | x0 y0 r0 Hvalid0 Hxy Hchain0].
  - subst x0 r.
    exfalso. apply Hneq. exact Hroot.
  - subst x0 r0.
    rewrite Hxy.
    exact Hchain0.
Qed.

Lemma repr_of_parent :
  forall s repr_of x,
    uf_abstract s repr_of ->
    valid s x ->
    uf_parent s x <> x ->
    repr_of (uf_parent s x) = repr_of x.
Proof.
  intros s repr_of x Habs Hvalid Hneq.
  pose proof (uf_abstract_models _ _ Habs x Hvalid) as Hroot_x_full.
  pose proof (uf_inv_parent_closed _ (uf_abstract_inv _ _ Habs) x Hvalid) as Hvalid_p.
  pose proof (uf_abstract_models _ _ Habs (uf_parent s x) Hvalid_p) as Hroot_p_full.
  destruct Hroot_x_full as [_ [Hchain_x [Hvalid_rx Hroot_x]]].
  destruct Hvalid_p as [Hvalid_p_l Hvalid_p_r].
  destruct Hvalid_rx as [Hvalid_rx_l Hvalid_rx_r].
  assert (parent_chain s (uf_parent s x) (repr_of x)) as Htail.
  { eapply root_chain_tail; eauto. }
  eapply (root_of_unique s (uf_parent s x));
    [exact Hroot_p_full | repeat split; eauto; lia].
Qed.

Lemma rank_le_along_chain :
  forall s x y,
    uf_inv s ->
    parent_chain s x y ->
    uf_rank s x <= uf_rank s y.
Proof.
  intros s x y Hinv Hchain.
  pose proof (uf_inv_rank_increases _ Hinv) as Hinc.
  induction Hchain as [x Hvalidx | x z y Hvalidx Hxz Hchain IH].
  - lia.
  - destruct (Z.eq_dec z x) as [-> | Hneq].
    + exact IH.
    + assert (uf_parent s x <> x) as Hparent_neq.
      { rewrite Hxz. exact Hneq. }
      specialize (Hinc x Hvalidx Hparent_neq).
      rewrite Hxz in Hinc.
      lia.
Qed.

Lemma rank_lt_along_chain_to_root :
  forall s x r,
    uf_inv s ->
    parent_chain s x r ->
    uf_parent s r = r ->
    x <> r ->
    uf_rank s x < uf_rank s r.
Proof.
  intros s x r Hinv Hchain.
  pose proof (uf_inv_rank_increases _ Hinv) as Hinc.
  induction Hchain as [x Hvalidx | x y r Hvalidx Hxy Hchain IH];
    intros Hroot Hneq.
  - contradiction.
  - destruct (Z.eq_dec y x) as [-> | Hneq_xy].
    + apply IH; auto.
    + assert (uf_parent s x <> x) as Hparent_neq.
      { rewrite Hxy. exact Hneq_xy. }
      specialize (Hinc x Hvalidx Hparent_neq).
      rewrite Hxy in Hinc.
      assert (uf_rank s y <= uf_rank s r) by (eapply rank_le_along_chain; eauto).
      lia.
Qed.

Lemma repr_of_root :
  forall s repr_of x,
    uf_abstract s repr_of ->
    valid s x ->
    uf_parent s x = x ->
    repr_of x = x.
Proof.
  intros s repr_of x Habs Hvalid Hroot.
  pose proof Hvalid as Hvalid0.
  destruct Hvalid as [Hvalid_l Hvalid_r].
  eapply (root_of_unique s x).
  - exact (uf_abstract_models _ _ Habs x Hvalid0).
  - repeat split; eauto using parent_chain_refl; lia.
Qed.

Lemma valid_set_parent_state :
  forall s x p z,
    valid (set_parent_state x p s) z <-> valid s z.
Proof.
  intros s x p z.
  unfold valid, set_parent_state; simpl.
  tauto.
Qed.

Lemma uf_parent_set_parent_eq :
  forall s x p,
    uf_parent (set_parent_state x p s) x = p.
Proof.
  intros s x p.
  unfold set_parent_state; simpl.
  destruct (Z.eq_dec x x); congruence.
Qed.

Lemma uf_parent_set_parent_neq :
  forall s x p z,
    z <> x ->
    uf_parent (set_parent_state x p s) z = uf_parent s z.
Proof.
  intros s x p z Hneq.
  unfold set_parent_state; simpl.
  destruct (Z.eq_dec z x); congruence.
Qed.

Lemma uf_rank_set_parent_state :
  forall s x p z,
    uf_rank (set_parent_state x p s) z = uf_rank s z.
Proof.
  reflexivity.
Qed.

Lemma parent_chain_compress_preserve :
  forall s x rx z r,
    parent_chain s x rx ->
    uf_parent s rx = rx ->
    parent_chain s z r ->
    uf_parent s r = r ->
    parent_chain (set_parent_state x rx s) z r.
Proof.
  intros s x rx z r Hchain_x Hroot_rx Hchain_z.
  revert x rx Hchain_x Hroot_rx.
  induction Hchain_z as [z Hvalidz | z y r Hvalidz Hzy Hchain_z IH];
    intros x rx Hchain_x Hroot_rx Hroot_r.
  - apply parent_chain_refl.
    unfold valid in *; simpl in *; exact Hvalidz.
  - destruct (Z.eq_dec z x) as [-> | Hneq].
    + assert (parent_chain s x r) as Hchain_xr.
      { eapply parent_chain_step; eauto. }
      assert (rx = r) by (eapply parent_chain_root_unique; eauto).
      subst r.
      eapply parent_chain_step.
      * unfold valid in *; simpl in *; exact Hvalidz.
      * rewrite uf_parent_set_parent_eq. reflexivity.
      * apply parent_chain_refl.
        eapply parent_chain_valid_end; eauto.
    + eapply parent_chain_step.
      * unfold valid in *; simpl in *; exact Hvalidz.
      * rewrite uf_parent_set_parent_neq; eauto.
      * apply IH; eauto.
Qed.

Lemma repr_root_preserved_by_compress :
  forall s repr_of x z,
    uf_abstract s repr_of ->
    valid s x ->
    valid s z ->
    uf_parent (set_parent_state x (repr_of x) s) (repr_of z) = repr_of z.
Proof.
  intros s repr_of x z Habs Hvalidx Hvalidz.
  destruct (Z.eq_dec (repr_of z) x) as [Heq | Hneq].
  - rewrite Heq.
    rewrite uf_parent_set_parent_eq.
    pose proof (legal_repr_idem _ _ z (uf_abstract_legal _ _ Habs) Hvalidz) as Hid.
    rewrite Heq in Hid.
    exact Hid.
  - rewrite uf_parent_set_parent_neq; auto.
    destruct (uf_abstract_models _ _ Habs z Hvalidz) as [_ [_ [_ Hroot]]].
    exact Hroot.
Qed.

Lemma uf_abstract_compress :
  forall s repr_of x,
    uf_abstract s repr_of ->
    valid s x ->
    uf_abstract (set_parent_state x (repr_of x) s) repr_of.
Proof.
  intros s repr_of x Habs Hvalidx.
  destruct Habs as [Hlegal [Hinv [Hmodels Hrank_bound]]].
  split.
  - intros a Hva.
    unfold valid in *; simpl in *.
    exact (Hlegal a Hva).
  - split.
    + split.
      * intros a Hva.
        destruct (Z.eq_dec a x) as [-> | Hneq].
        -- rewrite uf_parent_set_parent_eq.
           pose proof (legal_repr_valid _ _ x Hlegal Hvalidx) as Hvalid_repr.
           unfold valid in Hvalid_repr |- *; simpl in *.
           exact Hvalid_repr.
        -- rewrite uf_parent_set_parent_neq; auto.
           pose proof (uf_inv_parent_closed _ Hinv a Hva) as Hvalid_parent.
           unfold valid in Hvalid_parent; simpl in Hvalid_parent.
           exact Hvalid_parent.
      * split.
        -- intros a Hva.
           unfold valid in *; simpl in *.
           eapply uf_inv_rank_nonnegative; [exact Hinv | exact Hva].
        -- intros a Hva Hneq_new.
           destruct (Z.eq_dec a x) as [-> | Hneq_ax].
           ++ rewrite uf_parent_set_parent_eq in Hneq_new.
              destruct (Hmodels x Hvalidx) as [_ [Hchain_x [_ Hroot_x]]].
              assert (x <> repr_of x) as Hneq_repr by congruence.
              unfold set_parent_state; simpl.
              destruct (Z.eq_dec x x) as [_ | Habsurd]; [| contradiction].
              eapply rank_lt_along_chain_to_root;
                [exact Hinv | exact Hchain_x | exact Hroot_x | exact Hneq_repr].
           ++ rewrite uf_parent_set_parent_neq in Hneq_new by auto.
              unfold set_parent_state; simpl.
              destruct (Z.eq_dec a x) as [Habsurd | _]; [contradiction|].
              eapply uf_inv_rank_increases; [exact Hinv | exact Hva | exact Hneq_new].
    + split.
      * intros a Hva.
        assert (Hva_old : valid s a).
        { unfold valid in *; simpl in *; exact Hva. }
        pose proof (Hmodels a Hva_old) as Hroot_a.
        pose proof (Hmodels x Hvalidx) as Hroot_x.
        destruct Hroot_a as [_ [Hchain_a [Hvalid_ra Hroot_ra]]].
        destruct Hroot_x as [_ [Hchain_x [_ Hroot_x]]].
        destruct Hvalid_ra as [Hvalid_ra_l Hvalid_ra_r].
        split.
        -- exact Hva_old.
        -- split.
           ++ eapply parent_chain_compress_preserve;
                [exact Hchain_x | exact Hroot_x | exact Hchain_a | exact Hroot_ra].
           ++ split.
              ** split; [exact Hvalid_ra_l | exact Hvalid_ra_r].
              ** eapply repr_root_preserved_by_compress;
                   [split; [exact Hlegal | split; [exact Hinv | split; [exact Hmodels | exact Hrank_bound]]]
                   | exact Hvalidx
                   | exact Hva_old].
      * intros r Hr_valid Hr_root.
        unfold valid in Hr_valid |- *; simpl in *.
        unfold set_parent_state; simpl.
        exact (Hrank_bound r Hr_valid Hr_root).
Qed.

Lemma valid_from_size :
  forall s n x,
    uf_size s = n ->
    0 <= x < n ->
    valid s x.
Proof.
  intros s n x Hsize Hrange.
  unfold valid.
  lia.
Qed.

Lemma uf_size_set_parent_state :
  forall s x p,
    uf_size (set_parent_state x p s) = uf_size s.
Proof.
  reflexivity.
Qed.

Lemma read_parent_rule :
  forall (P : uf_state -> Prop) x,
    (forall s, P s -> valid s x) ->
    (forall s, P s -> valid s (uf_parent s x)) ->
    Hoare P (read_parent x)
      (fun p s => p = uf_parent s x /\ valid s p /\ P s).
Proof.
  intros P x Hx Hparent.
  unfold read_parent.
  eapply Hoare_bind with (Q := fun p s => p = uf_parent s x /\ P s).
  - apply Hoare_assertS_bind.
    + auto.
    + unfold get'.
      eapply Hoare_cons_post.
      2: apply Hoare_get.
      intros p s [Hp HP].
      split; auto.
  - intros p.
    apply Hoare_assertS_bind.
    + intros s [Hp HP].
      rewrite Hp.
      apply Hparent; auto.
    + apply Hoare_ret.
      intros s [Hp HP].
      split; [exact Hp |].
      split.
      * rewrite Hp. apply Hparent; auto.
      * exact HP.
Qed.

Lemma read_rank_rule :
  forall (P : uf_state -> Prop) x,
    (forall s, P s -> valid s x) ->
    Hoare P (read_rank x)
      (fun k s => k = uf_rank s x /\ P s).
Proof.
  intros P x Hx.
  unfold read_rank.
  apply Hoare_assertS_bind.
  - auto.
  - unfold get'.
    eapply Hoare_cons_post.
    2: apply Hoare_get.
    intros k s [Hk HP].
    split; auto.
Qed.

Lemma write_parent_rule :
  forall (P : uf_state -> Prop) x p,
    (forall s, P s -> parent_write_safe s x p) ->
    Hoare P (write_parent x p)
      (fun _ s => exists s0, s = set_parent_state x p s0 /\ P s0).
Proof.
  intros P x p Hsafe.
  unfold write_parent.
  apply Hoare_assertS_bind.
  - auto.
  - unfold update'.
    eapply Hoare_cons_post.
    2: apply Hoare_update.
    intros [] s [s0 [Hs HP]].
    exists s0; split; auto.
Qed.

Lemma bump_rank_rule :
  forall (P : uf_state -> Prop) x,
    (forall s, P s -> rank_bump_safe s x) ->
    Hoare P (bump_rank x)
      (fun _ s => exists s0, s = inc_rank_state x s0 /\ P s0).
Proof.
  intros P x Hsafe.
  unfold bump_rank.
  apply Hoare_assertS_bind.
  - auto.
  - unfold update'.
    apply (@Hoare_cons_post unit uf_state
             P
             (update' (inc_rank_state x))
             (fun _ s => exists s0, s = inc_rank_state x s0 /\ P s0)
             (fun _ s => exists s0, s = inc_rank_state x s0 /\ P s0)).
    + intros [] s H.
      exact H.
    + apply Hoare_update.
Qed.

Lemma write_parent_compress_ret_rule :
  forall a y orig n repr_of (keep : elem -> Prop),
    Hoare
      (fun s =>
         y = repr_of orig /\
         uf_abstract s repr_of /\
         uf_size s = n /\
         0 <= orig < n /\
         (forall z, keep z \/ z = a -> repr_of z = repr_of orig /\ 0 <= z < n))
      (write_parent a y ;; ret y)
      (fun b s =>
         b = repr_of orig /\
         uf_abstract s repr_of /\
         uf_size s = n /\
         0 <= orig < n /\
         (forall z, keep z -> repr_of z = repr_of orig /\ 0 <= z < n)).
Proof.
  intros a y orig n repr_of keep.
  apply (@Hoare_bind unit elem uf_state
           (fun s =>
              y = repr_of orig /\
              uf_abstract s repr_of /\
              uf_size s = n /\
              0 <= orig < n /\
              (forall z : elem,
                  keep z \/ z = a ->
                  repr_of z = repr_of orig /\ 0 <= z < n))
           (fun _ s =>
              y = repr_of orig /\
              uf_abstract s repr_of /\
              uf_size s = n /\
              0 <= orig < n /\
              (forall z : elem,
                  keep z ->
                  repr_of z = repr_of orig /\ 0 <= z < n))
           (fun b s =>
              b = repr_of orig /\
              uf_abstract s repr_of /\
              uf_size s = n /\
              0 <= orig < n /\
              (forall z : elem,
                  keep z ->
                  repr_of z = repr_of orig /\ 0 <= z < n))
           (write_parent a y)
           (fun _ => ret y)).
  - apply (@Hoare_cons_post unit uf_state
             (fun s =>
                y = repr_of orig /\
                uf_abstract s repr_of /\
                uf_size s = n /\
                0 <= orig < n /\
                (forall z : elem,
                    keep z \/ z = a ->
                    repr_of z = repr_of orig /\ 0 <= z < n))
             (write_parent a y)
             (fun _ s =>
                exists s0,
                  s = set_parent_state a y s0 /\
                  y = repr_of orig /\
                  uf_abstract s0 repr_of /\
                  uf_size s0 = n /\
                  0 <= orig < n /\
                  (forall z : elem,
                      keep z \/ z = a ->
                      repr_of z = repr_of orig /\ 0 <= z < n))
             (fun _ s =>
                y = repr_of orig /\
                uf_abstract s repr_of /\
                uf_size s = n /\
                0 <= orig < n /\
                (forall z : elem,
                    keep z ->
                    repr_of z = repr_of orig /\ 0 <= z < n))).
    + intros [] s [s0 [Hs [Hy [Habs [Hsize [Hrange Hkeep]]]]]].
      subst s.
      assert (Ha_info : repr_of a = repr_of orig /\ 0 <= a < n)
        by exact (Hkeep a (or_intror eq_refl)).
      destruct Ha_info as [Hrepr_a Ha_range].
      split; [exact Hy |].
      split.
      * rewrite Hy.
        rewrite <- Hrepr_a.
        apply (uf_abstract_compress s0 repr_of a Habs
                 (valid_from_size s0 n a Hsize Ha_range)).
      * split.
        -- rewrite uf_size_set_parent_state.
           exact Hsize.
        -- split; [exact Hrange |].
           intros z Hz.
           exact (Hkeep z (or_introl Hz)).
    + apply (write_parent_rule
               (fun s =>
                  y = repr_of orig /\
                  uf_abstract s repr_of /\
                  uf_size s = n /\
                  0 <= orig < n /\
                  (forall z : elem,
                      keep z \/ z = a ->
                      repr_of z = repr_of orig /\ 0 <= z < n))
               a y).
      intros s [Hy [Habs [Hsize [Hrange Hkeep]]]].
      unfold parent_write_safe.
      split.
      * destruct (Hkeep a (or_intror eq_refl)) as [_ Ha_range].
        exact (valid_from_size s n a Hsize Ha_range).
      * rewrite Hy.
        apply (legal_repr_valid s repr_of orig
                 (uf_abstract_legal s repr_of Habs)
                 (valid_from_size s n orig Hsize Hrange)).
  - intros [].
    apply Hoare_ret.
    intros s H.
    exact H.
Qed.

Theorem uf_find_strong :
  forall x orig n repr_of (keep : elem -> Prop),
    Hoare
      (fun s =>
         uf_abstract s repr_of /\
         valid s x /\
         repr_of x = repr_of orig /\
         uf_size s = n /\
         0 <= orig < n /\
         forall z, keep z -> repr_of z = repr_of orig /\ 0 <= z < n)
      (uf_find x)
      (fun y s =>
         y = repr_of orig /\
         uf_abstract s repr_of /\
         uf_size s = n /\
         0 <= orig < n /\
         forall z, keep z -> repr_of z = repr_of orig /\ 0 <= z < n).
Proof.
  intros x orig n repr_of keep.
  apply (@Hoare_BW_fix_logicv uf_state elem elem
           (elem * (Z * (elem -> Prop)))
           uf_find_f
           (fun a c s =>
              let '(orig0, (n0, keep0)) := c in
              uf_abstract s repr_of /\
              valid s a /\
              repr_of a = repr_of orig0 /\
              uf_size s = n0 /\
              0 <= orig0 < n0 /\
              forall z : elem,
                keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
           (fun _ c b s =>
              let '(orig0, (n0, keep0)) := c in
              b = repr_of orig0 /\
              uf_abstract s repr_of /\
              uf_size s = n0 /\
              0 <= orig0 < n0 /\
              forall z : elem,
                keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
           x (orig, (n, keep))).
  intros W IH a [orig0 [n0 keep0]].
  unfold uf_find_f.
  apply (@Hoare_bind elem elem uf_state
           (fun s =>
              uf_abstract s repr_of /\
              valid s a /\
              repr_of a = repr_of orig0 /\
              uf_size s = n0 /\
              0 <= orig0 < n0 /\
              forall z : elem,
                keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
           (fun p s =>
              p = uf_parent s a /\
              valid s p /\
              uf_abstract s repr_of /\
              valid s a /\
              repr_of a = repr_of orig0 /\
              uf_size s = n0 /\
              0 <= orig0 < n0 /\
              forall z : elem,
                keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
           (fun b s =>
              b = repr_of orig0 /\
              uf_abstract s repr_of /\
              uf_size s = n0 /\
              0 <= orig0 < n0 /\
              forall z : elem,
                keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
           (read_parent a)
           (fun p =>
              choice
                (assume!! (p = a);; ret a)
                (assume!! (p <> a);;
                 y <- W p;;
                 write_parent a y;;
                 ret y))).
  - apply (read_parent_rule
             (fun s =>
                uf_abstract s repr_of /\
                valid s a /\
                repr_of a = repr_of orig0 /\
                uf_size s = n0 /\
                0 <= orig0 < n0 /\
                forall z : elem,
                  keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
             a).
    + intros s [_ [Hva _]].
      exact Hva.
    + intros s [Habs [Hva _]].
      apply (uf_inv_parent_closed s (uf_abstract_inv s repr_of Habs) a Hva).
  - intros p.
    apply Hoare_choice.
    + apply Hoare_assume_bind.
      intros Hp_root.
      apply Hoare_ret.
      intros s [Hp [Hvp [Habs [Hva [Heq [Hsize [Hrange Hkeep]]]]]]].
      assert (Hroot : uf_parent s a = a).
      { transitivity p.
        - symmetry.
          exact Hp.
        - exact Hp_root. }
      split.
      * rewrite <- Heq.
        symmetry.
        apply (repr_of_root s repr_of a Habs Hva Hroot).
      * split; [exact Habs |].
        split; [exact Hsize |].
        split; [exact Hrange | exact Hkeep].
    + apply Hoare_assume_bind.
      intros Hp_neq.
      apply (@Hoare_bind elem elem uf_state
               (fun s =>
                  p = uf_parent s a /\
                  valid s p /\
                  uf_abstract s repr_of /\
                  valid s a /\
                  repr_of a = repr_of orig0 /\
                  uf_size s = n0 /\
                  0 <= orig0 < n0 /\
                  forall z : elem,
                    keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
               (fun y s =>
                  y = repr_of orig0 /\
                  uf_abstract s repr_of /\
                  uf_size s = n0 /\
                  0 <= orig0 < n0 /\
                  forall z : elem,
                    keep0 z \/ z = a ->
                    repr_of z = repr_of orig0 /\ 0 <= z < n0)
               (fun b s =>
                  b = repr_of orig0 /\
                  uf_abstract s repr_of /\
                  uf_size s = n0 /\
                  0 <= orig0 < n0 /\
                  forall z : elem,
                    keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
               (W p)
               (fun y => write_parent a y;; ret y)).
      * apply (@Hoare_cons_pre elem uf_state
                 (fun s =>
                    uf_abstract s repr_of /\
                    valid s p /\
                    repr_of p = repr_of orig0 /\
                    uf_size s = n0 /\
                    0 <= orig0 < n0 /\
                    forall z : elem,
                      keep0 z \/ z = a ->
                      repr_of z = repr_of orig0 /\ 0 <= z < n0)
                 (fun s =>
                    p = uf_parent s a /\
                    valid s p /\
                    uf_abstract s repr_of /\
                    valid s a /\
                    repr_of a = repr_of orig0 /\
                    uf_size s = n0 /\
                    0 <= orig0 < n0 /\
                    forall z : elem,
                      keep0 z -> repr_of z = repr_of orig0 /\ 0 <= z < n0)
                 (W p)
                 (fun y s =>
                    y = repr_of orig0 /\
                    uf_abstract s repr_of /\
                    uf_size s = n0 /\
                    0 <= orig0 < n0 /\
                    forall z : elem,
                      keep0 z \/ z = a ->
                      repr_of z = repr_of orig0 /\ 0 <= z < n0)).
        -- intros s [Hp [Hvp [Habs [Hva [Heq [Hsize [Hrange Hkeep]]]]]]].
           split; [exact Habs |].
           split; [exact Hvp |].
           split.
           ++ rewrite Hp.
              transitivity (repr_of a).
              ** apply (repr_of_parent s repr_of a Habs Hva).
                 rewrite <- Hp.
                 exact Hp_neq.
              ** exact Heq.
           ++ split; [exact Hsize |].
              split; [exact Hrange |].
              intros z Hz.
              destruct Hz as [Hz | Hz].
              ** exact (Hkeep z Hz).
              ** subst z.
                 split; [exact Heq |].
                 unfold valid in Hva.
                 rewrite Hsize in Hva.
                 exact Hva.
        -- exact (IH p (orig0, (n0, fun z : elem => keep0 z \/ z = a))).
      * intros y.
        apply (write_parent_compress_ret_rule a y orig0 n0 repr_of keep0).
Qed.

Theorem uf_find_correct :
  forall x, uf_find_spec x.
Proof.
  intros x.
  unfold uf_find_spec.
  intros repr_of.
  apply (@Hoare_cons_pre elem uf_state
           (fun s =>
              exists n : Z,
                uf_abstract s repr_of /\
                valid s x /\
                repr_of x = repr_of x /\
                uf_size s = n /\
                0 <= x < n /\
                forall z : elem,
                  False -> repr_of z = repr_of x /\ 0 <= z < n)
           (fun s => uf_abstract s repr_of /\ valid s x)
           (uf_find x)
           (fun y s => y = repr_of x /\ uf_abstract s repr_of)).
  - intros s [Habs Hvalid].
    exists (uf_size s).
    split; [exact Habs |].
    split; [exact Hvalid |].
    split; [reflexivity |].
    split; [reflexivity |].
    split; [exact Hvalid |].
    intros z Hfalse.
    contradiction.
  - apply (@Hoare_cons_post elem uf_state
             (fun s =>
                exists n : Z,
                  uf_abstract s repr_of /\
                  valid s x /\
                  repr_of x = repr_of x /\
                  uf_size s = n /\
                  0 <= x < n /\
                  forall z : elem,
                    False -> repr_of z = repr_of x /\ 0 <= z < n)
             (uf_find x)
             (fun y s =>
                exists n : Z,
                  y = repr_of x /\
                  uf_abstract s repr_of /\
                  uf_size s = n /\
                  0 <= x < n /\
                  forall z : elem,
                    False -> repr_of z = repr_of x /\ 0 <= z < n)
             (fun y s => y = repr_of x /\ uf_abstract s repr_of)).
    + intros y s [n [Hy [Habs _]]].
      split; [exact Hy | exact Habs].
    + apply (@Hoare_pre_ex uf_state elem Z
               (fun n s =>
                  uf_abstract s repr_of /\
                  valid s x /\
                  repr_of x = repr_of x /\
                  uf_size s = n /\
                  0 <= x < n /\
                  forall z : elem,
                    False -> repr_of z = repr_of x /\ 0 <= z < n)
               (uf_find x)
               (fun y s =>
                  exists n : Z,
                    y = repr_of x /\
                    uf_abstract s repr_of /\
                    uf_size s = n /\
                    0 <= x < n /\
                    forall z : elem,
                      False -> repr_of z = repr_of x /\ 0 <= z < n)).
      intros n.
      apply (@Hoare_cons_post elem uf_state
               (fun s =>
                  uf_abstract s repr_of /\
                  valid s x /\
                  repr_of x = repr_of x /\
                  uf_size s = n /\
                  0 <= x < n /\
                  forall z : elem,
                    False -> repr_of z = repr_of x /\ 0 <= z < n)
               (uf_find x)
               (fun y s =>
                  y = repr_of x /\
                  uf_abstract s repr_of /\
                  uf_size s = n /\
                  0 <= x < n /\
                  forall z : elem,
                    False -> repr_of z = repr_of x /\ 0 <= z < n)
               (fun y s =>
                  exists n : Z,
                    y = repr_of x /\
                    uf_abstract s repr_of /\
                    uf_size s = n /\
                    0 <= x < n /\
                    forall z : elem,
                      False -> repr_of z = repr_of x /\ 0 <= z < n)).
      * intros y s Hpost.
        exists n.
        exact Hpost.
      * apply (uf_find_strong x x n repr_of (fun _ => False)).
Qed.

Definition link_repr
  (repr_of : elem -> elem)
  (old new : elem) : elem -> elem :=
  fun z => if Z.eq_dec (repr_of z) old then new else repr_of z.

Lemma class_test_link_repr_new :
  forall repr_of old new z,
    old <> new ->
    class_test (link_repr repr_of old new) new z =
    orb (class_test repr_of old z) (class_test repr_of new z).
Proof.
  intros repr_of old new z Hneq.
  unfold class_test, link_repr.
  destruct (Z.eq_dec (repr_of z) old) as [Hold | Hnot_old].
  - destruct (Z.eq_dec old new); [congruence |].
    destruct (Z.eq_dec new new); [reflexivity | contradiction].
  - destruct (Z.eq_dec (repr_of z) new) as [Hnew | Hnot_new].
    + destruct (Z.eq_dec new old); [congruence |].
      destruct (Z.eq_dec new new); [reflexivity | contradiction].
    + destruct (Z.eq_dec (repr_of z) old); [congruence |].
      destruct (Z.eq_dec (repr_of z) new); [congruence | reflexivity].
Qed.

Lemma class_test_link_repr_other :
  forall repr_of old new r z,
    r <> new ->
    r <> old ->
    class_test (link_repr repr_of old new) r z =
    class_test repr_of r z.
Proof.
  intros repr_of old new r z Hrnew Hrold.
  unfold class_test, link_repr.
  destruct (Z.eq_dec (repr_of z) old) as [Hold | Hnot_old].
  - destruct (Z.eq_dec new r); [congruence |].
    destruct (Z.eq_dec old r); [congruence |].
    destruct (Z.eq_dec (repr_of z) r); [congruence | reflexivity].
  - destruct (Z.eq_dec (repr_of z) old); [congruence | reflexivity].
Qed.

Lemma class_size_link_repr_new :
  forall s repr_of old new,
    old <> new ->
    class_size (set_parent_state old new s) (link_repr repr_of old new) new =
    class_size s repr_of old + class_size s repr_of new.
Proof.
  intros s repr_of old new Hneq.
  unfold class_size, set_parent_state; simpl.
  rewrite (count_if_ext
             (enum_elems (uf_size s))
             (class_test (link_repr repr_of old new) new)
             (fun z => orb (class_test repr_of old z) (class_test repr_of new z))).
  2:{
    intros z Hz.
    apply class_test_link_repr_new.
    exact Hneq.
  }
  rewrite count_if_or_disjoint.
  - reflexivity.
  - intros z _ Hzold Hznew.
    unfold class_test in Hzold, Hznew.
    destruct (Z.eq_dec (repr_of z) old); [| discriminate].
    destruct (Z.eq_dec (repr_of z) new); [| discriminate].
    congruence.
Qed.

Lemma class_size_link_repr_other :
  forall s repr_of old new r,
    r <> new ->
    r <> old ->
    class_size (set_parent_state old new s) (link_repr repr_of old new) r =
    class_size s repr_of r.
Proof.
  intros s repr_of old new r Hrnew Hrold.
  unfold class_size, set_parent_state; simpl.
  apply count_if_ext.
  intros z Hz.
  apply class_test_link_repr_other; auto.
Qed.

Lemma class_size_inc_rank_state :
  forall s repr_of x r,
    class_size (inc_rank_state x s) repr_of r = class_size s repr_of r.
Proof.
  intros s repr_of x r.
  unfold class_size, inc_rank_state, set_rank_state; simpl.
  reflexivity.
Qed.

Lemma valid_set_rank_state :
  forall s x k z,
    valid (set_rank_state x k s) z <-> valid s z.
Proof.
  intros s x k z.
  unfold valid, set_rank_state; simpl.
  tauto.
Qed.

Lemma uf_parent_set_rank_state :
  forall s x k z,
    uf_parent (set_rank_state x k s) z = uf_parent s z.
Proof.
  reflexivity.
Qed.

Lemma uf_rank_set_rank_eq :
  forall s x k,
    uf_rank (set_rank_state x k s) x = k.
Proof.
  intros s x k.
  unfold set_rank_state; simpl.
  destruct (Z.eq_dec x x); [reflexivity | contradiction].
Qed.

Lemma uf_rank_set_rank_neq :
  forall s x k z,
    z <> x ->
    uf_rank (set_rank_state x k s) z = uf_rank s z.
Proof.
  intros s x k z Hneq.
  unfold set_rank_state; simpl.
  destruct (Z.eq_dec z x); congruence.
Qed.

Lemma valid_inc_rank_state :
  forall s x z,
    valid (inc_rank_state x s) z <-> valid s z.
Proof.
  intros s x z.
  unfold inc_rank_state.
  apply valid_set_rank_state.
Qed.

Lemma uf_parent_inc_rank_state :
  forall s x z,
    uf_parent (inc_rank_state x s) z = uf_parent s z.
Proof.
  intros s x z.
  unfold inc_rank_state.
  apply uf_parent_set_rank_state.
Qed.

Lemma uf_rank_inc_rank_eq :
  forall s x,
    uf_rank (inc_rank_state x s) x = uf_rank s x + 1.
Proof.
  intros s x.
  unfold inc_rank_state.
  apply uf_rank_set_rank_eq.
Qed.

Lemma uf_rank_inc_rank_neq :
  forall s x z,
    z <> x ->
    uf_rank (inc_rank_state x s) z = uf_rank s z.
Proof.
  intros s x z Hneq.
  unfold inc_rank_state.
  apply uf_rank_set_rank_neq.
  exact Hneq.
Qed.

Lemma parent_chain_reroot :
  forall s x p z,
    parent_chain s z x ->
    uf_parent s x = x ->
    valid s p ->
    uf_parent s p = p ->
    parent_chain (set_parent_state x p s) z p.
Proof.
  intros s x p z Hchain.
  induction Hchain as [z Hvalidz | z y x0 Hvalidz Hzy Hchain IH];
    intros Hroot_x Hvalidp Hroot_p.
  - apply parent_chain_step with (y := p).
    + apply (proj2 (valid_set_parent_state s z p z)).
      exact Hvalidz.
    + rewrite uf_parent_set_parent_eq. reflexivity.
    + apply parent_chain_refl.
      apply (proj2 (valid_set_parent_state s z p p)).
      exact Hvalidp.
  - destruct (Z.eq_dec z x0) as [-> | Hneq].
    + rewrite Hroot_x in Hzy. subst y.
      apply parent_chain_step with (y := p).
      * apply (proj2 (valid_set_parent_state s x0 p x0)).
        exact Hvalidz.
      * rewrite uf_parent_set_parent_eq. reflexivity.
      * apply parent_chain_refl.
        apply (proj2 (valid_set_parent_state s x0 p p)).
        exact Hvalidp.
    + apply parent_chain_step with (y := y).
      * apply (proj2 (valid_set_parent_state s x0 p z)).
        exact Hvalidz.
      * rewrite uf_parent_set_parent_neq; auto.
      * apply IH; auto.
Qed.

Lemma parent_chain_preserve_off_root :
  forall s x p z r,
    uf_parent s x = x ->
    parent_chain s z r ->
    uf_parent s r = r ->
    r <> x ->
    parent_chain (set_parent_state x p s) z r.
Proof.
  intros s x p z r Hroot_x Hchain.
  induction Hchain as [z Hvalidz | z y r Hvalidz Hzy Hchain IH];
    intros Hroot_r Hneq_rx.
  - apply parent_chain_refl.
    apply (proj2 (valid_set_parent_state s x p z)).
    exact Hvalidz.
  - destruct (Z.eq_dec z x) as [-> | Hneq_zx].
    + assert (x = r).
      { symmetry.
        apply (parent_chain_root_unique s x r x).
        - apply parent_chain_step with (y := y).
          + exact Hvalidz.
          + exact Hzy.
          + exact Hchain.
        - exact Hroot_r.
        - apply parent_chain_refl.
          exact Hvalidz.
        - exact Hroot_x. }
      subst r.
      contradiction.
    + apply parent_chain_step with (y := y).
      * apply (proj2 (valid_set_parent_state s x p z)).
        exact Hvalidz.
      * rewrite uf_parent_set_parent_neq; auto.
      * apply IH; auto.
Qed.

Lemma link_repr_root_fixed :
  forall repr_of old new,
    repr_of new = new ->
    old <> new ->
    link_repr repr_of old new new = new.
Proof.
  intros repr_of old new Hrepr_new Hneq.
  unfold link_repr.
  destruct (Z.eq_dec (repr_of new) old); congruence.
Qed.

Lemma legal_link_repr :
  forall s repr_of old new,
    legal s repr_of ->
    valid s new ->
    repr_of new = new ->
    old <> new ->
    legal (set_parent_state old new s) (link_repr repr_of old new).
Proof.
  intros s repr_of old new Hlegal Hvalid_new Hrepr_new Hneq_new a Hva_new.
  pose proof (proj1 (valid_set_parent_state s old new a) Hva_new) as Hva_old.
  destruct (Z.eq_dec (repr_of a) old) as [Ha_old | Ha_not_old].
  - split.
    + unfold link_repr.
      rewrite Ha_old.
      destruct (Z.eq_dec old old); [| contradiction].
      apply (proj2 (valid_set_parent_state s old new new)).
      exact Hvalid_new.
    + unfold link_repr.
      rewrite Ha_old.
      destruct (Z.eq_dec old old); [| contradiction].
      apply link_repr_root_fixed; auto.
  - split.
    + unfold link_repr.
      destruct (Z.eq_dec (repr_of a) old); [congruence |].
      apply (proj2 (valid_set_parent_state s old new (repr_of a))).
      apply (legal_repr_valid s repr_of a Hlegal Hva_old).
    + unfold link_repr.
      destruct (Z.eq_dec (repr_of a) old); [congruence |].
      pose proof (legal_repr_idem s repr_of a Hlegal Hva_old) as Hid.
      rewrite Hid.
      destruct (Z.eq_dec (repr_of a) old); [congruence | reflexivity].
Qed.

Lemma merge_same_class_refl :
  forall D repr_of x y,
    same_class repr_of x y ->
    merge D repr_of x y repr_of.
Proof.
  intros D repr_of x y Hxy a b _ _.
  unfold merge, same_class in *.
  split; intro Hab.
  - left. exact Hab.
  - destruct Hab as [Hab | [[Hax Hby] | [Hay Hbx]]].
    + exact Hab.
    + rewrite Hax, Hby, Hxy. reflexivity.
    + rewrite Hay, Hbx, Hxy. reflexivity.
Qed.

Lemma merge_link_repr :
  forall s repr_of x y rx ry,
    valid s x ->
    valid s y ->
    rx = repr_of x ->
    ry = repr_of y ->
    rx <> ry ->
    merge (valid s) repr_of x y (link_repr repr_of rx ry).
Proof.
  intros s repr_of x y rx ry Hvalidx Hvalidy Hrx Hry Hneq a b Hva Hvb.
  unfold merge, same_class, link_repr.
  subst rx ry.
  destruct (Z.eq_dec (repr_of a) (repr_of x)) as [Ha | Ha];
    destruct (Z.eq_dec (repr_of b) (repr_of x)) as [Hb | Hb];
    split; intro H.
  - left. congruence.
  - reflexivity.
  - right. left. split.
    + exact Ha.
    + symmetry. exact H.
  - destruct H as [Hab | [[Hax Hby] | [Hay Hbx]]].
    + exfalso.
      apply Hb.
      rewrite <- Hab.
      exact Ha.
    + symmetry. exact Hby.
    + exfalso.
      apply Hneq.
      rewrite <- Ha, Hay.
      reflexivity.
  - right. right. split.
    + exact H.
    + exact Hb.
  - destruct H as [Hab | [[Hax Hby] | [Hay Hbx]]].
    + exfalso.
      apply Ha.
      rewrite Hab.
      exact Hb.
    + exfalso.
      apply Hneq.
      rewrite <- Hb, Hby.
      reflexivity.
    + exact Hay.
  - left. exact H.
  - destruct H as [Hab | [[Hax Hby] | [Hay Hbx]]].
    + exact Hab.
    + contradiction.
    + contradiction.
Qed.

Lemma parent_chain_set_rank_state :
  forall s x k a r,
    parent_chain s a r ->
    parent_chain (set_rank_state x k s) a r.
Proof.
  intros s x k a r Hchain.
  induction Hchain as [a Hva | a y r Hva Hay Hchain IH].
  - apply parent_chain_refl.
    apply (proj2 (valid_set_rank_state s x k a)).
    exact Hva.
  - apply parent_chain_step with (y := y).
    + apply (proj2 (valid_set_rank_state s x k a)).
      exact Hva.
    + rewrite uf_parent_set_rank_state.
      exact Hay.
    + exact IH.
Qed.

Lemma parent_chain_inc_rank_state :
  forall s x a r,
    parent_chain s a r ->
    parent_chain (inc_rank_state x s) a r.
Proof.
  intros s x a r Hchain.
  unfold inc_rank_state.
  apply parent_chain_set_rank_state.
  exact Hchain.
Qed.

Lemma legal_inc_rank_state :
  forall s repr_of x,
    legal s repr_of ->
    legal (inc_rank_state x s) repr_of.
Proof.
  intros s repr_of x Hlegal a Hva_new.
  pose proof (proj1 (valid_inc_rank_state s x a) Hva_new) as Hva_old.
  destruct (Hlegal a Hva_old) as [Hvalid_repr Hid].
  split.
  - apply (proj2 (valid_inc_rank_state s x (repr_of a))).
    exact Hvalid_repr.
  - exact Hid.
Qed.

Lemma uf_models_inc_rank_state :
  forall s repr_of x,
    uf_models s repr_of ->
    uf_models (inc_rank_state x s) repr_of.
Proof.
  intros s repr_of x Hmodels a Hva_new.
  pose proof (proj1 (valid_inc_rank_state s x a) Hva_new) as Hva_old.
  destruct (Hmodels a Hva_old) as [_ [Hchain [Hvalid_r Hroot_r]]].
  split.
  - exact Hva_new.
  - split.
    + apply parent_chain_inc_rank_state.
      exact Hchain.
    + split.
      * apply (proj2 (valid_inc_rank_state s x (repr_of a))).
        exact Hvalid_r.
      * rewrite uf_parent_inc_rank_state.
        exact Hroot_r.
Qed.

Lemma uf_models_link_root :
  forall s repr_of old new,
    uf_abstract s repr_of ->
    valid s old ->
    valid s new ->
    uf_parent s old = old ->
    uf_parent s new = new ->
    old <> new ->
    uf_models (set_parent_state old new s) (link_repr repr_of old new).
Proof.
  intros s repr_of old new Habs Hvalid_old Hvalid_new Hroot_old Hroot_new Hneq a
    Hva_new.
  pose proof (proj1 (valid_set_parent_state s old new a) Hva_new) as Hva_old.
  destruct (uf_abstract_models s repr_of Habs a Hva_old)
    as [_ [Hchain_a [Hvalid_ra Hroot_ra]]].
  destruct (Z.eq_dec (repr_of a) old) as [Ha_old | Ha_not_old].
  - split.
    + exact Hva_new.
    + split.
      * unfold link_repr.
        rewrite Ha_old.
        destruct (Z.eq_dec old old); [| contradiction].
        rewrite Ha_old in Hchain_a.
        apply parent_chain_reroot; auto.
      * split.
        -- unfold link_repr.
           rewrite Ha_old.
           destruct (Z.eq_dec old old); [| contradiction].
           apply (proj2 (valid_set_parent_state s old new new)).
           exact Hvalid_new.
        -- unfold link_repr.
           rewrite Ha_old.
           destruct (Z.eq_dec old old); [| contradiction].
           rewrite uf_parent_set_parent_neq; auto.
  - split.
    + exact Hva_new.
    + split.
      * unfold link_repr.
        destruct (Z.eq_dec (repr_of a) old); [congruence |].
        apply parent_chain_preserve_off_root; auto.
      * split.
        -- unfold link_repr.
           destruct (Z.eq_dec (repr_of a) old); [congruence |].
           apply (proj2 (valid_set_parent_state s old new (repr_of a))).
           exact Hvalid_ra.
        -- unfold link_repr.
           destruct (Z.eq_dec (repr_of a) old); [congruence |].
           rewrite uf_parent_set_parent_neq; auto.
Qed.

Lemma uf_inv_link_root_lt :
  forall s old new,
    uf_inv s ->
    valid s old ->
    valid s new ->
    old <> new ->
    uf_rank s old < uf_rank s new ->
    uf_inv (set_parent_state old new s).
Proof.
  intros s old new Hinv Hvalid_old Hvalid_new Hneq Hrank_lt.
  destruct Hinv as [Hclosed [Hnonneg Hinc]].
  split.
  - intros a Hva_new.
    pose proof (proj1 (valid_set_parent_state s old new a) Hva_new) as Hva_old.
    destruct (Z.eq_dec a old) as [-> | Ha_neq].
    + rewrite uf_parent_set_parent_eq.
      apply (proj2 (valid_set_parent_state s old new new)).
      exact Hvalid_new.
    + rewrite uf_parent_set_parent_neq; auto.
      apply (proj2 (valid_set_parent_state s old new (uf_parent s a))).
      apply Hclosed.
      exact Hva_old.
  - split.
    + intros a Hva_new.
      pose proof (proj1 (valid_set_parent_state s old new a) Hva_new) as Hva_old.
      rewrite uf_rank_set_parent_state.
      apply Hnonneg.
      exact Hva_old.
    + intros a Hva_new Hneq_new.
      pose proof (proj1 (valid_set_parent_state s old new a) Hva_new) as Hva_old.
      destruct (Z.eq_dec a old) as [-> | Ha_neq].
      * rewrite uf_parent_set_parent_eq in Hneq_new.
        rewrite uf_rank_set_parent_state.
        rewrite uf_parent_set_parent_eq.
        rewrite uf_rank_set_parent_state.
        exact Hrank_lt.
      * rewrite uf_parent_set_parent_neq in Hneq_new by exact Ha_neq.
        rewrite uf_rank_set_parent_state.
        rewrite uf_parent_set_parent_neq by exact Ha_neq.
        rewrite uf_rank_set_parent_state.
        apply Hinc.
        -- exact Hva_old.
        -- exact Hneq_new.
Qed.

Lemma uf_inv_link_root_eq_bump :
  forall s old new,
    uf_inv s ->
    valid s old ->
    valid s new ->
    uf_parent s new = new ->
    old <> new ->
    uf_rank s old = uf_rank s new ->
    uf_inv (inc_rank_state new (set_parent_state old new s)).
Proof.
  intros s old new Hinv Hvalid_old Hvalid_new Hroot_new Hneq Hrank_eq.
  destruct Hinv as [Hclosed [Hnonneg Hinc]].
  split.
  - intros a Hva_final.
    pose proof (proj1 (valid_inc_rank_state (set_parent_state old new s) new a) Hva_final)
      as Hva_link.
    pose proof (proj1 (valid_set_parent_state s old new a) Hva_link) as Hva_old.
    rewrite uf_parent_inc_rank_state.
    destruct (Z.eq_dec a old) as [-> | Ha_neq].
    + rewrite uf_parent_set_parent_eq.
      apply (proj2 (valid_inc_rank_state (set_parent_state old new s) new new)).
      apply (proj2 (valid_set_parent_state s old new new)).
      exact Hvalid_new.
    + rewrite uf_parent_set_parent_neq; auto.
      apply (proj2 (valid_inc_rank_state (set_parent_state old new s) new (uf_parent s a))).
      apply (proj2 (valid_set_parent_state s old new (uf_parent s a))).
      apply Hclosed.
      exact Hva_old.
  - split.
    + intros a Hva_final.
      pose proof (proj1 (valid_inc_rank_state (set_parent_state old new s) new a) Hva_final)
        as Hva_link.
      pose proof (proj1 (valid_set_parent_state s old new a) Hva_link) as Hva_old.
      destruct (Z.eq_dec a new) as [-> | Ha_neq].
      * rewrite uf_rank_inc_rank_eq.
        rewrite uf_rank_set_parent_state.
        pose proof (Hnonneg new Hvalid_new).
        lia.
      * rewrite uf_rank_inc_rank_neq by exact Ha_neq.
        rewrite uf_rank_set_parent_state.
        apply Hnonneg.
        exact Hva_old.
    + intros a Hva_final Hneq_final.
      pose proof (proj1 (valid_inc_rank_state (set_parent_state old new s) new a) Hva_final)
        as Hva_link.
      pose proof (proj1 (valid_set_parent_state s old new a) Hva_link) as Hva_old.
      rewrite uf_parent_inc_rank_state in Hneq_final.
      destruct (Z.eq_dec a old) as [-> | Ha_old].
      * rewrite uf_parent_set_parent_eq in Hneq_final.
        rewrite uf_rank_inc_rank_neq by exact Hneq.
        rewrite uf_rank_set_parent_state.
        rewrite uf_parent_inc_rank_state.
        rewrite uf_parent_set_parent_eq.
        rewrite uf_rank_inc_rank_eq.
        rewrite uf_rank_set_parent_state.
        lia.
      * rewrite uf_parent_set_parent_neq in Hneq_final by exact Ha_old.
        destruct (Z.eq_dec a new) as [-> | Ha_new].
        -- rewrite Hroot_new in Hneq_final.
           contradiction.
        -- rewrite uf_rank_inc_rank_neq by exact Ha_new.
           rewrite uf_rank_set_parent_state.
           destruct (Z.eq_dec (uf_parent s a) new) as [Hparent_new | Hparent_neq].
           ++ rewrite uf_parent_inc_rank_state.
              rewrite uf_parent_set_parent_neq by exact Ha_old.
              rewrite Hparent_new.
              rewrite uf_rank_inc_rank_eq.
              rewrite uf_rank_set_parent_state.
              pose proof (Hinc a Hva_old Hneq_final) as Hlt.
              rewrite Hparent_new in Hlt.
              lia.
           ++ rewrite uf_parent_inc_rank_state.
              rewrite uf_parent_set_parent_neq by exact Ha_old.
              rewrite uf_rank_inc_rank_neq by exact Hparent_neq.
              rewrite uf_rank_set_parent_state.
              apply Hinc.
              ** exact Hva_old.
              ** exact Hneq_final.
Qed.

Lemma uf_abstract_link_root_lt :
  forall s repr_of old new,
    uf_abstract s repr_of ->
    valid s old ->
    valid s new ->
    uf_parent s old = old ->
    uf_parent s new = new ->
    old <> new ->
    uf_rank s old < uf_rank s new ->
    uf_abstract (set_parent_state old new s) (link_repr repr_of old new).
Proof.
  intros s repr_of old new Habs Hvalid_old Hvalid_new Hroot_old Hroot_new Hneq
    Hrank_lt.
  pose proof (repr_of_root s repr_of old Habs Hvalid_old Hroot_old) as Hrepr_old.
  pose proof (repr_of_root s repr_of new Habs Hvalid_new Hroot_new) as Hrepr_new.
  pose proof (uf_abstract_rank_class_bound s repr_of Habs) as Hrank_bound.
  split.
  - apply legal_link_repr.
    + exact (uf_abstract_legal s repr_of Habs).
    + exact Hvalid_new.
    + exact Hrepr_new.
    + exact Hneq.
  - split.
    + apply uf_inv_link_root_lt; auto.
      exact (uf_abstract_inv s repr_of Habs).
    + split.
      * apply uf_models_link_root; auto.
      * intros r Hr_valid_post Hr_root_post.
        destruct (Z.eq_dec r new) as [-> | Hr_new].
        -- rewrite class_size_link_repr_new by exact Hneq.
           rewrite uf_rank_set_parent_state.
           pose proof (Hrank_bound new Hvalid_new Hrepr_new) as Hnew_bound.
           pose proof (class_size_root_positive s repr_of old Hvalid_old Hrepr_old) as Hold_pos.
           lia.
        -- assert (r <> old) as Hr_old.
           {
             intro Heq.
             subst r.
             unfold link_repr in Hr_root_post.
             rewrite Hrepr_old in Hr_root_post.
             destruct (Z.eq_dec old old) as [_ | Hbad].
             - congruence.
             - contradiction.
           }
           assert (repr_of r = r) as Hr_root_pre.
           {
             unfold link_repr in Hr_root_post.
             destruct (Z.eq_dec (repr_of r) old) as [Hr_old_class | Hr_not_old_class].
             - exfalso. apply Hr_new. symmetry. exact Hr_root_post.
             - exact Hr_root_post.
           }
           rewrite class_size_link_repr_other by auto.
           rewrite uf_rank_set_parent_state.
           apply Hrank_bound.
           ++ exact Hr_valid_post.
           ++ exact Hr_root_pre.
Qed.

Lemma uf_abstract_link_root_eq :
  forall s repr_of old new,
    uf_abstract s repr_of ->
    valid s old ->
    valid s new ->
    uf_parent s old = old ->
    uf_parent s new = new ->
    old <> new ->
    uf_rank s old = uf_rank s new ->
    uf_abstract (inc_rank_state new (set_parent_state old new s))
      (link_repr repr_of old new).
Proof.
  intros s repr_of old new Habs Hvalid_old Hvalid_new Hroot_old Hroot_new Hneq
    Hrank_eq.
  pose proof (repr_of_root s repr_of old Habs Hvalid_old Hroot_old) as Hrepr_old.
  pose proof (repr_of_root s repr_of new Habs Hvalid_new Hroot_new) as Hrepr_new.
  pose proof (uf_abstract_rank_class_bound s repr_of Habs) as Hrank_bound.
  split.
  - apply legal_inc_rank_state.
    apply legal_link_repr.
    + exact (uf_abstract_legal s repr_of Habs).
    + exact Hvalid_new.
    + exact Hrepr_new.
    + exact Hneq.
  - split.
    + apply uf_inv_link_root_eq_bump; auto.
      exact (uf_abstract_inv s repr_of Habs).
    + split.
      * apply uf_models_inc_rank_state.
        apply uf_models_link_root; auto.
      * intros r Hr_valid_post Hr_root_post.
        destruct (Z.eq_dec r new) as [-> | Hr_new].
        -- rewrite class_size_inc_rank_state.
           rewrite class_size_link_repr_new by exact Hneq.
           rewrite uf_rank_inc_rank_eq.
           rewrite uf_rank_set_parent_state.
           pose proof (Hrank_bound old Hvalid_old Hrepr_old) as Hold_bound.
           pose proof (Hrank_bound new Hvalid_new Hrepr_new) as Hnew_bound.
           assert (uf_rank s new < class_size s repr_of old) as Hold_new.
           { rewrite <- Hrank_eq. exact Hold_bound. }
           assert (uf_rank s new < class_size s repr_of new) as Hnew_new.
           { exact Hnew_bound. }
           pose proof (class_size_root_positive s repr_of old Hvalid_old Hrepr_old) as Hold_pos.
           pose proof (class_size_root_positive s repr_of new Hvalid_new Hrepr_new) as Hnew_pos.
           lia.
        -- assert (Hr_valid_link : valid (set_parent_state old new s) r).
           {
             apply (proj1 (valid_inc_rank_state (set_parent_state old new s) new r)).
             exact Hr_valid_post.
           }
           assert (Hr_valid_pre : valid s r).
           {
             apply (proj1 (valid_set_parent_state s old new r)).
             exact Hr_valid_link.
           }
           assert (r <> old) as Hr_old.
           {
             intro Heq.
             subst r.
             unfold link_repr in Hr_root_post.
             rewrite Hrepr_old in Hr_root_post.
             destruct (Z.eq_dec old old) as [_ | Hbad].
             - congruence.
             - contradiction.
           }
           assert (repr_of r = r) as Hr_root_pre.
           {
             unfold link_repr in Hr_root_post.
             destruct (Z.eq_dec (repr_of r) old) as [Hr_old_class | Hr_not_old_class].
             - exfalso. apply Hr_new. symmetry. exact Hr_root_post.
             - exact Hr_root_post.
           }
           rewrite class_size_inc_rank_state.
           rewrite class_size_link_repr_other by auto.
           rewrite uf_rank_inc_rank_neq by exact Hr_new.
           rewrite uf_rank_set_parent_state.
           apply Hrank_bound.
           ++ exact Hr_valid_pre.
           ++ exact Hr_root_pre.
Qed.

Lemma merge_sym :
  forall D repr_of x y repr_of',
    merge D repr_of x y repr_of' ->
    merge D repr_of y x repr_of'.
Proof.
  intros D repr_of x y repr_of' Hmerge a b Ha Hb.
  specialize (Hmerge a b Ha Hb).
  unfold merge, same_class in *.
  tauto.
Qed.

Lemma merge_transport :
  forall D1 D2 repr_of x y repr_of',
    (forall z, D2 z -> D1 z) ->
    merge D1 repr_of x y repr_of' ->
    merge D2 repr_of x y repr_of'.
Proof.
  intros D1 D2 repr_of x y repr_of' Hsub Hmerge a b Ha Hb.
  apply Hmerge.
  - apply Hsub. exact Ha.
  - apply Hsub. exact Hb.
Qed.

Lemma merge_replace_repr_args :
  forall D repr_of x y rx ry repr_of',
    same_class repr_of x rx ->
    same_class repr_of y ry ->
    merge D repr_of rx ry repr_of' ->
    merge D repr_of x y repr_of'.
Proof.
  intros D repr_of x y rx ry repr_of' Hx Hy Hmerge a b Ha Hb.
  specialize (Hmerge a b Ha Hb).
  unfold merge, same_class in *.
  rewrite Hx, Hy.
  exact Hmerge.
Qed.

Lemma uf_find_preserve_valids :
  forall x y repr_of,
    Hoare
      (fun s => uf_abstract s repr_of /\ valid s x /\ valid s y)
      (uf_find x)
      (fun rx s =>
         rx = repr_of x /\
         uf_abstract s repr_of /\
         valid s x /\
         valid s y).
Proof.
  intros x y repr_of.
  apply Hoare_state_intro.
  intros s0 [Habs [Hvalidx Hvalidy]].
  apply (@Hoare_cons_post elem uf_state
           (fun s => s = s0)
           (uf_find x)
           (fun rx s =>
              rx = repr_of x /\
              uf_abstract s repr_of /\
              uf_size s = uf_size s0 /\
              0 <= x < uf_size s0 /\
              forall z : elem,
                False -> repr_of z = repr_of x /\ 0 <= z < uf_size s0)
           (fun rx s =>
              rx = repr_of x /\
              uf_abstract s repr_of /\
              valid s x /\
              valid s y)).
  - intros rx s [Hrx [Habs' [Hsize [Hrange _]]]].
    split; [exact Hrx |].
    split; [exact Habs' |].
    split.
    + unfold valid.
      rewrite Hsize.
      exact Hrange.
    + unfold valid in Hvalidy |- *.
      rewrite Hsize.
      exact Hvalidy.
  - apply (@Hoare_cons_pre elem uf_state
             (fun s =>
                uf_abstract s repr_of /\
                valid s x /\
                repr_of x = repr_of x /\
                uf_size s = uf_size s0 /\
                0 <= x < uf_size s0 /\
                forall z : elem,
                  False -> repr_of z = repr_of x /\ 0 <= z < uf_size s0)
             (fun s => s = s0)
             (uf_find x)
             (fun rx s =>
                rx = repr_of x /\
                uf_abstract s repr_of /\
                uf_size s = uf_size s0 /\
                0 <= x < uf_size s0 /\
                forall z : elem,
                  False -> repr_of z = repr_of x /\ 0 <= z < uf_size s0)).
    + intros s Hs.
      subst s.
      split; [exact Habs |].
      split; [exact Hvalidx |].
      split; [reflexivity |].
      split; [reflexivity |].
      split; [exact Hvalidx |].
      intros z Hfalse.
      contradiction.
    + apply (uf_find_strong x x (uf_size s0) repr_of (fun _ => False)).
Qed.

Lemma uf_union_link_correct :
  forall rx ry x y repr_of,
    Hoare
      (fun s =>
         uf_abstract s repr_of /\
         valid s rx /\
         valid s ry /\
         rx = repr_of rx /\
         ry = repr_of ry /\
         rx <> ry /\
         valid s x /\
         valid s y)
      (rx_rank <- read_rank rx;;
       ry_rank <- read_rank ry;;
       choice
         (assume!! (ry_rank < rx_rank);;
          write_parent ry rx)
         (choice
            (assume!! (rx_rank < ry_rank);;
             write_parent rx ry)
            (assume!! (rx_rank = ry_rank);;
             write_parent rx ry;;
             bump_rank ry)))
      (fun _ s =>
         exists repr_of',
           uf_abstract s repr_of' /\
           merge (valid s) repr_of rx ry repr_of' /\
           valid s x /\
           valid s y).
Proof.
  intros rx ry x y repr_of.
  apply Hoare_state_intro.
  intros s0
    [Habs
      [Hvalid_rx
        [Hvalid_ry
          [Hrepr_rx [Hrepr_ry [Hneq [Hvalidx Hvalidy]]]]]]].
  pose proof (uf_abstract_models s0 repr_of Habs rx Hvalid_rx) as Hroot_rx_full.
  pose proof (uf_abstract_models s0 repr_of Habs ry Hvalid_ry) as Hroot_ry_full.
  destruct Hroot_rx_full as [_ [_ [_ Hroot_rx]]].
  destruct Hroot_ry_full as [_ [_ [_ Hroot_ry]]].
  rewrite <- Hrepr_rx in Hroot_rx.
  rewrite <- Hrepr_ry in Hroot_ry.
  apply (@Hoare_bind Z unit uf_state
           (fun s => s = s0)
           (fun rx_rank s => rx_rank = uf_rank s rx /\ s = s0)
           (fun _ s =>
              exists repr_of',
                uf_abstract s repr_of' /\
                merge (valid s) repr_of rx ry repr_of' /\
                valid s x /\
                valid s y)
           (read_rank rx)
           (fun rx_rank =>
              ry_rank <- read_rank ry;;
              choice
                (assume!! (ry_rank < rx_rank);;
                 write_parent ry rx)
                (choice
                   (assume!! (rx_rank < ry_rank);;
                    write_parent rx ry)
                   (assume!! (rx_rank = ry_rank);;
                    write_parent rx ry;;
                    bump_rank ry)))).
  - apply (read_rank_rule (fun s => s = s0) rx).
    intros s Hs.
    subst s.
    exact Hvalid_rx.
  - intros rx_rank.
    apply (@Hoare_bind Z unit uf_state
             (fun s => rx_rank = uf_rank s rx /\ s = s0)
             (fun ry_rank s =>
                ry_rank = uf_rank s ry /\
                rx_rank = uf_rank s rx /\
                s = s0)
             (fun _ s =>
                exists repr_of',
                  uf_abstract s repr_of' /\
                  merge (valid s) repr_of rx ry repr_of' /\
                  valid s x /\
                  valid s y)
             (read_rank ry)
             (fun ry_rank =>
                choice
                  (assume!! (ry_rank < rx_rank);;
                   write_parent ry rx)
                  (choice
                     (assume!! (rx_rank < ry_rank);;
                      write_parent rx ry)
                     (assume!! (rx_rank = ry_rank);;
                      write_parent rx ry;;
                      bump_rank ry)))).
    + apply (read_rank_rule
               (fun s => rx_rank = uf_rank s rx /\ s = s0)
               ry).
      intros s [_ Hs].
      subst s.
      exact Hvalid_ry.
    + intros ry_rank.
      apply Hoare_choice.
      * apply Hoare_assume_bind.
        intros Hlt.
        apply (@Hoare_cons_post unit uf_state
                 (fun s =>
                    ry_rank = uf_rank s ry /\
                    rx_rank = uf_rank s rx /\
                    s = s0)
                 (write_parent ry rx)
                 (fun _ s =>
                    exists s1,
                      s = set_parent_state ry rx s1 /\
                      ry_rank = uf_rank s1 ry /\
                      rx_rank = uf_rank s1 rx /\
                      s1 = s0)
                 (fun _ s =>
                    exists repr_of',
                      uf_abstract s repr_of' /\
                      merge (valid s) repr_of rx ry repr_of' /\
                      valid s x /\
                      valid s y)).
        -- intros [] s [s1 [Hs [Hryrank [Hrxrank Hs1]]]].
           subst s1.
           subst s.
           rewrite Hryrank, Hrxrank in Hlt.
           assert (Hneq_yr : ry <> rx).
           { intro Hbad. apply Hneq. symmetry. exact Hbad. }
           exists (link_repr repr_of ry rx).
           split.
           ++ apply (uf_abstract_link_root_lt
                       s0 repr_of ry rx Habs Hvalid_ry Hvalid_rx
                       Hroot_ry Hroot_rx Hneq_yr Hlt).
           ++ split.
              ** apply (merge_transport
                          (valid s0)
                          (valid (set_parent_state ry rx s0))
                          repr_of rx ry
                          (link_repr repr_of ry rx)).
                 --- intros z Hz.
                     apply (proj1 (valid_set_parent_state s0 ry rx z)).
                     exact Hz.
                 --- apply merge_sym.
                     apply (merge_link_repr
                              s0 repr_of ry rx ry rx
                              Hvalid_ry Hvalid_rx Hrepr_ry Hrepr_rx Hneq_yr).
              ** split.
                 --- apply (proj2 (valid_set_parent_state s0 ry rx x)).
                     exact Hvalidx.
                 --- apply (proj2 (valid_set_parent_state s0 ry rx y)).
                     exact Hvalidy.
        -- apply (write_parent_rule
                    (fun s =>
                       ry_rank = uf_rank s ry /\
                       rx_rank = uf_rank s rx /\
                       s = s0)
                    ry rx).
           intros s [_ [_ Hs]].
           subst s.
           unfold parent_write_safe.
           split; [exact Hvalid_ry | exact Hvalid_rx].
      * apply Hoare_choice.
        -- apply Hoare_assume_bind.
           intros Hlt.
           apply (@Hoare_cons_post unit uf_state
                    (fun s =>
                       ry_rank = uf_rank s ry /\
                       rx_rank = uf_rank s rx /\
                       s = s0)
                    (write_parent rx ry)
                    (fun _ s =>
                       exists s1,
                         s = set_parent_state rx ry s1 /\
                         ry_rank = uf_rank s1 ry /\
                         rx_rank = uf_rank s1 rx /\
                         s1 = s0)
                    (fun _ s =>
                       exists repr_of',
                         uf_abstract s repr_of' /\
                         merge (valid s) repr_of rx ry repr_of' /\
                         valid s x /\
                         valid s y)).
           ++ intros [] s [s1 [Hs [Hryrank [Hrxrank Hs1]]]].
              subst s1.
              subst s.
              rewrite Hrxrank, Hryrank in Hlt.
              exists (link_repr repr_of rx ry).
              split.
              ** apply (uf_abstract_link_root_lt
                          s0 repr_of rx ry Habs Hvalid_rx Hvalid_ry
                          Hroot_rx Hroot_ry Hneq Hlt).
              ** split.
                 --- apply (merge_transport
                               (valid s0)
                               (valid (set_parent_state rx ry s0))
                               repr_of rx ry
                               (link_repr repr_of rx ry)).
                     +++ intros z Hz.
                         apply (proj1 (valid_set_parent_state s0 rx ry z)).
                         exact Hz.
                     +++ apply (merge_link_repr
                                  s0 repr_of rx ry rx ry
                                  Hvalid_rx Hvalid_ry Hrepr_rx Hrepr_ry Hneq).
                 --- split.
                     +++ apply (proj2 (valid_set_parent_state s0 rx ry x)).
                         exact Hvalidx.
                     +++ apply (proj2 (valid_set_parent_state s0 rx ry y)).
                         exact Hvalidy.
           ++ apply (write_parent_rule
                       (fun s =>
                          ry_rank = uf_rank s ry /\
                          rx_rank = uf_rank s rx /\
                          s = s0)
                       rx ry).
              intros s [_ [_ Hs]].
              subst s.
              unfold parent_write_safe.
              split; [exact Hvalid_rx | exact Hvalid_ry].
        -- apply Hoare_assume_bind.
           intros Heq_rank.
           apply (@Hoare_bind unit unit uf_state
                    (fun s =>
                       ry_rank = uf_rank s ry /\
                       rx_rank = uf_rank s rx /\
                       s = s0)
                    (fun _ s =>
                       s = set_parent_state rx ry s0 /\
                       uf_rank s0 rx = uf_rank s0 ry)
                    (fun _ s =>
                       exists repr_of',
                         uf_abstract s repr_of' /\
                         merge (valid s) repr_of rx ry repr_of' /\
                         valid s x /\
                         valid s y)
                    (write_parent rx ry)
                    (fun _ => bump_rank ry)).
           ++ apply (@Hoare_cons_post unit uf_state
                       (fun s =>
                          ry_rank = uf_rank s ry /\
                          rx_rank = uf_rank s rx /\
                          s = s0)
                       (write_parent rx ry)
                       (fun _ s =>
                          exists s1,
                            s = set_parent_state rx ry s1 /\
                            ry_rank = uf_rank s1 ry /\
                            rx_rank = uf_rank s1 rx /\
                            s1 = s0)
                       (fun _ s =>
                          s = set_parent_state rx ry s0 /\
                          uf_rank s0 rx = uf_rank s0 ry)).
              ** intros [] s [s1 [Hs [Hryrank [Hrxrank Hs1]]]].
                 subst s1.
                 subst s.
                 split; [reflexivity |].
                 rewrite Hrxrank, Hryrank in Heq_rank.
                 exact Heq_rank.
              ** apply (write_parent_rule
                          (fun s =>
                             ry_rank = uf_rank s ry /\
                             rx_rank = uf_rank s rx /\
                             s = s0)
                          rx ry).
                 intros s [_ [_ Hs]].
                 subst s.
                 unfold parent_write_safe.
                 split; [exact Hvalid_rx | exact Hvalid_ry].
           ++ intros [].
              apply (@Hoare_cons_post unit uf_state
                       (fun s =>
                          s = set_parent_state rx ry s0 /\
                          uf_rank s0 rx = uf_rank s0 ry)
                       (bump_rank ry)
                       (fun _ s =>
                          exists s1,
                            s = inc_rank_state ry s1 /\
                            s1 = set_parent_state rx ry s0 /\
                            uf_rank s0 rx = uf_rank s0 ry)
                       (fun _ s =>
                          exists repr_of',
                            uf_abstract s repr_of' /\
                            merge (valid s) repr_of rx ry repr_of' /\
                            valid s x /\
                            valid s y)).
              ** intros [] s [s1 [Hs [Hs1 Hrank_eq]]].
                 subst s1.
                 subst s.
                 exists (link_repr repr_of rx ry).
                 split.
                 --- apply (uf_abstract_link_root_eq
                               s0 repr_of rx ry Habs Hvalid_rx Hvalid_ry
                               Hroot_rx Hroot_ry Hneq Hrank_eq).
                 --- split.
                     +++ apply (merge_transport
                                  (valid s0)
                                  (valid (inc_rank_state ry (set_parent_state rx ry s0)))
                                  repr_of rx ry
                                  (link_repr repr_of rx ry)).
                         *** intros z Hz.
                             pose proof
                               (proj1
                                  (valid_inc_rank_state
                                     (set_parent_state rx ry s0) ry z)
                                  Hz) as Hz_link.
                             apply (proj1 (valid_set_parent_state s0 rx ry z)).
                             exact Hz_link.
                         *** apply (merge_link_repr
                                      s0 repr_of rx ry rx ry
                                      Hvalid_rx Hvalid_ry Hrepr_rx Hrepr_ry Hneq).
                     +++ split.
                         *** apply (proj2 (valid_inc_rank_state
                                             (set_parent_state rx ry s0) ry x)).
                             apply (proj2 (valid_set_parent_state s0 rx ry x)).
                             exact Hvalidx.
                         *** apply (proj2 (valid_inc_rank_state
                                             (set_parent_state rx ry s0) ry y)).
                             apply (proj2 (valid_set_parent_state s0 rx ry y)).
                             exact Hvalidy.
              ** apply (bump_rank_rule
                          (fun s =>
                             s = set_parent_state rx ry s0 /\
                             uf_rank s0 rx = uf_rank s0 ry)
                          ry).
                 intros s [Hs _].
                 subst s.
                 unfold rank_bump_safe.
                 split.
                 --- apply (proj2 (valid_set_parent_state s0 rx ry ry)).
                     exact Hvalid_ry.
                 --- split.
                     +++ rewrite uf_rank_set_parent_state.
                         apply (uf_inv_rank_nonnegative
                                  s0
                                  (uf_abstract_inv s0 repr_of Habs)
                                  ry
                                  Hvalid_ry).
                     +++ rewrite uf_rank_set_parent_state.
                         rewrite uf_size_set_parent_state.
                         pose proof
                           (uf_abstract_rank_class_bound
                              s0 repr_of Habs ry Hvalid_ry (eq_sym Hrepr_ry))
                           as Hrank_bound.
                         pose proof
                           (class_size_upper
                              s0 repr_of ry
                              ltac:(unfold valid in Hvalid_ry; lia))
                         as Hclass_upper.
                         lia.
Qed.

Theorem uf_union_correct :
  forall x y, uf_union_spec x y.
Proof.
  intros x y.
  unfold uf_union_spec.
  intros repr_of.
  unfold uf_union.
  apply (@Hoare_bind elem unit uf_state
           (fun s => uf_abstract s repr_of /\ valid s x /\ valid s y)
           (fun rx s =>
              rx = repr_of x /\
              uf_abstract s repr_of /\
              valid s x /\
              valid s y)
           (fun _ s =>
              exists repr_of',
                uf_abstract s repr_of' /\
                merge (valid s) repr_of x y repr_of')
           (uf_find x)
           (fun rx =>
              ry <- uf_find y;;
              choice
                (assume!! (rx = ry);; ret tt)
                (assume!! (rx <> ry);;
                 rx_rank <- read_rank rx;;
                 ry_rank <- read_rank ry;;
                 choice
                   (assume!! (ry_rank < rx_rank);;
                    write_parent ry rx)
                   (choice
                      (assume!! (rx_rank < ry_rank);;
                       write_parent rx ry)
                      (assume!! (rx_rank = ry_rank);;
                       write_parent rx ry;;
                       bump_rank ry))))).
  - apply uf_find_preserve_valids.
  - intros rx.
    apply (@Hoare_bind elem unit uf_state
             (fun s =>
                rx = repr_of x /\
                uf_abstract s repr_of /\
                valid s x /\
                valid s y)
             (fun ry s =>
                ry = repr_of y /\
                uf_abstract s repr_of /\
                valid s y /\
                valid s x /\
                rx = repr_of x)
             (fun _ s =>
                exists repr_of',
                  uf_abstract s repr_of' /\
                  merge (valid s) repr_of x y repr_of')
             (uf_find y)
             (fun ry =>
                choice
                  (assume!! (rx = ry);; ret tt)
                  (assume!! (rx <> ry);;
                   rx_rank <- read_rank rx;;
                   ry_rank <- read_rank ry;;
                   choice
                     (assume!! (ry_rank < rx_rank);;
                      write_parent ry rx)
                     (choice
                        (assume!! (rx_rank < ry_rank);;
                         write_parent rx ry)
                        (assume!! (rx_rank = ry_rank);;
                         write_parent rx ry;;
                         bump_rank ry))))).
    + apply (@Hoare_cons_pre elem uf_state
               (fun s =>
                  (uf_abstract s repr_of /\ valid s y /\ valid s x) /\
                  rx = repr_of x)
               (fun s =>
                  rx = repr_of x /\
                  uf_abstract s repr_of /\
                  valid s x /\
                  valid s y)
               (uf_find y)
               (fun ry s =>
                  ry = repr_of y /\
                  uf_abstract s repr_of /\
                  valid s y /\
                  valid s x /\
                  rx = repr_of x)).
      * intros s [Hrx [Habs [Hvalidx Hvalidy]]].
        split.
        -- split; [exact Habs |].
           split; [exact Hvalidy | exact Hvalidx].
        -- exact Hrx.
      * apply (@Hoare_stateless' elem uf_state
                 (rx = repr_of x)
                 (fun s => uf_abstract s repr_of /\ valid s y /\ valid s x)
                 (uf_find y)
                 (fun ry s =>
                    ry = repr_of y /\
                    uf_abstract s repr_of /\
                    valid s y /\
                    valid s x /\
                    rx = repr_of x)).
        intros Hrx.
        apply (@Hoare_cons_post elem uf_state
                 (fun s => uf_abstract s repr_of /\ valid s y /\ valid s x)
                 (uf_find y)
                 (fun ry s =>
                    ry = repr_of y /\
                    uf_abstract s repr_of /\
                    valid s y /\
                    valid s x)
                 (fun ry s =>
                    ry = repr_of y /\
                    uf_abstract s repr_of /\
                    valid s y /\
                    valid s x /\
                    rx = repr_of x)).
        -- intros ry s [Hry [Habs [Hvalidy Hvalidx]]].
           split; [exact Hry |].
           split; [exact Habs |].
           split; [exact Hvalidy |].
           split; [exact Hvalidx | exact Hrx].
        -- apply uf_find_preserve_valids.
    + intros ry.
      apply Hoare_choice.
      * apply Hoare_assume_bind.
        intros Hsame.
        apply Hoare_ret.
        intros s [Hry [Habs [Hvalidy [Hvalidx Hrx]]]].
        exists repr_of.
        split; [exact Habs |].
        apply merge_same_class_refl.
        unfold same_class.
        rewrite <- Hrx.
        rewrite Hsame.
        exact Hry.
      * apply Hoare_assume_bind.
        intros Hneq_roots.
        apply (@Hoare_cons_post unit uf_state
                 (fun s =>
                    ry = repr_of y /\
                    uf_abstract s repr_of /\
                    valid s y /\
                    valid s x /\
                    rx = repr_of x)
                 (rx_rank <- read_rank rx;;
                  ry_rank <- read_rank ry;;
                  choice
                    (assume!! (ry_rank < rx_rank);;
                     write_parent ry rx)
                    (choice
                       (assume!! (rx_rank < ry_rank);;
                        write_parent rx ry)
                       (assume!! (rx_rank = ry_rank);;
                        write_parent rx ry;;
                        bump_rank ry)))
                 (fun _ s =>
                    (exists repr_of',
                       uf_abstract s repr_of' /\
                       merge (valid s) repr_of rx ry repr_of' /\
                       valid s x /\
                       valid s y) /\
                    same_class repr_of x rx /\
                    same_class repr_of y ry)
                 (fun _ s =>
                    exists repr_of',
                      uf_abstract s repr_of' /\
                      merge (valid s) repr_of x y repr_of')).
        -- intros [] s [[repr_of' [Habs' [Hmerge [_ _]]]] [Hxclass Hyclass]].
           exists repr_of'.
           split; [exact Habs' |].
           apply (merge_replace_repr_args
                    (valid s) repr_of x y rx ry repr_of'
                    Hxclass Hyclass Hmerge).
        -- apply (@Hoare_cons_pre unit uf_state
                    (fun s =>
                       (uf_abstract s repr_of /\
                        valid s rx /\
                        valid s ry /\
                        rx = repr_of rx /\
                        ry = repr_of ry /\
                        rx <> ry /\
                        valid s x /\
                        valid s y) /\
                       same_class repr_of x rx /\
                       same_class repr_of y ry)
                    (fun s =>
                       ry = repr_of y /\
                       uf_abstract s repr_of /\
                       valid s y /\
                       valid s x /\
                       rx = repr_of x)
                    (rx_rank <- read_rank rx;;
                     ry_rank <- read_rank ry;;
                     choice
                       (assume!! (ry_rank < rx_rank);;
                        write_parent ry rx)
                       (choice
                          (assume!! (rx_rank < ry_rank);;
                           write_parent rx ry)
                          (assume!! (rx_rank = ry_rank);;
                           write_parent rx ry;;
                           bump_rank ry)))
                    (fun _ s =>
                       (exists repr_of',
                          uf_abstract s repr_of' /\
                          merge (valid s) repr_of rx ry repr_of' /\
                          valid s x /\
                          valid s y) /\
                       same_class repr_of x rx /\
                       same_class repr_of y ry)).
           ++ intros s [Hry [Habs [Hvalidy [Hvalidx Hrx]]]].
              pose proof
                (legal_repr_valid s repr_of x (uf_abstract_legal s repr_of Habs) Hvalidx)
                as Hvalid_rx.
              pose proof
                (legal_repr_valid s repr_of y (uf_abstract_legal s repr_of Habs) Hvalidy)
                as Hvalid_ry.
              split.
              ** split; [exact Habs |].
                 split.
                 --- rewrite Hrx.
                     exact Hvalid_rx.
                 --- split.
                     +++ rewrite Hry.
                         exact Hvalid_ry.
                     +++ split.
                         *** rewrite Hrx.
                             symmetry.
                             apply (legal_repr_idem
                                      s repr_of x
                                      (uf_abstract_legal s repr_of Habs)
                                      Hvalidx).
                         *** split.
                             ----- rewrite Hry.
                                   symmetry.
                                   apply (legal_repr_idem
                                            s repr_of y
                                            (uf_abstract_legal s repr_of Habs)
                                            Hvalidy).
                             ----- split.
                                   +++++ exact Hneq_roots.
                                   +++++ split; [exact Hvalidx | exact Hvalidy].
              ** split.
                 --- unfold same_class.
                     rewrite Hrx.
                     symmetry.
                     apply (legal_repr_idem
                              s repr_of x
                              (uf_abstract_legal s repr_of Habs)
                              Hvalidx).
                 --- unfold same_class.
                     rewrite Hry.
                     symmetry.
                     apply (legal_repr_idem
                              s repr_of y
                              (uf_abstract_legal s repr_of Habs)
                              Hvalidy).
           ++ apply (@Hoare_stateless' unit uf_state
                       (same_class repr_of x rx /\ same_class repr_of y ry)
                       (fun s =>
                          uf_abstract s repr_of /\
                          valid s rx /\
                          valid s ry /\
                          rx = repr_of rx /\
                          ry = repr_of ry /\
                          rx <> ry /\
                          valid s x /\
                          valid s y)
                       (rx_rank <- read_rank rx;;
                        ry_rank <- read_rank ry;;
                        choice
                          (assume!! (ry_rank < rx_rank);;
                           write_parent ry rx)
                          (choice
                             (assume!! (rx_rank < ry_rank);;
                              write_parent rx ry)
                             (assume!! (rx_rank = ry_rank);;
                              write_parent rx ry;;
                              bump_rank ry)))
                       (fun _ s =>
                          (exists repr_of',
                             uf_abstract s repr_of' /\
                             merge (valid s) repr_of rx ry repr_of' /\
                             valid s x /\
                             valid s y) /\
                          same_class repr_of x rx /\
                          same_class repr_of y ry)).
              intros Hclasses.
              apply (@Hoare_cons_post unit uf_state
                       (fun s =>
                          uf_abstract s repr_of /\
                          valid s rx /\
                          valid s ry /\
                          rx = repr_of rx /\
                          ry = repr_of ry /\
                          rx <> ry /\
                          valid s x /\
                          valid s y)
                       (rx_rank <- read_rank rx;;
                        ry_rank <- read_rank ry;;
                        choice
                          (assume!! (ry_rank < rx_rank);;
                           write_parent ry rx)
                          (choice
                             (assume!! (rx_rank < ry_rank);;
                              write_parent rx ry)
                             (assume!! (rx_rank = ry_rank);;
                              write_parent rx ry;;
                              bump_rank ry)))
                       (fun _ s =>
                          exists repr_of',
                            uf_abstract s repr_of' /\
                            merge (valid s) repr_of rx ry repr_of' /\
                            valid s x /\
                            valid s y)
                       (fun _ s =>
                          (exists repr_of',
                             uf_abstract s repr_of' /\
                             merge (valid s) repr_of rx ry repr_of' /\
                             valid s x /\
                             valid s y) /\
                          same_class repr_of x rx /\
                          same_class repr_of y ry)).
              ** intros [] s Hlink.
                 split; [exact Hlink | exact Hclasses].
              ** apply (uf_union_link_correct rx ry x y repr_of).
Qed.

End union_find_proofs.
