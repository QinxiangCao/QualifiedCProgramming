Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.

Require Import AUXLib.Axioms.
Require Import AUXLib.Idents.
Require Import AUXLib.Feq.

Section VMap.

Context {A : Type}.

Definition vmap_update (f : var -> A) x v : var -> A :=
  fun y => if var_eqb y x then v else f y.

Fixpoint vmap_update_list (f : var -> A) (xs : list var) (vs : list A) : var -> A :=
  match xs, vs with
  | x :: xs', v :: vs' =>
    vmap_update (vmap_update_list f xs' vs') x v
  | _, _ => f
  end.

Ltac inv H := inversion H; subst; clear H.

#[export] Instance vmap_update_congr0 :
  Proper (f_eq ==> eq ==> eq ==> f_eq) vmap_update.
Proof.
  unfold Proper, respectful, vmap_update, f_eq.
  intros. subst. var_destruct x2 y0; auto.
Qed.

#[export] Instance vmap_update_list_congr0 :
  Proper (f_eq ==> eq ==> eq ==> f_eq) vmap_update_list.
Proof.
  unfold Proper, respectful.
  intros J J' ? xs xs' <- ns ns' <-.
  revert ns. induction xs; intros; destruct ns; simpl in *; auto.
  rewrite IHxs. reflexivity.
Qed.

Lemma vmap_update_eq : forall (J : var -> A) x n,
  vmap_update J x n x = n.
Proof.
  intros. unfold vmap_update.
  rewrite var_eqb_refl. auto.
Qed.


Lemma vmap_update_neq : forall (J : var -> A) x y n,
  x <> y ->
  vmap_update J x n y = J y.
Proof.
  intros. unfold vmap_update.
  var_destruct y x; auto. congruence.
Qed.

Lemma vmap_update_same : forall (J : var -> A) x n1 n2,
  f_eq (vmap_update (vmap_update J x n1) x n2)
       (vmap_update J x n2).
Proof.
  intros. unfold f_eq, vmap_update. intros y.
  var_destruct y x; auto.
Qed.

Lemma vmap_update_perm : forall (J : var -> A) x y n1 n2,
  x <> y ->
  f_eq (vmap_update (vmap_update J x n1) y n2)
       (vmap_update (vmap_update J y n2) x n1).
Proof.
  intros. unfold f_eq, vmap_update. intros z.
  var_destruct z y; var_destruct z x; congruence.
Qed.

Lemma vmap_update_perm_list : forall (J : var -> A) x ys n ns,
  ~ In x ys ->
  f_eq (vmap_update_list (vmap_update J x n) ys ns)
       (vmap_update (vmap_update_list J ys ns) x n).
Proof.
  induction ys; intros; simpl.
  - reflexivity.
  - destruct ns; simpl.
    + reflexivity.
    + assert (x <> a).
      { contradict H. subst. left. auto. }
      assert (~ In x ys).
      { contradict H. right. auto. }
      rewrite vmap_update_perm by congruence.
      rewrite IHys; auto.
      reflexivity.
Qed.

Lemma vmap_update_congr : forall (P : var -> Prop) J J' x n,
  (forall y, P y -> J y = J' y) ->
  forall y, P y ->
  vmap_update J x n y = vmap_update J' x n y.
Proof.
  intros.
  unfold vmap_update.
  var_destruct y x; auto.
Qed.

Lemma vmap_update_list_congr : forall (P : var -> Prop) J J' xs ns,
  (forall y, P y -> J y = J' y) ->
  forall y, P y ->
  vmap_update_list J xs ns y = vmap_update_list J' xs ns y.
Proof.
  intros.
  revert ns. generalize dependent y.
  induction xs; destruct ns; simpl; auto.
  - apply (vmap_update_congr P); auto.
Qed.

Lemma vmap_update_list_notin : forall J xs ns x,
  ~ In x xs ->
  vmap_update_list J xs ns x = J x.
Proof.
  induction xs; intros; destruct ns; simpl in *; auto.
  rewrite vmap_update_neq by tauto.
  apply IHxs. tauto.
Qed.

Lemma vmap_update_list_same : forall J xs x,
  vmap_update_list J xs (map J xs) x = J x.
Proof.
  intros. induction xs; simpl.
  - reflexivity.
  - unfold vmap_update.
    var_destruct x a; subst; auto.
Qed.

Lemma vmap_update_list_app : forall J xs ys ns1 ns2 x,
  length xs = length ns1 ->
  vmap_update_list J (xs ++ ys) (ns1 ++ ns2) x =
  vmap_update_list (vmap_update_list J ys ns2) xs ns1 x.
Proof.
  induction xs; intros; destruct ns1; simpl in *; intros; auto; try lia.
  unfold vmap_update. var_destruct x a; auto.
Qed.

Lemma vmap_update_list_app_skip1 : forall J xs ys ns1 ns2 x,
  length xs = length ns1 ->
  ~ In x xs ->
  vmap_update_list J (xs ++ ys) (ns1 ++ ns2) x =
  vmap_update_list J ys ns2 x.
Proof.
  intros. rewrite vmap_update_list_app; auto.
  rewrite vmap_update_list_notin; auto.
Qed.

Lemma vmap_update_list_app_skip2 : forall J xs ys ns1 ns2 x,
  length xs = length ns1 ->
  ~ In x ys ->
  vmap_update_list J (xs ++ ys) (ns1 ++ ns2) x =
  vmap_update_list J xs ns1 x.
Proof.
  intros. rewrite vmap_update_list_app; auto.
  destruct (In_dec var_dec x xs).
  - generalize dependent ns1.
    induction xs; intros; destruct ns1; simpl in *; auto; try lia.
    unfold vmap_update. var_destruct x a; auto.
    apply IHxs; try lia.
    destruct i; congruence.
  - rewrite ! vmap_update_list_notin; auto.
Qed.

Lemma vmap_update_list_in : forall J1 J2 xs ns x,
  In x xs ->
  length xs = length ns ->
  vmap_update_list J1 xs ns x = vmap_update_list J2 xs ns x.
Proof.
  induction xs; intros; destruct ns; simpl in *; try contradiction; try lia.
  inv H0. var_destruct a x.
  - subst. unfold vmap_update. rewrite var_eqb_refl. auto.
  - destruct H; [congruence | ].
    rewrite ! vmap_update_neq by auto.
    apply IHxs; auto.
Qed.

Lemma vmap_update_update_list_in : forall J xs ns x n,
  In x xs ->
  length xs = length ns ->
  f_eq (vmap_update_list (vmap_update J x n) xs ns)
       (vmap_update_list J xs ns).
Proof.
  induction xs; intros; simpl.
  - inv H.
  - destruct ns; simpl in *; [lia | ].
    inv H0. var_destruct a x.
    + subst. unfold f_eq. intros y. unfold vmap_update.
      var_destruct y x; auto.
      destruct (in_dec var_dec y xs).
      * apply vmap_update_list_in; auto.
      * rewrite ! vmap_update_list_notin; auto.
        apply var_eqb_neq in E. rewrite E. auto.
    + destruct H; [congruence | ]. rewrite IHxs; auto. reflexivity.
Qed.

Lemma vmap_repair_eq : forall (l1 l2 : var -> A) x,
  (forall y, y <> x -> l1 y = l2 y) ->
  f_eq l1 (vmap_update l2 x (l1 x)).
Proof.
  intros. unfold f_eq, vmap_update.
  intros y. var_destruct y x; subst; auto.
Qed.

Lemma vmap_repair_eq' : forall (l1 l2 : var -> A) x,
  (forall y, y <> x -> l1 y = l2 y) ->
  (vmap_update l2 x (l1 x)) = l1.
Proof.
  intros. pose proof (vmap_repair_eq l1 l2 x H).
  apply functional_extensionality in H0.
  auto.
Qed.

End VMap.
