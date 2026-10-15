Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.PeanoNat.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition TripleStep (a b:list Z) : Prop :=
  exists i j,0 <= i < Zlength a /\ 0 <= j < Zlength a /\ i <> j /\
    b=replace_Znth j (Znth j a 0/3) (replace_Znth i (3*Znth i a 0) a).
Definition TripleReach (l r moves:Z) : Prop :=
  exists st:list(list Z),Zlength st=moves+1 /\ Znth 0 st []=Zrange l (r+1) /\
    (forall q,0 <= q < moves -> TripleStep(Znth q st[])(Znth(q+1)st[])) /\
    Forall(fun x=>x=0)(Znth moves st []).
Definition Pre (l r:Z) : Prop :=
  (* Every clause below is stated explicitly in the P034 solver Require, which
     therefore omits the Pre(l, r) call:
       1 <= l < r /\ r <= 200000. *)
  True.
Definition Spec (l r out:Z) : Prop :=
  min_value_of_subset Z.le (fun q=>q >= 0 /\ TripleReach l r q) (fun x => x) out.

(* Contents of the two precomputed tables the solver reads: fvs.[i] counts the
   base-3 digits of i and pres.[i] accumulates fvs over 1..i, each stated as the
   recurrence that determines it from index 0 upwards. *)
Definition TripleTablesBridge (fvs pres : list Z) : Prop :=
  Zlength fvs = 200005 /\
  Zlength pres = 200005 /\
  Znth 0 fvs 0 = 0 /\
  Znth 0 pres 0 = 0 /\
  (forall i, 1 <= i < 200005 -> Znth i fvs 0 = Znth (i / 3) fvs 0 + 1) /\
  (forall i, 1 <= i < 200005 ->
     Znth i pres 0 = Znth (i - 1) pres 0 + Znth i fvs 0).

(* A prefix form of [TripleTablesBridge], used while the two global tables are
   initialized.  The numeric bounds are conservative C-safety facts; the two
   recurrence clauses carry the mathematical table meaning. *)
Definition TripleTablesPrefix (fvs pres : list Z) (n : Z) : Prop :=
  Zlength fvs = n /\
  Zlength pres = n /\
  1 <= n <= 200005 /\
  Znth 0 fvs 0 = 0 /\
  Znth 0 pres 0 = 0 /\
  (forall i, 0 <= i < n -> 0 <= Znth i fvs 0 <= i) /\
  (forall i, 0 <= i < n -> 0 <= Znth i pres 0 <= 200005 * i) /\
  (forall i, 1 <= i < n ->
     Znth i fvs 0 = Znth (i / 3) fvs 0 + 1) /\
  (forall i, 1 <= i < n ->
     Znth i pres 0 = Znth (i - 1) pres 0 + Znth i fvs 0).

(* The already-written output prefix satisfies the frozen per-query result
   relation. *)
Definition TripleOutputsPrefix
    (ls rs outs : list Z) (n : Z) : Prop :=
  Zlength outs = n /\
  (forall i, 0 <= i < n ->
     Spec (Znth i ls 0) (Znth i rs 0) (Znth i outs 0)).

(* Canonical base-three potential used to connect the table recurrence with
   the operational relation. *)
Program Fixpoint triple_digits_nat (n : nat) {measure n} : nat :=
  match n with
  | O => O
  | S k => S (triple_digits_nat (Nat.div (S k) 3%nat))
  end.
Next Obligation.
  change (Nat.div (S k) 3 < S k)%nat.
  apply Nat.div_lt; lia.
Qed.

Lemma triple_digits_nat_unfold : forall n,
  triple_digits_nat n =
  match n with
  | O => O
  | S k => S (triple_digits_nat (Nat.div (S k) 3%nat))
  end.
Proof.
  intro n.
  WfExtensionality.unfold_sub triple_digits_nat (triple_digits_nat n).
  destruct n; reflexivity.
Qed.

Definition TripleDigits (x : Z) : Z :=
  Z.of_nat (triple_digits_nat (Z.to_nat x)).

Fixpoint TriplePotential (a : list Z) : Z :=
  match a with
  | [] => 0
  | x :: xs => TripleDigits x + TriplePotential xs
  end.

Fixpoint TripleMinDigits (a : list Z) : Z :=
  match a with
  | [] => 0
  | x :: xs =>
      match xs with
      | [] => TripleDigits x
      | _ => Z.min (TripleDigits x) (TripleMinDigits xs)
      end
  end.

Definition TripleRank (a : list Z) : Z :=
  TriplePotential a +
  if in_dec Z.eq_dec 0 a then 0 else TripleMinDigits a.

Definition TripleClosedFormBridge (fvs pres : list Z) : Prop :=
  forall l r,
    1 <= l < r /\ r <= 200000 ->
    Spec l r
      (2 * Znth l fvs 0 + (Znth r pres 0 - Znth l pres 0)).

Lemma triple_digits_nat_0 : triple_digits_nat 0 = 0%nat.
Proof. rewrite triple_digits_nat_unfold. reflexivity. Qed.

Lemma triple_digits_nat_pos : forall n,
  n <> 0%nat ->
  triple_digits_nat n = S (triple_digits_nat (Nat.div n 3)).
Proof.
  intros [|n] H; [contradiction|].
  rewrite triple_digits_nat_unfold. reflexivity.
Qed.

Lemma TripleDigits_nonneg : forall x, 0 <= TripleDigits x.
Proof. intros; unfold TripleDigits; lia. Qed.

Lemma TripleDigits_0 : TripleDigits 0 = 0.
Proof. unfold TripleDigits; simpl; reflexivity. Qed.

Lemma TripleDigits_pos : forall x,
  0 < x -> 0 < TripleDigits x.
Proof.
  intros x Hx. unfold TripleDigits.
  assert (Z.to_nat x <> 0%nat) by (intro H; apply (f_equal Z.of_nat) in H;
    rewrite Z2Nat.id in H by lia; simpl in H; lia).
  rewrite triple_digits_nat_pos by exact H.
  lia.
Qed.

Lemma TripleDigits_eq_zero : forall x,
  0 <= x -> (TripleDigits x = 0 <-> x = 0).
Proof.
  intros x Hx; split; intros H.
  - destruct (Z.eq_dec x 0); auto.
    pose proof (TripleDigits_pos x ltac:(lia)); lia.
  - subst; apply TripleDigits_0.
Qed.

Lemma TripleDigits_div3 : forall x,
  0 < x -> TripleDigits (x / 3) = TripleDigits x - 1.
Proof.
  intros x Hx.
  unfold TripleDigits.
  rewrite Z2Nat.inj_div by lia.
  replace (Z.to_nat 3) with 3%nat by reflexivity.
  assert (Hnz : Z.to_nat x <> 0%nat).
  { intro Hzero.
    apply (f_equal Z.of_nat) in Hzero.
    rewrite Z2Nat.id in Hzero by lia.
    simpl in Hzero; lia. }
  rewrite (triple_digits_nat_pos (Z.to_nat x) Hnz).
  rewrite Nat2Z.inj_succ. ring.
Qed.

Lemma TripleDigits_mul3 : forall x,
  0 < x -> TripleDigits (3 * x) = TripleDigits x + 1.
Proof.
  intros x Hx.
  pose proof (TripleDigits_div3 (3 * x) ltac:(lia)) as H.
  replace (3 * x / 3) with x in H by
    (rewrite Z.mul_comm, Z.div_mul; lia).
  lia.
Qed.

Lemma TriplePotential_nonneg : forall a,
  0 <= TriplePotential a.
Proof.
  induction a; simpl; [lia|].
  pose proof (TripleDigits_nonneg a). lia.
Qed.

Lemma TriplePotential_replace : forall a i v,
  0 <= i < Zlength a ->
  TriplePotential (replace_Znth i v a) =
  TriplePotential a - TripleDigits (Znth i a 0) + TripleDigits v.
Proof.
  induction a as [|x xs IH]; intros i v Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + unfold replace_Znth, Znth; simpl; ring.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia.
      simpl. rewrite IH by lia. ring.
Qed.

Lemma Forall_replace_Znth_triple : forall (P : Z -> Prop) a i v,
  Forall P a -> P v -> Forall P (replace_Znth i v a).
Proof.
  intros P a i v Ha Hv.
  unfold replace_Znth.
  remember (Z.to_nat i) as n; clear i Heqn.
  revert n.
  induction Ha; intros n; simpl; [constructor|].
  destruct n; constructor; auto.
Qed.

Lemma TripleMinDigits_nonneg : forall a,
  0 <= TripleMinDigits a.
Proof.
  induction a as [|x xs IH]; simpl; [lia|].
  destruct xs; simpl in *; pose proof (TripleDigits_nonneg x); lia.
Qed.

Lemma TripleMinDigits_le_member : forall a x,
  a <> [] -> In x a -> TripleMinDigits a <= TripleDigits x.
Proof.
  induction a as [|y ys IH]; intros x Hne Hin; [contradiction|].
  simpl in Hin. destruct ys as [|z zs].
  - simpl in *. destruct Hin as [->|[]]; lia.
  - simpl. destruct Hin as [->|Hin]; [apply Z.le_min_l|].
    eapply Z.le_trans; [apply Z.le_min_r|].
    apply IH; [discriminate|exact Hin].
Qed.

Lemma TripleMinDigits_lower : forall a k,
  a <> [] -> Forall (fun x => k <= TripleDigits x) a ->
  k <= TripleMinDigits a.
Proof.
  induction a as [|x xs IH]; intros k Hne Hall; [contradiction|].
  inversion Hall as [|? ? Hx Hxs]; subst.
  destruct xs as [|y ys].
  - simpl; exact Hx.
  - simpl. apply Z.min_glb; [exact Hx|].
    apply IH; [discriminate|exact Hxs].
Qed.

Lemma TripleMinDigits_member : forall a,
  a <> [] -> exists x, In x a /\ TripleDigits x = TripleMinDigits a.
Proof.
  induction a as [|x xs IH]; intros Hne; [contradiction|].
  destruct xs as [|y ys].
  - exists x; simpl; auto.
  - destruct (IH ltac:(discriminate)) as [m [Hm Hdm]].
    simpl. destruct (Z_le_dec (TripleDigits x) (TripleMinDigits (y :: ys))).
    + exists x. split; [left; reflexivity|]. rewrite Z.min_l by exact l; reflexivity.
    + exists m. split; [right; exact Hm|].
      rewrite Z.min_r; [exact Hdm|].
      apply Z.lt_le_incl. apply Z.nle_gt. exact n.
Qed.

Lemma TripleDigits_mul3_ge : forall x,
  0 <= x -> TripleDigits x <= TripleDigits (3 * x).
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|Hne].
  - replace (3 * 0) with 0 by ring. rewrite TripleDigits_0. lia.
  - rewrite TripleDigits_mul3 by lia. lia.
Qed.

Lemma TripleDigits_div3_ge : forall x,
  0 <= x -> TripleDigits x - 1 <= TripleDigits (x / 3).
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|Hne].
  - replace (0 / 3) with 0 by reflexivity. rewrite TripleDigits_0. lia.
  - rewrite TripleDigits_div3 by lia. lia.
Qed.

Lemma Forall_nonneg_Znth : forall a i,
  Forall (fun x => 0 <= x) a -> 0 <= i < Zlength a ->
  0 <= Znth i a 0.
Proof.
  induction a as [|x xs IH]; intros i Hall Hi.
  - rewrite Zlength_nil in Hi; lia.
  - inversion Hall; subst. rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + unfold Znth; simpl; assumption.
    + rewrite Znth_cons by lia. apply IH; auto; lia.
Qed.

Lemma Znth_In_triple : forall (a : list Z) (i d : Z),
  0 <= i < Zlength a -> In (Znth i a d) a.
Proof.
  induction a as [|x xs IH]; intros i d Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + left. reflexivity.
    + right. rewrite Znth_cons by lia. apply IH. lia.
Qed.

Lemma Forall_digits_min : forall a,
  a <> [] ->
  Forall (fun x => TripleMinDigits a <= TripleDigits x) a.
Proof.
  intros a Hne. apply Forall_forall. intros x Hx.
  apply TripleMinDigits_le_member; auto.
Qed.

Lemma Forall_weaken_digits : forall a k,
  Forall (fun x => k <= TripleDigits x) a ->
  Forall (fun x => k - 1 <= TripleDigits x) a.
Proof.
  intros a k H. induction H; constructor; auto; lia.
Qed.

Lemma TriplePotential_step : forall a b,
  Forall (fun x => 0 <= x) a -> TripleStep a b ->
  TriplePotential a - 1 <= TriplePotential b /\
  (~ In 0 a -> TriplePotential b = TriplePotential a).
Proof.
  intros a b Hnonneg [i [j [Hi [Hj [Hneq ->]]]]].
  set (ai := Znth i a 0).
  set (aj := Znth j a 0).
  assert (Hai : 0 <= ai) by (unfold ai; eapply Forall_nonneg_Znth; eauto).
  assert (Haj : 0 <= aj) by (unfold aj; eapply Forall_nonneg_Znth; eauto).
  assert (Hlen : Zlength (replace_Znth i (3 * ai) a) = Zlength a)
    by apply ListLib.Zlength_replace_Znth.
  assert (Hjval : Znth j (replace_Znth i (3 * ai) a) 0 = aj).
  { unfold aj. apply Znth_replace_Znth_Diff; auto. }
  rewrite TriplePotential_replace by (rewrite Hlen; exact Hj).
  rewrite Hjval.
  rewrite TriplePotential_replace by exact Hi.
  fold ai.
  split.
  - assert (Hmul : 0 <= TripleDigits (3 * ai) - TripleDigits ai)
      by (pose proof (TripleDigits_mul3_ge ai Hai); lia).
    assert (Hdiv : -1 <= TripleDigits (aj / 3) - TripleDigits aj)
      by (pose proof (TripleDigits_div3_ge aj Haj); lia).
    replace (TriplePotential a - TripleDigits ai + TripleDigits (3 * ai) -
      TripleDigits aj + TripleDigits (aj / 3)) with
      (TriplePotential a +
       (TripleDigits (3 * ai) - TripleDigits ai) +
       (TripleDigits (aj / 3) - TripleDigits aj)) by ring.
    replace (TriplePotential a - 1) with
      (TriplePotential a + (0 + -1)) by ring.
    replace (TriplePotential a +
      (TripleDigits (3 * ai) - TripleDigits ai) +
      (TripleDigits (aj / 3) - TripleDigits aj)) with
      (TriplePotential a +
       ((TripleDigits (3 * ai) - TripleDigits ai) +
        (TripleDigits (aj / 3) - TripleDigits aj))) by ring.
    apply Z.add_le_mono_l.
    apply Z.add_le_mono; assumption.
  - intros Hnozero.
    assert (0 < ai).
    { destruct (Z.eq_dec ai 0) as [Heq|Hne].
      - exfalso. apply Hnozero. unfold ai in Heq.
        rewrite <- Heq. apply Znth_In_triple. exact Hi.
      - lia. }
    assert (0 < aj).
    { destruct (Z.eq_dec aj 0) as [Heq|Hne].
      - exfalso. apply Hnozero. unfold aj in Heq.
        rewrite <- Heq. apply Znth_In_triple. exact Hj.
      - lia. }
    rewrite TripleDigits_mul3 by lia.
    rewrite TripleDigits_div3 by lia. ring.
Qed.

Lemma In_replace_Znth_inv_triple : forall (x : Z) (a : list Z) (i v : Z),
  In x (replace_Znth i v a) -> x = v \/ In x a.
Proof.
  intros x a i v H.
  unfold replace_Znth in H.
  remember (Z.to_nat i) as n; clear i Heqn.
  revert n H. induction a as [|y ys IH]; intros n H; simpl in H; [contradiction|].
  destruct n.
  - simpl in H. destruct H; [left; auto|right; right; auto].
  - simpl in H. destruct H; [right; left; auto|].
    destruct (IH n H); [left|right; right]; auto.
Qed.

Lemma TripleStep_nonneg : forall a b,
  Forall (fun x => 0 <= x) a -> TripleStep a b ->
  Forall (fun x => 0 <= x) b.
Proof.
  intros a b Hnonneg [i [j [Hi [Hj [Hneq ->]]]]].
  apply Forall_replace_Znth_triple.
  - apply Forall_replace_Znth_triple; [exact Hnonneg|].
    pose proof (Forall_nonneg_Znth a i Hnonneg Hi). nia.
  - pose proof (Forall_nonneg_Znth a j Hnonneg Hj).
    apply Z_div_nonneg_nonneg; lia.
Qed.

Lemma TripleMinDigits_pos_nozero : forall a,
  a <> [] -> Forall (fun x => 0 <= x) a -> ~ In 0 a ->
  0 < TripleMinDigits a.
Proof.
  intros a Hne Hnonneg Hnozero.
  destruct (TripleMinDigits_member a Hne) as [x [Hin Heq]].
  assert (0 < x).
  { apply Forall_forall with (x := x) in Hnonneg; auto.
    destruct (Z.eq_dec x 0); [subst; contradiction|lia]. }
  pose proof (TripleDigits_pos x H). lia.
Qed.

Lemma TripleRank_step : forall a b,
  a <> [] -> Forall (fun x => 0 <= x) a -> TripleStep a b ->
  TripleRank a - 1 <= TripleRank b.
Proof.
  intros a b Hane Hnonneg Hstep.
  pose proof (TriplePotential_step a b Hnonneg Hstep) as [Hpot Hpot_nozero].
  pose proof (TripleStep_nonneg a b Hnonneg Hstep) as Hbnonneg.
  assert (Hblen : Zlength b = Zlength a).
  { destruct Hstep as [i [j [Hi [Hj [Hneq ->]]]]].
    repeat rewrite ListLib.Zlength_replace_Znth. reflexivity. }
  assert (Hbne : b <> []).
  { intro Hb. subst b. rewrite Zlength_nil in Hblen.
    destruct a as [|x xs]; [apply Hane; reflexivity|].
    rewrite Zlength_cons in Hblen.
    pose proof (Zlength_nonneg xs). lia. }
  unfold TripleRank.
  destruct (in_dec Z.eq_dec 0 a) as [Hza|Hnza].
  - destruct (in_dec Z.eq_dec 0 b) as [Hzb|Hnzb]; simpl.
    + lia.
    + pose proof (TripleMinDigits_nonneg b). lia.
  - rewrite Hpot_nozero by exact Hnza.
    destruct (in_dec Z.eq_dec 0 b) as [Hzb|Hnzb]; simpl.
    + assert (Hminone : TripleMinDigits a = 1).
      { destruct Hstep as [i [j [Hi [Hj [Hneq Hb]]]]].
        subst b.
        apply In_replace_Znth_inv_triple in Hzb.
        destruct Hzb as [Hdivzero|Hzinner].
        - assert (Haj : 0 < Znth j a 0).
          { pose proof (Forall_nonneg_Znth a j Hnonneg Hj).
            destruct (Z.eq_dec (Znth j a 0) 0) as [Heq|Hne].
            - exfalso. apply Hnza. rewrite <- Heq.
              apply Znth_In_triple. exact Hj.
            - lia. }
          assert (Hdigits : TripleDigits (Znth j a 0) = 1).
          { pose proof (TripleDigits_div3 (Znth j a 0) Haj).
            rewrite <- Hdivzero, TripleDigits_0 in H. lia. }
          assert (TripleMinDigits a <= 1).
          { rewrite <- Hdigits. apply TripleMinDigits_le_member; auto.
            apply Znth_In_triple. exact Hj. }
          pose proof (TripleMinDigits_pos_nozero a Hane Hnonneg Hnza). lia.
        - apply In_replace_Znth_inv_triple in Hzinner.
          destruct Hzinner as [Hmulzero|Hzold].
          * assert (Hai : 0 < Znth i a 0).
            { pose proof (Forall_nonneg_Znth a i Hnonneg Hi).
              destruct (Z.eq_dec (Znth i a 0) 0) as [Heq|Hne].
              - exfalso. apply Hnza. rewrite <- Heq.
                apply Znth_In_triple. exact Hi.
              - lia. }
            nia.
          * contradiction.
      }
      lia.
    + assert (Hlower : TripleMinDigits a - 1 <= TripleMinDigits b).
      { destruct Hstep as [i [j [Hi [Hj [Hneq Hb]]]]].
        subst b.
        apply TripleMinDigits_lower.
        - intro Hem. apply (f_equal (@Zlength Z)) in Hem.
          repeat rewrite ListLib.Zlength_replace_Znth in Hem.
          rewrite Zlength_nil in Hem.
          destruct a as [|x xs]; [apply Hane; reflexivity|].
          rewrite Zlength_cons in Hem. pose proof (Zlength_nonneg xs). lia.
        - apply Forall_replace_Znth_triple.
          + apply Forall_replace_Znth_triple.
            * apply Forall_weaken_digits. apply Forall_digits_min. exact Hane.
            * pose proof (TripleMinDigits_le_member a (Znth i a 0) Hane
                (Znth_In_triple a i 0 Hi)).
              pose proof (Forall_nonneg_Znth a i Hnonneg Hi).
              pose proof (TripleDigits_mul3_ge (Znth i a 0) H0). lia.
          + pose proof (TripleMinDigits_le_member a (Znth j a 0) Hane
              (Znth_In_triple a j 0 Hj)).
            pose proof (Forall_nonneg_Znth a j Hnonneg Hj).
            pose proof (TripleDigits_div3_ge (Znth j a 0) H0). lia. }
      lia.
Qed.

Lemma In_Znth_index_triple : forall a x,
  In x a -> exists i, 0 <= i < Zlength a /\ Znth i a 0 = x.
Proof.
  induction a as [|y ys IH]; intros x Hin; [contradiction|].
  simpl in Hin. destruct Hin as [->|Hin].
  - exists 0. split; [rewrite Zlength_cons; pose proof (Zlength_nonneg ys); lia|reflexivity].
  - destruct (IH x Hin) as [i [Hi Heq]].
    exists (i + 1). split.
    + rewrite Zlength_cons. lia.
    + rewrite Znth_cons by lia. replace (i + 1 - 1) with i by ring. exact Heq.
Qed.

Lemma not_all_zero_member : forall a,
  ~ Forall (fun x : Z => x = 0) a -> exists x, In x a /\ x <> 0.
Proof.
  induction a as [|x xs IH]; intros Hnot; [exfalso; apply Hnot; constructor|].
  destruct (Z.eq_dec x 0) as [Hx|Hx].
  - destruct (prop_dec (Forall (fun z : Z => z = 0) xs)) as [Hall|Htail].
    + exfalso. apply Hnot. constructor; auto.
    + destruct (IH Htail) as [y [Hy Hyn]]. exists y; split; [right|]; auto.
  - exists x; split; [left; reflexivity|exact Hx].
Qed.

Lemma TriplePotential_zero : forall a,
  Forall (fun x => 0 <= x) a -> TriplePotential a = 0 ->
  Forall (fun x => x = 0) a.
Proof.
  induction a as [|x xs IH]; intros Hnonneg Hpot; [constructor|].
  inversion Hnonneg as [|? ? Hx Hxs]; subst. simpl in Hpot.
  pose proof (TripleDigits_nonneg x).
  pose proof (TriplePotential_nonneg xs).
  assert (Hd : TripleDigits x = 0) by lia.
  constructor.
  - apply (proj1 (TripleDigits_eq_zero x Hx)); exact Hd.
  - apply IH; auto; lia.
Qed.

Lemma TripleRank_zero_all_zero : forall a,
  a <> [] -> Forall (fun x => 0 <= x) a -> TripleRank a = 0 ->
  Forall (fun x => x = 0) a.
Proof.
  intros a Hne Hnonneg Hrank.
  unfold TripleRank in Hrank.
  destruct (in_dec Z.eq_dec 0 a); simpl in Hrank.
  - apply TriplePotential_zero; auto. lia.
  - pose proof (TriplePotential_nonneg a).
    pose proof (TripleMinDigits_nonneg a).
    apply TriplePotential_zero; auto; lia.
Qed.

Lemma TripleRank_all_zero : forall a,
  a <> [] -> Forall (fun x => x = 0) a -> TripleRank a = 0.
Proof.
  intros a Hne Hall.
  assert (Hpot : TriplePotential a = 0).
  { clear Hne. revert Hall. induction a as [|x xs IH]; intros Hz; [reflexivity|].
    inversion Hz as [|? ? Hx Hxs]; subst.
    simpl. apply IH. exact Hxs. }
  unfold TripleRank. rewrite Hpot.
  destruct (in_dec Z.eq_dec 0 a) as [Hin|Hnin]; simpl; [reflexivity|].
  exfalso. apply Hnin.
  destruct a as [|x xs]; [contradiction|].
  inversion Hall; subst. left; reflexivity.
Qed.

Lemma distinct_valid_index : forall (a : list Z) (j : Z),
  2 <= Zlength a -> 0 <= j < Zlength a ->
  exists i, 0 <= i < Zlength a /\ i <> j.
Proof.
  intros a j Hlen Hj. destruct (Z.eq_dec j 0).
  - exists 1; lia.
  - exists 0; lia.
Qed.

Lemma TriplePotential_step_zero_multiplier : forall a i j,
  0 <= i < Zlength a -> 0 <= j < Zlength a -> i <> j ->
  Znth i a 0 = 0 -> 0 < Znth j a 0 ->
  TriplePotential
    (replace_Znth j (Znth j a 0 / 3)
       (replace_Znth i (3 * Znth i a 0) a)) =
  TriplePotential a - 1.
Proof.
  intros a i j Hi Hj Hneq Hizero Hjpos.
  assert (Hlen : Zlength (replace_Znth i (3 * Znth i a 0) a) = Zlength a)
    by apply ListLib.Zlength_replace_Znth.
  rewrite TriplePotential_replace by (rewrite Hlen; exact Hj).
  rewrite Znth_replace_Znth_Diff by auto.
  rewrite TriplePotential_replace by exact Hi.
  rewrite Hizero, TripleDigits_0.
  replace (3 * 0) with 0 by ring. rewrite TripleDigits_0.
  rewrite TripleDigits_div3 by exact Hjpos. ring.
Qed.

Lemma TripleRank_best_step : forall a,
  2 <= Zlength a -> Forall (fun x => 0 <= x) a ->
  ~ Forall (fun x => x = 0) a ->
  exists b, TripleStep a b /\ Forall (fun x => 0 <= x) b /\
    TripleRank b = TripleRank a - 1 /\ Zlength b = Zlength a.
Proof.
  intros a Hlen Hnonneg Hnotzero.
  assert (Hane : a <> []).
  { intro Ha; subst. rewrite Zlength_nil in Hlen; lia. }
  destruct (in_dec Z.eq_dec 0 a) as [Hzero|Hnozero].
  - destruct (In_Znth_index_triple a 0 Hzero) as [i [Hi Hival]].
    destruct (not_all_zero_member a Hnotzero) as [x [Hxin Hxne]].
    destruct (In_Znth_index_triple a x Hxin) as [j [Hj Hjval]].
    assert (Hjpos : 0 < Znth j a 0).
    { rewrite Hjval. apply Forall_forall with (x := x) in Hnonneg; auto; lia. }
    assert (Hneq : i <> j).
    { intro Heq. subst j. rewrite Hival in Hjval. lia. }
    set (b := replace_Znth j (Znth j a 0 / 3)
      (replace_Znth i (3 * Znth i a 0) a)).
    assert (Hstep : TripleStep a b).
    { exists i, j. split; [exact Hi|]. split; [exact Hj|].
      split; [exact Hneq|]. unfold b; reflexivity. }
    exists b. split; [exact Hstep|].
    split; [eapply TripleStep_nonneg; eauto|].
    split.
    + assert (Hbzero : In 0 b).
      { assert (Hbi : Znth i b 0 = 0).
        { unfold b. rewrite Znth_replace_Znth_Diff.
          - rewrite Znth_replace_Znth_Same by exact Hi.
            rewrite Hival. ring.
          - rewrite ListLib.Zlength_replace_Znth. exact Hj.
          - rewrite ListLib.Zlength_replace_Znth. exact Hi.
          - intro Heq. apply Hneq. symmetry. exact Heq. }
        rewrite <- Hbi. apply Znth_In_triple.
        unfold b. repeat rewrite ListLib.Zlength_replace_Znth. exact Hi. }
      unfold TripleRank.
      destruct (in_dec Z.eq_dec 0 a) as [Ha0|Ha0]; [|contradiction].
      destruct (in_dec Z.eq_dec 0 b) as [Hb0|Hb0]; [|contradiction].
      simpl. unfold b.
      rewrite TriplePotential_step_zero_multiplier by auto. ring.
    + unfold b. repeat rewrite ListLib.Zlength_replace_Znth. reflexivity.
  - destruct (TripleMinDigits_member a Hane) as [x [Hxin Hxmin]].
    destruct (In_Znth_index_triple a x Hxin) as [j [Hj Hjval]].
    destruct (distinct_valid_index a j Hlen Hj) as [i [Hi Hneq]].
    set (b := replace_Znth j (Znth j a 0 / 3)
      (replace_Znth i (3 * Znth i a 0) a)).
    assert (Hstep : TripleStep a b).
    { exists i, j. split; [exact Hi|]. split; [exact Hj|].
      split; [exact Hneq|]. unfold b; reflexivity. }
    assert (Hbnonneg : Forall (fun x => 0 <= x) b)
      by (eapply TripleStep_nonneg; eauto).
    assert (Hpot : TriplePotential b = TriplePotential a)
      by (apply (proj2 (TriplePotential_step a b Hnonneg Hstep)); exact Hnozero).
    assert (Hranklower : TripleRank a - 1 <= TripleRank b)
      by (eapply TripleRank_step; eauto).
    exists b. split; [exact Hstep|]. split; [exact Hbnonneg|]. split.
    + unfold TripleRank in *.
      destruct (in_dec Z.eq_dec 0 a) as [Ha0|Ha0]; [contradiction|].
      destruct (in_dec Z.eq_dec 0 b) as [Hb0|Hb0]; simpl in *.
      * assert (Hminpos : 0 < TripleMinDigits a)
          by (eapply TripleMinDigits_pos_nozero; eauto).
        lia.
      * assert (Hbj : Znth j b 0 = Znth j a 0 / 3).
        { unfold b. apply Znth_replace_Znth_Same.
          rewrite ListLib.Zlength_replace_Znth. exact Hj. }
        assert (Hjpos : 0 < Znth j a 0).
        { pose proof (Forall_nonneg_Znth a j Hnonneg Hj).
          destruct (Z.eq_dec (Znth j a 0) 0) as [Heq|Hne].
          - exfalso. apply Hnozero. rewrite <- Heq.
            apply Znth_In_triple. exact Hj.
          - lia. }
        assert (Hminupper : TripleMinDigits b <= TripleMinDigits a - 1).
        { rewrite <- Hxmin, <- Hjval.
          rewrite <- (TripleDigits_div3 (Znth j a 0) Hjpos).
          rewrite <- Hbj. apply TripleMinDigits_le_member.
          - intro Hbempty. apply (f_equal (@Zlength Z)) in Hbempty.
            unfold b in Hbempty. repeat rewrite ListLib.Zlength_replace_Znth in Hbempty.
            rewrite Zlength_nil in Hbempty. lia.
          - apply Znth_In_triple. unfold b.
          repeat rewrite ListLib.Zlength_replace_Znth. exact Hj. }
        lia.
    + unfold b. repeat rewrite ListLib.Zlength_replace_Znth. reflexivity.
Qed.

Inductive TripleSteps : nat -> list Z -> list Z -> Prop :=
| TripleSteps_zero : forall a, TripleSteps O a a
| TripleSteps_succ : forall n a b c,
    TripleStep a b -> TripleSteps n b c -> TripleSteps (S n) a c.

Lemma TripleRank_nonneg : forall a,
  0 <= TripleRank a.
Proof.
  intros a. unfold TripleRank.
  destruct (in_dec Z.eq_dec 0 a); simpl.
  - pose proof (TriplePotential_nonneg a). lia.
  - pose proof (TriplePotential_nonneg a).
    pose proof (TripleMinDigits_nonneg a). lia.
Qed.

Lemma TripleSteps_construct : forall n a,
  2 <= Zlength a -> Forall (fun x => 0 <= x) a ->
  TripleRank a = Z.of_nat n ->
  exists z, TripleSteps n a z /\ Forall (fun x => x = 0) z.
Proof.
  induction n as [|n IH]; intros a Hlen Hnonneg Hrank.
  - exists a. split; [constructor|].
    apply TripleRank_zero_all_zero; auto.
    intro Ha; subst. rewrite Zlength_nil in Hlen; lia.
  - assert (Hnotzero : ~ Forall (fun x => x = 0) a).
    { intro Hall.
      assert (Ha0 : TripleRank a = 0).
      { apply TripleRank_all_zero; auto. intro Ha; subst.
        rewrite Zlength_nil in Hlen; lia. }
      rewrite Ha0 in Hrank. rewrite Nat2Z.inj_succ in Hrank. lia. }
    destruct (TripleRank_best_step a Hlen Hnonneg Hnotzero)
      as [b [Hstep [Hbnonneg [Hbrank Hblen]]]].
    assert (Hbranknat : TripleRank b = Z.of_nat n).
    { rewrite Hbrank, Hrank, Nat2Z.inj_succ. lia. }
    destruct (IH b ltac:(lia) Hbnonneg Hbranknat) as [z [Hsteps Hz]].
    exists z. split; [econstructor; eauto|exact Hz].
Qed.

Lemma TripleSteps_trace : forall n a z,
  TripleSteps n a z ->
  exists st : list (list Z),
    length st = S n /\ nth 0 st [] = a /\
    (forall q : nat, (q < n)%nat ->
       TripleStep (nth q st []) (nth (S q) st [])) /\
    nth n st [] = z.
Proof.
  intros n a z Hsteps. induction Hsteps.
  - exists [a]. repeat split; auto. intros q Hq; lia.
  - destruct IHHsteps as [st [Hlength [Hfirst [Hadj Hlast]]]].
    exists (a :: st). split; [simpl; lia|]. split; [reflexivity|].
    split.
    + intros q Hq. destruct q as [|q].
      * simpl. rewrite Hfirst. exact H.
      * simpl. apply Hadj. lia.
    + simpl. exact Hlast.
Qed.

Lemma TripleSteps_reach : forall n a z,
  TripleSteps n a z -> Forall (fun x => x = 0) z ->
  exists st : list (list Z),
    Zlength st = Z.of_nat n + 1 /\ Znth 0 st [] = a /\
    (forall q, 0 <= q < Z.of_nat n ->
       TripleStep (Znth q st []) (Znth (q + 1) st [])) /\
    Forall (fun x => x = 0) (Znth (Z.of_nat n) st []).
Proof.
  intros n a z Hsteps Hz.
  destruct (TripleSteps_trace n a z Hsteps)
    as [st [Hlength [Hfirst [Hadj Hlast]]]].
  exists st. split.
  - rewrite Zlength_correct, Hlength, Nat2Z.inj_succ. lia.
  - split; [exact Hfirst|]. split.
    + intros q Hq. unfold Znth.
      assert (Hqnat : (Z.to_nat q < n)%nat) by lia.
      replace (Z.to_nat (q + 1)) with (S (Z.to_nat q)).
      * apply Hadj. exact Hqnat.
      * rewrite Z2Nat.inj_add by lia. simpl. lia.
    + unfold Znth. rewrite Nat2Z.id. rewrite Hlast. exact Hz.
Qed.

Lemma TripleReach_rank_upper : forall l r a,
  a = Zrange l (r + 1) -> 2 <= Zlength a ->
  Forall (fun x => 0 <= x) a ->
  TripleReach l r (TripleRank a).
Proof.
  intros l r a Ha Hlen Hnonneg.
  pose proof (TripleRank_nonneg a) as Hranknonneg.
  destruct (TripleSteps_construct (Z.to_nat (TripleRank a)) a Hlen Hnonneg)
    as [z [Hsteps Hz]].
  { rewrite Z2Nat.id by exact Hranknonneg. reflexivity. }
  destruct (TripleSteps_reach _ _ _ Hsteps Hz)
    as [st [Hstlen [Hfirst [Hadj Hlast]]]].
  rewrite Z2Nat.id in Hstlen by exact Hranknonneg.
  rewrite Z2Nat.id in Hadj by exact Hranknonneg.
  rewrite Z2Nat.id in Hlast by exact Hranknonneg.
  exists st. split; [exact Hstlen|]. split.
  - rewrite Hfirst. exact Ha.
  - split; assumption.
Qed.

Lemma TripleStep_length : forall a b,
  TripleStep a b -> Zlength b = Zlength a.
Proof.
  intros a b [i [j [Hi [Hj [Hneq ->]]]]].
  repeat rewrite ListLib.Zlength_replace_Znth. reflexivity.
Qed.

Lemma TripleTrace_state_nat : forall k n st,
  (k <= n)%nat ->
  2 <= Zlength (Znth 0 st []) ->
  Forall (fun x => 0 <= x) (Znth 0 st []) ->
  (forall q, 0 <= q < Z.of_nat n ->
     TripleStep (Znth q st []) (Znth (q + 1) st [])) ->
  Forall (fun x => 0 <= x) (Znth (Z.of_nat k) st []) /\
  Zlength (Znth (Z.of_nat k) st []) = Zlength (Znth 0 st []).
Proof.
  induction k as [|k IH]; intros n st Hkn Hlen Hnonneg Hsteps.
  - simpl. split; auto.
  - destruct (IH n st ltac:(lia) Hlen Hnonneg Hsteps) as [Hknonneg Hklength].
    assert (Hstep : TripleStep (Znth (Z.of_nat k) st [])
      (Znth (Z.of_nat (S k)) st [])).
    { rewrite Nat2Z.inj_succ.
      apply Hsteps. split; lia. }
    split.
    + eapply TripleStep_nonneg; eauto.
    + rewrite (TripleStep_length _ _ Hstep). exact Hklength.
Qed.

Lemma TripleTrace_rank_nat : forall k n st,
  (k <= n)%nat ->
  2 <= Zlength (Znth 0 st []) ->
  Forall (fun x => 0 <= x) (Znth 0 st []) ->
  (forall q, 0 <= q < Z.of_nat n ->
     TripleStep (Znth q st []) (Znth (q + 1) st [])) ->
  TripleRank (Znth 0 st []) <=
    Z.of_nat k + TripleRank (Znth (Z.of_nat k) st []).
Proof.
  induction k as [|k IH]; intros n st Hkn Hlen Hnonneg Hsteps.
  - simpl. lia.
  - pose proof (TripleTrace_state_nat k n st ltac:(lia) Hlen Hnonneg Hsteps)
      as [Hstate_nonneg Hstate_len].
    assert (Hstep : TripleStep (Znth (Z.of_nat k) st [])
      (Znth (Z.of_nat (S k)) st [])).
    { rewrite Nat2Z.inj_succ. apply Hsteps.
      split; lia. }
    assert (Hne : Znth (Z.of_nat k) st [] <> []).
    { intro He. apply (f_equal (@Zlength Z)) in He.
      rewrite Zlength_nil, Hstate_len in He. lia. }
    pose proof (TripleRank_step _ _ Hne Hstate_nonneg Hstep) as Hrankstep.
    pose proof (IH n st ltac:(lia) Hlen Hnonneg Hsteps) as Hprev.
    eapply Z.le_trans; [exact Hprev|].
    assert (Hsucc : Z.of_nat (S k) = Z.of_nat k + 1).
    { rewrite Nat2Z.inj_succ. lia. }
    rewrite Hsucc in Hrankstep |- *.
    replace (Z.of_nat k + 1 + TripleRank (Znth (Z.of_nat k + 1) st [])) with
      (Z.of_nat k + (1 + TripleRank (Znth (Z.of_nat k + 1) st []))) by ring.
    apply Z.add_le_mono_l.
    replace (1 + TripleRank (Znth (Z.of_nat k + 1) st [])) with
      (TripleRank (Znth (Z.of_nat k + 1) st []) + 1) by ring.
    lia.
Qed.

Lemma TripleReach_rank_lower : forall l r moves,
  0 <= moves -> 2 <= Zlength (Zrange l (r + 1)) ->
  Forall (fun x => 0 <= x) (Zrange l (r + 1)) ->
  TripleReach l r moves -> TripleRank (Zrange l (r + 1)) <= moves.
Proof.
  intros l r moves Hmoves Hlen Hnonneg
    [st [Hstlen [Hfirst [Hsteps Hfinal]]]].
  set (n := Z.to_nat moves).
  assert (Hmovesnat : Z.of_nat n = moves).
  { unfold n. apply Z2Nat.id. exact Hmoves. }
  assert (Hstepsnat : forall q, 0 <= q < Z.of_nat n ->
    TripleStep (Znth q st []) (Znth (q + 1) st [])).
  { rewrite Hmovesnat. exact Hsteps. }
  assert (Hinitiallen : 2 <= Zlength (Znth 0 st [])) by (rewrite Hfirst; exact Hlen).
  assert (Hinitialnonneg : Forall (fun x => 0 <= x) (Znth 0 st []))
    by (rewrite Hfirst; exact Hnonneg).
  pose proof (TripleTrace_rank_nat n n st ltac:(lia) Hinitiallen
    Hinitialnonneg Hstepsnat) as Hbound.
  pose proof (TripleTrace_state_nat n n st ltac:(lia) Hinitiallen
    Hinitialnonneg Hstepsnat) as [Hendnonneg Hendlen].
  assert (Hendne : Znth (Z.of_nat n) st [] <> []).
  { intro He. apply (f_equal (@Zlength Z)) in He.
    rewrite Zlength_nil, Hendlen in He. lia. }
  rewrite <- Hmovesnat in Hfinal.
  assert (Hendrank : TripleRank (Znth (Z.of_nat n) st []) = 0).
  { apply TripleRank_all_zero; auto. }
  rewrite Hfirst, Hendrank in Hbound. rewrite Hmovesnat in Hbound. lia.
Qed.

Lemma triple_digits_nat_monotone : forall m n,
  (n <= m)%nat -> (triple_digits_nat n <= triple_digits_nat m)%nat.
Proof.
  intro m. induction m as [m IH] using lt_wf_ind. intros n Hnm.
  destruct m as [|m].
  - assert (n = 0%nat) by lia. subst. lia.
  - destruct n as [|n].
    + rewrite triple_digits_nat_0. lia.
    + replace (triple_digits_nat (S n)) with
        (S (triple_digits_nat (S n / 3))) by
        (symmetry; apply triple_digits_nat_pos; discriminate).
      replace (triple_digits_nat (S m)) with
        (S (triple_digits_nat (S m / 3))) by
        (symmetry; apply triple_digits_nat_pos; discriminate).
      apply le_n_S. apply IH.
      * apply Nat.div_lt; lia.
      * apply Nat.Div0.div_le_mono. exact Hnm.
Qed.

Lemma TripleDigits_monotone : forall x y,
  0 <= x <= y -> TripleDigits x <= TripleDigits y.
Proof.
  intros x y Hxy. unfold TripleDigits.
  apply Nat2Z.inj_le. apply triple_digits_nat_monotone.
  apply Z2Nat.inj_le; lia.
Qed.

Lemma Zlength_Zrange_aux_triple : forall low n,
  Zlength (Zrange_aux low n) = Z.of_nat n.
Proof.
  intros low n. revert low. induction n; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IHn. lia.
Qed.

Lemma Zlength_Zrange_triple : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high H. unfold Zrange.
  rewrite Zlength_Zrange_aux_triple, Z2Nat.id by lia. reflexivity.
Qed.

Lemma Zrange_nonneg_triple : forall low high,
  0 <= low -> Forall (fun x => 0 <= x) (Zrange low high).
Proof.
  intros low high Hlow. apply Forall_forall. intros x Hx.
  apply (proj2 (In_Zrange low high x)) in Hx. lia.
Qed.

Lemma TriplePotential_Zrange : forall low high,
  TriplePotential (Zrange low high) =
  sum (fun x => low <= x < high) TripleDigits.
Proof.
  intros low high. rewrite sum_range_unfold.
  induction (Zrange low high); simpl; [reflexivity|].
  rewrite IHl. reflexivity.
Qed.

Lemma TripleMinDigits_Zrange : forall low high,
  0 <= low < high ->
  TripleMinDigits (Zrange low high) = TripleDigits low.
Proof.
  intros low high Hrange.
  assert (Hne : Zrange low high <> []).
  { intro He. assert (Hin : In low (Zrange low high)).
    { apply (proj1 (In_Zrange low high low)); lia. }
    rewrite He in Hin; contradiction. }
  apply Z.le_antisymm.
  - apply TripleMinDigits_le_member; auto.
    apply (proj1 (In_Zrange low high low)); lia.
  - apply TripleMinDigits_lower; auto.
    apply Forall_forall. intros x Hx. apply TripleDigits_monotone.
    apply (proj2 (In_Zrange low high x)) in Hx. lia.
Qed.

Lemma TripleRank_Zrange : forall low high,
  1 <= low < high ->
  TripleRank (Zrange low high) =
  sum (fun x => low <= x < high) TripleDigits + TripleDigits low.
Proof.
  intros low high Hrange. unfold TripleRank.
  rewrite TriplePotential_Zrange, TripleMinDigits_Zrange by lia.
  destruct (in_dec Z.eq_dec 0 (Zrange low high)) as [Hin|Hnin].
  - apply (proj2 (In_Zrange low high 0)) in Hin. lia.
  - reflexivity.
Qed.

Lemma TripleTables_fvs : forall fvs pres i,
  TripleTablesBridge fvs pres -> 0 <= i < 200005 ->
  Znth i fvs 0 = TripleDigits i.
Proof.
  intros fvs pres i Htables [Hi0 Hiupper].
  destruct Htables as [Hflen [Hplen [Hf0 [Hp0 [Hfrec Hprec]]]]].
  assert (Hbase : 0 <= i) by exact Hi0.
  revert Hi0 Hiupper. pattern i. apply Z_lt_induction.
  intros x IH Hxnonneg Hxupper.
  destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Hf0, TripleDigits_0; reflexivity|].
  rewrite Hfrec by lia.
  assert (Hdivlt : 0 <= x / 3 < x).
  { split; [apply Z_div_nonneg_nonneg; lia|apply Z.div_lt; lia]. }
  assert (Hdivbound : x / 3 < 200005).
  { eapply Z.lt_trans; [exact (proj2 Hdivlt)|lia]. }
  rewrite (IH (x / 3) Hdivlt (proj1 Hdivlt) Hdivbound).
  rewrite TripleDigits_div3 by lia. lia.
  exact Hbase.
Qed.

Lemma TripleTables_pres : forall fvs pres i,
  TripleTablesBridge fvs pres -> 0 <= i < 200005 ->
  Znth i pres 0 = sum (fun x => 1 <= x < i + 1) TripleDigits.
Proof.
  intros fvs pres i Htables [Hi0 Hiupper].
  destruct Htables as [Hflen [Hplen [Hf0 [Hp0 [Hfrec Hprec]]]]].
  assert (Ht : TripleTablesBridge fvs pres).
  { repeat split; assumption. }
  assert (Hbase : 0 <= i) by exact Hi0.
  revert Hi0 Hiupper. pattern i. apply Z_lt_induction.
  intros x IH Hxnonneg Hxupper.
  destruct (Z.eq_dec x 0) as [->|Hx0].
  - rewrite Hp0, sum_Z_range_empty by lia. reflexivity.
  - rewrite Hprec by lia.
    rewrite (IH (x - 1)) by lia.
    rewrite (TripleTables_fvs fvs pres x) by (exact Ht || lia).
    replace (x - 1 + 1) with x by ring.
    rewrite sum_Z_range_extend_right by lia. reflexivity.
  - exact Hbase.
Qed.

Lemma TripleTables_rank_formula : forall fvs pres l r,
  TripleTablesBridge fvs pres -> 1 <= l < r -> r <= 200000 ->
  TripleRank (Zrange l (r + 1)) =
  2 * Znth l fvs 0 + (Znth r pres 0 - Znth l pres 0).
Proof.
  intros fvs pres l r Htables Hlr Hr.
  rewrite TripleRank_Zrange by lia.
  rewrite (TripleTables_fvs fvs pres l) by (exact Htables || lia).
  rewrite (TripleTables_pres fvs pres r) by (exact Htables || lia).
  rewrite (TripleTables_pres fvs pres l) by (exact Htables || lia).
  rewrite (sum_Z_range_split 1 l (r + 1)) by lia.
  rewrite (sum_Z_range_split 1 l (l + 1)) by lia.
  rewrite sum_Z_range_single.
  rewrite (sum_Z_range_split l (l + 1) (r + 1)) by lia.
  rewrite sum_Z_range_single. ring.
Qed.

Lemma TripleSpec_rank : forall l r,
  1 <= l < r ->
  Spec l r (TripleRank (Zrange l (r + 1))).
Proof.
  intros l r Hlr. unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (TripleRank (Zrange l (r + 1))). split.
  - split.
    + split; [pose proof (TripleRank_nonneg (Zrange l (r + 1))); lia|].
      apply TripleReach_rank_upper with (a := Zrange l (r + 1)).
      * reflexivity.
      * rewrite Zlength_Zrange_triple by lia. lia.
      * apply Zrange_nonneg_triple; lia.
    + intros q [Hqnonneg Hqreach].
      apply TripleReach_rank_lower.
      * lia.
      * rewrite Zlength_Zrange_triple by lia. lia.
      * apply Zrange_nonneg_triple; lia.
      * exact Hqreach.
  - reflexivity.
Qed.

Lemma TripleTablesBridge_closed_form : forall fvs pres,
  TripleTablesBridge fvs pres -> TripleClosedFormBridge fvs pres.
Proof.
  intros fvs pres Htables l r [Hlr Hr].
  rewrite <- (TripleTables_rank_formula fvs pres l r Htables Hlr Hr).
  apply TripleSpec_rank. exact Hlr.
Qed.

Lemma Znth_app_last__table_numeric_safety : forall (l : list Z) (x : Z),
  Znth (Zlength l) (l ++ [x]) 0 = x.
Proof.
  intros l x.
  rewrite app_Znth2 by (pose proof (Zlength_nonneg l); lia).
  replace (Zlength l - Zlength l) with 0 by lia.
  rewrite Znth0_cons.
  reflexivity.
Qed.
Lemma triple_tables_prefix_one__table_invariants :
  TripleTablesPrefix [0] [0] 1.
Proof.
  unfold TripleTablesPrefix.
  repeat apply conj.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros j Hj.
    assert (j = 0) by lia. subst j. change (0 <= 0 <= 0). lia.
  - intros j Hj.
    assert (j = 0) by lia. subst j. change (0 <= 0 <= 0). lia.
  - intros j Hj. lia.
  - intros j Hj. lia.
Qed.
Lemma triple_tables_prefix_snoc__table_invariants :
  forall (fvs pres : list Z) (i : Z),
    1 <= i < 200005 ->
    TripleTablesPrefix fvs pres i ->
    TripleTablesPrefix
      (fvs ++ [Znth (i / 3) fvs 0 + 1])
      (pres ++ [Znth (i - 1) pres 0 +
                Znth i (fvs ++ [Znth (i / 3) fvs 0 + 1]) 0])
      (i + 1).
Proof.
  intros fvs pres i Hi HP.
  unfold TripleTablesPrefix in HP |- *.
  destruct HP as
      (Hlf & Hlp & Hn & Hf0 & Hp0 & Hfb & Hpb & Hfr & Hpr).
  assert (Hdiv : 0 <= i / 3 < i) by
      (split; [apply Z.div_pos; lia | apply Z.div_lt; lia]).
  assert (Him1 : 0 <= i - 1 < i) by lia.
  pose proof (Hfb (i / 3) Hdiv) as Hfdiv.
  pose proof (Hpb (i - 1) Him1) as Hpim1.
  repeat apply conj.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlf. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlp. lia.
  - lia.
  - lia.
  - rewrite app_Znth1; auto; lia.
  - rewrite app_Znth1; auto; lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + rewrite app_Znth2 by (rewrite Hlf; lia).
      rewrite Hlf. replace (i - i) with 0 by lia.
      rewrite Znth0_cons.
      lia.
    + rewrite app_Znth1 by (rewrite Hlf; lia).
      apply Hfb. lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + rewrite app_Znth2 by (rewrite Hlp; lia).
      rewrite Hlp. replace (i - i) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth2 by (rewrite Hlf; lia).
      rewrite Hlf. replace (i - i) with 0 by lia.
      rewrite Znth0_cons.
      lia.
    + rewrite app_Znth1 by (rewrite Hlp; lia).
      apply Hpb. lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + rewrite app_Znth2 by (rewrite Hlf; lia).
      rewrite Hlf. replace (i - i) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth1 by (rewrite Hlf; lia).
      reflexivity.
    + rewrite app_Znth1 by (rewrite Hlf; lia).
      assert (Hjdiv : 0 <= j / 3 < i) by
          (split; [apply Z.div_pos; lia |
                   assert (j / 3 < j) by (apply Z.div_lt; lia); lia]).
      rewrite app_Znth1 by (rewrite Hlf; exact Hjdiv).
      apply Hfr. lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hneq].
    + rewrite app_Znth2 by (rewrite Hlp; lia).
      rewrite Hlp. replace (i - i) with 0 by lia.
      rewrite Znth0_cons.
      rewrite (app_Znth1 0 pres _ (i - 1)) by (rewrite Hlp; lia).
      reflexivity.
    + rewrite (app_Znth1 0 pres _ j) by (rewrite Hlp; lia).
      rewrite (app_Znth1 0 pres _ (j - 1)) by (rewrite Hlp; lia).
      rewrite (app_Znth1 0 fvs _ j) by (rewrite Hlf; lia).
      apply Hpr. lia.
Qed.
Lemma triple_tables_prefix_full_bridge__table_invariants :
  forall (fvs pres : list Z),
    TripleTablesPrefix fvs pres 200005 ->
    TripleTablesBridge fvs pres.
Proof.
  intros fvs pres HP.
  unfold TripleTablesPrefix in HP.
  unfold TripleTablesBridge.
  tauto.
Qed.
Lemma Znth_app_left__output_transition : forall (l : list Z) (x d k : Z),
  0 <= k < Zlength l ->
  Znth k (l ++ [x]) d = Znth k l d.
Proof.
  intros l x d k Hk.
  rewrite app_Znth1 by exact Hk.
  reflexivity.
Qed.
Lemma Znth_app_last__output_transition : forall (l : list Z) (x d : Z),
  Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros l x d.
  rewrite app_Znth2 by lia.
  replace (Zlength l - Zlength l) with 0 by lia.
  rewrite Znth0_cons.
  reflexivity.
Qed.
Lemma triple_outputs_prefix_snoc__output_transition :
  forall (ls rs outs : list Z) (i value : Z),
    TripleOutputsPrefix ls rs outs i ->
    Spec (Znth i ls 0) (Znth i rs 0) value ->
    TripleOutputsPrefix ls rs (outs ++ [value]) (i + 1).
Proof.
  intros ls rs outs i value [Hlen Hprefix] Hvalue.
  unfold TripleOutputsPrefix.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen.
    lia.
  - intros k Hk.
    destruct (Z.eq_dec k i) as [-> | Hne].
    + assert (Hlast : Znth i (outs ++ [value]) 0 = value).
      { rewrite <- Hlen.
        apply Znth_app_last__output_transition. }
      rewrite Hlast.
      exact Hvalue.
    + rewrite Znth_app_left__output_transition by lia.
      apply Hprefix.
      lia.
Qed.
