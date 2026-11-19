From Coq Require Import ZArith List Bool Lia FunctionalExtensionality.
From MonadLib Require Import MonadLib.
Export StateRelMonadErr MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.

(** An absent value represents an uninitialised byte. The model does not
    allocate a temporary buffer: [before] is a logical snapshot only. *)
Definition mm_memory := Z -> option Z.
Definition mm_write (m : mm_memory) (p : Z) (v : option Z) : mm_memory :=
  fun a => if Z.eq_dec a p then v else m a.
Definition mm_snapshot (before : mm_memory) (s d n : Z) : mm_memory :=
  fun a => if (d <=? a) && (a <? d+n)
           then before (s+a-d) else before a.

Lemma mm_snapshot_zero : forall m s d, mm_snapshot m s d 0 = m.
Proof.
 intros; apply functional_extensionality; intro a; unfold mm_snapshot.
 destruct (Z.leb_spec0 d a), (Z.ltb_spec0 a (d+0)); cbn; try lia; reflexivity.
Qed.

Lemma mm_snapshot_outside : forall m s d n a,
 a < d \/ d+n <= a -> mm_snapshot m s d n a = m a.
Proof.
 intros; unfold mm_snapshot.
 destruct (Z.leb_spec0 d a), (Z.ltb_spec0 a (d+n)); cbn; intuition lia.
Qed.

Lemma mm_snapshot_inside : forall m s d n a,
 d <= a < d+n -> mm_snapshot m s d n a = m (s+a-d).
Proof.
 intros; unfold mm_snapshot.
 destruct (Z.leb_spec0 d a), (Z.ltb_spec0 a (d+n)); cbn; intuition lia.
Qed.

(** A forward read remains an entry-state read both for left overlap and
    for a disjoint destination to the right. *)
Lemma mm_forward_read : forall m s d n i,
 0 <= i < n -> (d <= s \/ s+n <= d) ->
 mm_snapshot m s d i (s+i) = m (s+i).
Proof. intros; apply mm_snapshot_outside; lia. Qed.

Lemma mm_forward_step : forall m s d n i,
 0 <= i < n -> (d <= s \/ s+n <= d) ->
 mm_write (mm_snapshot m s d i) (d+i)
   (mm_snapshot m s d i (s+i)) = mm_snapshot m s d (i+1).
Proof.
 intros m s d n i Hi Hd. rewrite (mm_forward_read m s d n i Hi Hd).
 apply functional_extensionality; intro a; unfold mm_write.
 destruct (Z.eq_dec a (d+i)) as [->|Hne].
 - rewrite mm_snapshot_inside by lia. f_equal; lia.
 - unfold mm_snapshot.
   destruct (Z.leb_spec0 d a), (Z.ltb_spec0 a (d+i)),
     (Z.ltb_spec0 a (d+(i+1))); cbn; try lia; reflexivity.
Qed.

Lemma mm_backward_read : forall m s d n i,
 s <= d -> 0 < i <= n ->
 mm_snapshot m (s+i) (d+i) (n-i) (s+i-1) = m (s+i-1).
Proof. intros; apply mm_snapshot_outside; lia. Qed.

Lemma mm_backward_step : forall m s d n i,
 s <= d -> 0 < i <= n ->
 mm_write (mm_snapshot m (s+i) (d+i) (n-i)) (d+i-1)
   (mm_snapshot m (s+i) (d+i) (n-i) (s+i-1)) =
 mm_snapshot m (s+(i-1)) (d+(i-1)) (n-(i-1)).
Proof.
 intros m s d n i Hd Hi. rewrite mm_backward_read by lia.
 apply functional_extensionality; intro a; unfold mm_write.
 destruct (Z.eq_dec a (d+i-1)) as [->|Hne].
 - rewrite mm_snapshot_inside by lia. f_equal; lia.
 - unfold mm_snapshot.
   destruct (Z.leb_spec0 (d+i) a), (Z.ltb_spec0 a (d+i+(n-i))),
     (Z.leb_spec0 (d+(i-1)) a),
     (Z.ltb_spec0 a (d+(i-1)+(n-(i-1)))); cbn; try lia;
     try reflexivity; f_equal; lia.
Qed.

(** Each step reads the CURRENT state, then writes the destination. *)
Definition mm_step (s d : Z) : program mm_memory unit :=
  m <- read;; put (mm_write m d (m s)).
Fixpoint mm_forward (s d i : Z) (count : nat) : program mm_memory unit :=
  match count with
  | O => ret tt
  | S k => mm_step (s+i) (d+i);; mm_forward s d (i+1) k
  end.
Fixpoint mm_backward (s d : Z) (count : nat) : program mm_memory unit :=
  match count with
  | O => ret tt
  | S k => mm_step (s+Z.of_nat k) (d+Z.of_nat k);; mm_backward s d k
  end.

Lemma mm_step_correct : forall m s d,
 Hoare (fun st => st = m) (mm_step s d)
       (fun _ st => st = mm_write m d (m s)).
Proof.
 intros; unfold mm_step.
 eapply Hoare_bind with (Q := fun v st => v = m /\ st = m).
 - unfold Hoare, read; cbn; split; intros; intuition congruence.
 - intro v; unfold Hoare, put; cbn; split; intros; intuition congruence.
Qed.

Lemma mm_forward_correct : forall count m s d i n,
 0 <= i -> i + Z.of_nat count = n -> (d <= s \/ s+n <= d) ->
 Hoare (fun st => st = mm_snapshot m s d i) (mm_forward s d i count)
       (fun _ st => st = mm_snapshot m s d n).
Proof.
 induction count as [|k IH]; intros m s d i n Hi Hn Hd; cbn in *.
 - replace n with i by lia. apply Hoare_ret; auto.
 - eapply Hoare_bind with (Q := fun _ st => st = mm_snapshot m s d (i+1)).
   + rewrite <- (mm_forward_step m s d n i) by lia. apply mm_step_correct.
   + intros []; apply IH; try lia; assumption.
Qed.

Lemma mm_backward_correct : forall count m s d n,
 s <= d -> Z.of_nat count <= n ->
 Hoare (fun st => st = mm_snapshot m (s+Z.of_nat count)
                    (d+Z.of_nat count) (n-Z.of_nat count))
       (mm_backward s d count)
       (fun _ st => st = mm_snapshot m s d n).
Proof.
 induction count as [|k IH]; intros m s d n Hd Hn; cbn in *.
 - rewrite !Z.add_0_r, Z.sub_0_r. apply Hoare_ret; auto.
 - eapply Hoare_bind with
     (Q := fun _ st => st = mm_snapshot m (s+Z.of_nat k)
                                 (d+Z.of_nat k) (n-Z.of_nat k)).
   + pose proof (mm_backward_step m s d n (Z.of_nat (S k)) Hd ltac:(lia)) as H.
     replace (Z.of_nat (S k)-1) with (Z.of_nat k) in H by lia.
     replace (d+Z.of_nat (S k)-1) with (d+Z.of_nat k) in H by lia.
     replace (s+Z.of_nat (S k)-1) with (s+Z.of_nat k) in H by lia.
     rewrite <- H. apply mm_step_correct.
   + intros []; apply IH; lia.
Qed.
