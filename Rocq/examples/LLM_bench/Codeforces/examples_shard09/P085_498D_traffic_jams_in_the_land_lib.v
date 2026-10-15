Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition TrafficQuery := (Z * Z * Z)%type.
(* Crossing one segment: two minutes when the moment of arrival is a multiple
   of that segment's period, one minute otherwise. *)
Definition CrossSegment (period times : list Z) (x i : Z) : Prop :=
  ((Znth (x + i - 1) period 2 | Znth i times 0) /\
   Znth (i + 1) times 0 = Znth i times 0 + 2) \/
  (~ (Znth (x + i - 1) period 2 | Znth i times 0) /\
   Znth (i + 1) times 0 = Znth i times 0 + 1).

(* The moments at which a ride leaving x at time zero reaches each crossing. *)
Definition RideTimes (period : list Z) (x y : Z) (times : list Z) : Prop :=
  Zlength times = y - x + 1 /\ Znth 0 times 0 = 0 /\
  forall i, 0 <= i < y - x -> CrossSegment period times x i.

(* How long the ride from x to y takes. *)
Definition RideTime (period : list Z) (x y t : Z) : Prop :=
  1 <= x < y /\ y <= Zlength period + 1 /\
  exists times : list Z, RideTimes period x y times /\ t = Znth (y - x) times 0.

(* How many of the first [i] queries ask for a ride time; it is also the
   position an answer takes in the printed list. *)
Definition AskCount (qs : list TrafficQuery) (i : Z) : Z :=
  #(fun j : Z => 0 <= j < i /\ let ' (d, _, _) := Znth j qs (0, 0, 0) in d = 65).

(* One query: 'C' resets a segment's period, 'A' leaves the road unchanged. *)
Definition QueryStep (qs : list TrafficQuery) (states : list (list Z)) (i : Z) : Prop :=
  let ' (c, x, y) := Znth i qs (0, 0, 0) in
  (c = 67 /\ Znth (i + 1) states [] = replace_Znth (x - 1) y (Znth i states [])) \/
  (c = 65 /\ Znth (i + 1) states [] = Znth i states []).

(* The whole run: the road after every query, and the answer each 'A' query
   contributes, in the order they are printed. *)
Definition TrafficTrace (init : list Z) (qs : list TrafficQuery) (states : list (list Z)) (answers : list Z) : Prop :=
  Zlength states = Zlength qs + 1 /\ Znth 0 states [] = init /\
  Zlength answers = AskCount qs (Zlength qs) /\
  (forall i, 0 <= i < Zlength qs -> QueryStep qs states i) /\
  forall i, 0 <= i < Zlength qs -> let ' (c, x, y) := Znth i qs (0, 0, 0) in c = 65 ->
   exists t, RideTime (Znth i states []) x y t /\
     Znth (AskCount qs i) answers 0 = t.
Definition Pre (init : list Z) (qs : list TrafficQuery) : Prop :=
  (* Every clause below is stated explicitly in the P085 solver Require, which
     therefore omits the Pre(...) call.  The per-query clause is expanded there
     over the three parallel arrays the caller holds, which the Require ties to
     [qs] element by element:
       1 <= Zlength init <= 100000 /\
       Forall (fun x => 2 <= x <= 6) init /\
       1 <= Zlength qs <= 100000 /\
       Forall (fun q => let ' (c, x, y) := q in
         (c = 65 /\ 1 <= x < y /\ y <= Zlength init + 1) \/
         (c = 67 /\ 1 <= x <= Zlength init /\ 2 <= y <= 6)) qs. *)
  True.
Definition Spec (init : list Z) (qs : list TrafficQuery) (out : list Z) : Prop :=
  exists states, TrafficTrace init qs states out.

(* ================================================================== *)
(* Annotation support: the table semantics the segment tree realises.  *)
(* Everything below is new; nothing above this line is touched.        *)
(* ================================================================== *)

(* The clock after crossing a whole block of consecutive segments, starting
   at time [t].  This is the mathematical content of one tree node: a node
   owning the periods [ps] is entirely described by the function [cross ps]. *)
Fixpoint cross (ps : list Z) (t : Z) : Z :=
  match ps with
  | [] => t
  | p :: rest => cross rest (if Z.eqb (t mod p) 0 then t + 2 else t + 1)
  end.

(* Time spent in a block, as a function of the arrival time. *)
Definition delta (ps : list Z) (r : Z) : Z := cross ps r - r.

(* The road periods the statement allows; every one of them divides 60, which
   is why [delta ps] only depends on the arrival time modulo 60. *)
Definition PeriodsOK (ps : list Z) : Prop := Forall (fun p => 2 <= p <= 6) ps.

(* The block of periods a tree node covering the C segments [lo, hi] owns.
   [arr] mirrors a_[1..n], so C segment j is [Znth (j - 1) arr]. *)
Definition NodeSlice (arr : list Z) (lo hi : Z) : list Z := sublist (lo - 1) hi arr.

(* --- tree geometry ------------------------------------------------- *)

(* A node index [v] together with the range [lo, hi] it covers fits inside the
   400020 rows of seg[][] when the subtree below it is shallow enough.  The
   witness [k] bounds that depth: a range of length at most 2 ^ k has a subtree
   whose largest index is below (v + 1) * 2 ^ k. *)
Definition NodeFits (v lo hi : Z) : Prop :=
  1 <= v /\ 1 <= lo /\ lo <= hi /\
  exists k : Z, 0 <= k /\ hi - lo + 1 <= 2 ^ k /\ (v + 1) * 2 ^ k <= 400020.

(* [InSub v lo hi u a b]: the node [u], covering [a, b], is [v] itself or one
   of its descendants in the tree rooted at [v] over [lo, hi]. *)
Inductive InSub : Z -> Z -> Z -> Z -> Z -> Z -> Prop :=
| InSub_self : forall v lo hi, InSub v lo hi v lo hi
| InSub_left : forall v lo hi u a b,
    lo < hi -> InSub (2 * v) lo ((lo + hi) / 2) u a b -> InSub v lo hi u a b
| InSub_right : forall v lo hi u a b,
    lo < hi -> InSub (2 * v + 1) ((lo + hi) / 2 + 1) hi u a b -> InSub v lo hi u a b.

Definition NodeIn (v lo hi u : Z) : Prop := exists a b, InSub v lo hi u a b.

(* --- the stored tables --------------------------------------------- *)

(* Row [v] of seg[][] holds the travel times of the block [ps]: every one of
   the 60 residues is already written and carries the right value. *)
Definition RowIs (cells : list (list (option Z))) (v : Z) (ps : list Z) : Prop :=
  forall r, 0 <= r < 60 -> Znth r (Znth v cells []) None = Some (delta ps r).

(* The same statement restricted to the residues below [k]: what one of the
   60-iteration loops has established so far. *)
Definition RowPrefixIs
    (cells : list (list (option Z))) (v : Z) (ps : list Z) (k : Z) : Prop :=
  forall r, 0 <= r < k -> Znth r (Znth v cells []) None = Some (delta ps r).

(* Every node of the subtree rooted at [v] stores the table of the block it
   covers.  This is the invariant the tree maintains. *)
Definition TreeOK
    (cells : list (list (option Z))) (arr : list Z) (v lo hi : Z) : Prop :=
  forall u a b, InSub v lo hi u a b -> RowIs cells u (NodeSlice arr a b).

(* Frames.  [pull] rewrites exactly one row, [build] and [update] rewrite only
   rows belonging to the subtree they were called on. *)
Definition RowsAgreeExcept
    (v : Z) (cells cells' : list (list (option Z))) : Prop :=
  forall u, u <> v -> Znth u cells' [] = Znth u cells [].

Definition CellsAgreeOutside
    (v lo hi : Z) (cells cells' : list (list (option Z))) : Prop :=
  forall u, ~ NodeIn v lo hi u -> Znth u cells' [] = Znth u cells [].

(* The rectangular shape of seg[][] as a pure fact; [mixed_full] only reports
   the outer length, and the frozen Ensure asks for the row lengths too. *)
Definition CellsShaped (cells : list (list (option Z))) : Prop :=
  Zlength cells = 400020 /\
  forall i, 0 <= i < 400020 -> Zlength (Znth i cells []) = 60.

(* Two roads that differ in at most one segment: what a 'C' query does. *)
Definition AgreeExceptIdx (k : Z) (arr0 arr : list Z) : Prop :=
  Zlength arr0 = Zlength arr /\
  forall j, 0 <= j -> j <> k -> Znth j arr0 0 = Znth j arr 0.

(* --- solver loop state --------------------------------------------- *)

(* The first [i] queries have been replayed on [states]. *)
Definition QueryStepsOK
    (qs : list TrafficQuery) (states : list (list Z)) (i : Z) : Prop :=
  forall j, 0 <= j < i -> QueryStep qs states j.

(* Every 'A' query among the first [i] has already contributed its answer at
   the position the printed list gives it. *)
Definition AnswersOK
    (qs : list TrafficQuery) (states : list (list Z)) (answers : list Z) (i : Z) : Prop :=
  forall j, 0 <= j < i ->
    let ' (c, x, y) := Znth j qs (0, 0, 0) in c = 65 ->
    exists t, RideTime (Znth j states []) x y t /\ Znth (AskCount qs j) answers 0 = t.

(* --- two computation lemmas that pin the definitions down ----------- *)

Lemma cross_nil : forall t, cross [] t = t.
Proof. reflexivity. Qed.

Lemma cross_app : forall ps1 ps2 t,
  cross (ps1 ++ ps2) t = cross ps2 (cross ps1 t).
Proof.
  induction ps1 as [| p ps1 IH]; intros ps2 t; simpl; [reflexivity |].
  apply IH.
Qed.

Lemma delta_single : forall p r,
  delta [p] r = (if Z.eqb (r mod p) 0 then 2 else 1).
Proof.
  intros p r. unfold delta. simpl.
  destruct (Z.eqb (r mod p) 0); ring.
Qed.

(* The block a query call actually crosses inside the node [lo, hi]: the
   requested range clipped to the node.  The recursive descent keeps the two
   ranges overlapping rather than nested. *)
Definition QuerySlice (arr : list Z) (lo hi ql qr : Z) : list Z :=
  NodeSlice arr (Z.max lo ql) (Z.min hi qr).

Definition TreeStaleAt (cells : list (list (option Z))) (arr : list Z)
    (v lo hi pos : Z) : Prop :=
  exists arr0, AgreeExceptIdx (pos - 1) arr0 arr /\ TreeOK cells arr0 v lo hi.

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Psatz.
Lemma nth_replace_nth_diff__pull_merge :
  forall {A : Type} (l : list A) (m n : nat) (x d : A),
  m <> n -> nth n (replace_nth m l x) d = nth n l d.
Proof.
  intros A l. induction l as [| a l IH]; intros m n x d Hmn; simpl.
  - reflexivity.
  - destruct m as [| m']; destruct n as [| n']; simpl.
    + exfalso. apply Hmn. reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. intro Heq. apply Hmn. rewrite Heq. reflexivity.
Qed.
Lemma Znth_replace_Znth_diff__pull_merge :
  forall {A : Type} (l : list A) (i u : Z) (x d : A),
  1 <= i -> u <> i ->
  Znth u (replace_Znth i x l) d = Znth u l d.
Proof.
  intros A l i u x d Hi Hu.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_diff__pull_merge.
  intro Heq. apply Hu. lia.
Qed.
Lemma replace_same_cell__pull_merge :
  forall (row : list (option Z)) (j : Z) (v : Z),
  Znth j row None = Some v ->
  replace_Znth j (Some v) row = row.
Proof.
  intros row j v H. rewrite <- H. apply replace_Znth_Znth.
Qed.
Lemma Forall_firstn__pull_merge :
  forall {A : Type} (P : A -> Prop) (n : nat) (l : list A),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [| n IH]; intros l H; simpl.
  - constructor.
  - destruct l as [| a l]; simpl.
    + constructor.
    + inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.
Lemma Forall_skipn__pull_merge :
  forall {A : Type} (P : A -> Prop) (n : nat) (l : list A),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n. induction n as [| n IH]; intros l H; simpl.
  - assumption.
  - destruct l as [| a l]; simpl.
    + constructor.
    + inversion H; subst. apply IH; assumption.
Qed.
Lemma periods_ok_sublist__pull_merge :
  forall (arr : list Z) (a b : Z),
  PeriodsOK arr -> PeriodsOK (NodeSlice arr a b).
Proof.
  intros arr a b H. unfold PeriodsOK, NodeSlice, sublist in *.
  apply Forall_skipn__pull_merge. apply Forall_firstn__pull_merge. assumption.
Qed.
Lemma node_slice_split__pull_merge :
  forall (arr : list Z) (lo mid hi : Z),
  1 <= lo -> lo <= mid -> mid < hi -> hi <= Zlength arr ->
  NodeSlice arr lo hi = NodeSlice arr lo mid ++ NodeSlice arr (mid + 1) hi.
Proof.
  intros arr lo mid hi H1 H2 H3 H4. unfold NodeSlice.
  replace (mid + 1 - 1) with mid by lia.
  apply sublist_split; lia.
Qed.
Lemma delta_merge__pull_merge :
  forall (ps1 ps2 : list Z) (r : Z),
  delta (ps1 ++ ps2) r = delta ps1 r + delta ps2 (r + delta ps1 r).
Proof.
  intros ps1 ps2 r. unfold delta. rewrite cross_app.
  replace (r + (cross ps1 r - r)) with (cross ps1 r) by lia.
  lia.
Qed.
Lemma small_period_divides_60__pull_merge :
  forall p : Z, 2 <= p <= 6 -> (p | 60).
Proof.
  intros p Hp.
  assert (Hcase : p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6) by lia.
  destruct Hcase as [H | [H | [H | [H | H]]]]; subst.
  - exists 30. reflexivity.
  - exists 20. reflexivity.
  - exists 15. reflexivity.
  - exists 12. reflexivity.
  - exists 10. reflexivity.
Qed.
Lemma delta_congr60__pull_merge :
  forall (ps : list Z) (t1 t2 : Z),
  PeriodsOK ps -> t1 mod 60 = t2 mod 60 -> delta ps t1 = delta ps t2.
Proof.
  intros ps. induction ps as [| p ps IH]; intros t1 t2 Hok Hmod.
  - unfold delta. cbn [cross]. lia.
  - unfold PeriodsOK in Hok.
    assert (Hp : 2 <= p <= 6) by (apply (Forall_inv Hok)).
    assert (Hps : PeriodsOK ps) by (apply (Forall_inv_tail Hok)).
    assert (Hp60 : t1 mod p = t2 mod p).
    { rewrite (Zmod_div_mod p 60 t1) by (try lia; apply small_period_divides_60__pull_merge; lia).
      rewrite (Zmod_div_mod p 60 t2) by (try lia; apply small_period_divides_60__pull_merge; lia).
      rewrite Hmod. reflexivity. }
    assert (Hstep : forall t : Z,
      delta (p :: ps) t
        = (if Z.eqb (t mod p) 0 then 2 else 1)
          + delta ps (if Z.eqb (t mod p) 0 then t + 2 else t + 1)).
    { intro t. unfold delta. cbn [cross].
      destruct (Z.eqb (t mod p) 0); lia. }
    rewrite (Hstep t1), (Hstep t2), Hp60.
    assert (Hd : forall c : Z, delta ps (t1 + c) = delta ps (t2 + c)).
    { intro c. apply IH; [assumption |].
      rewrite Z.add_mod by lia. rewrite (Z.add_mod t2 c) by lia.
      rewrite Hmod. reflexivity. }
    destruct (Z.eqb (t2 mod p) 0).
    + rewrite (Hd 2). reflexivity.
    + rewrite (Hd 1). reflexivity.
Qed.
Lemma delta_mod60__pull_merge :
  forall (ps : list Z) (t : Z),
  PeriodsOK ps -> delta ps t = delta ps (t mod 60).
Proof.
  intros ps t Hok. apply delta_congr60__pull_merge; [assumption |].
  rewrite Zmod_mod. reflexivity.
Qed.
Lemma length_replace_nth__pull_merge :
  forall {A : Type} (l : list A) (n : nat) (x : A),
  length (replace_nth n l x) = length l.
Proof.
  intros A l. induction l as [| a l IH]; intros n x; simpl.
  - reflexivity.
  - destruct n as [| n]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma Zlength_replace_Znth__pull_merge :
  forall {A : Type} (l : list A) (n : Z) (x : A),
  Zlength (replace_Znth n x l) = Zlength l.
Proof.
  intros A l n x. unfold replace_Znth. rewrite !Zlength_correct.
  rewrite length_replace_nth__pull_merge. reflexivity.
Qed.
Lemma cells_shaped_replace__pull_merge :
  forall (cells : list (list (option Z))) (v : Z) (row : list (option Z)),
  CellsShaped cells -> 0 <= v < 400020 -> Zlength row = 60 ->
  CellsShaped (replace_Znth v row cells).
Proof.
  intros cells v row [Hlen Hrow] Hv Hrl.
  unfold CellsShaped. split.
  - rewrite Zlength_replace_Znth__pull_merge. assumption.
  - intros i Hi.
    destruct (Z.eq_dec i v) as [Heq | Hne].
    + subst i. rewrite Znth_replace_Znth_Same by lia. assumption.
    + rewrite Znth_replace_Znth_Diff by lia. apply Hrow. assumption.
Qed.
Lemma row_prefix_step__pull_merge :
  forall (cells : list (list (option Z))) (v : Z) (ps : list Z) (k : Z),
  0 <= v < Zlength cells ->
  0 <= k < Zlength (Znth v cells (@nil (option Z))) ->
  RowPrefixIs cells v ps k ->
  RowPrefixIs
    (replace_Znth v
       (replace_Znth k (Some (delta ps k)) (Znth v cells (@nil (option Z))))
       cells)
    v ps (k + 1).
Proof.
  intros cells v ps k Hv Hk Hpre.
  unfold RowPrefixIs. intros r Hr.
  rewrite Znth_replace_Znth_Same by lia.
  destruct (Z.eq_dec r k) as [Heq | Hne].
  - subst r. rewrite Znth_replace_Znth_Same by lia. reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hpre. lia.
Qed.
Lemma cross_cons__pull_frame : forall p ps t,
  cross (p :: ps) t = cross ps (if Z.eqb (t mod p) 0 then t + 2 else t + 1).
Proof. reflexivity. Qed.
Lemma delta_bounds__pull_frame : forall ps r,
  Zlength ps <= delta ps r <= 2 * Zlength ps.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros r; unfold delta in *.
  - rewrite cross_nil. rewrite Zlength_nil. lia.
  - rewrite cross_cons__pull_frame. rewrite Zlength_cons.
    destruct (Z.eqb (r mod p) 0).
    + specialize (IH (r + 2)). lia.
    + specialize (IH (r + 1)). lia.
Qed.
Lemma node_slice_facts__pull_frame : forall arr lo hi,
  1 <= lo -> lo - 1 <= hi -> hi <= Zlength arr ->
  Zlength (NodeSlice arr lo hi) = hi - lo + 1.
Proof.
  intros arr lo hi H1 H2 H3.
  unfold NodeSlice.
  rewrite Zlength_sublist by lia.
  lia.
Qed.
Lemma row_is_value__pull_frame : forall cells v ps r d,
  CellsShaped cells ->
  0 <= v < 400020 ->
  RowIs cells v ps ->
  0 <= r < 60 ->
  Znth r (Znth v cells d) None = Some (delta ps r).
Proof.
  intros cells v ps r d Hshape Hv Hrow Hr.
  destruct Hshape as [Hlen _].
  rewrite (Znth_indep cells v d (@nil (option Z))) by lia.
  apply Hrow. exact Hr.
Qed.
Lemma length_replace_nth__leaf_loop :
  forall {A : Type} (l : list A) (n : nat) (a : A),
  length (replace_nth n l a) = length l.
Proof.
  intros A l. induction l as [| x l IH]; intros n a; simpl.
  - destruct n; reflexivity.
  - destruct n as [| n']; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma Zlength_replace_Znth__leaf_loop :
  forall {A : Type} (l : list A) (i : Z) (a : A),
  Zlength (replace_Znth i a l) = Zlength l.
Proof.
  intros A l i a. unfold replace_Znth.
  rewrite !Zlength_correct, length_replace_nth__leaf_loop. reflexivity.
Qed.
Lemma nth_replace_nth_diff__leaf_loop :
  forall {A : Type} (l : list A) (m n : nat) (a d : A),
  m <> n -> nth n (replace_nth m l a) d = nth n l d.
Proof.
  intros A l. induction l as [| x l IH]; intros m n a d Hmn; simpl.
  - destruct m; destruct n; reflexivity.
  - destruct m as [| m']; destruct n as [| n']; simpl.
    + exfalso; apply Hmn; reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. intro; apply Hmn; f_equal; assumption.
Qed.
Lemma Znth_replace_Znth_neq__leaf_loop :
  forall {A : Type} (d : A) (l : list A) (i j : Z) (a : A),
  Z.to_nat i <> Z.to_nat j ->
  Znth j (replace_Znth i a l) d = Znth j l d.
Proof.
  intros A d l i j a H. unfold Znth, replace_Znth.
  apply nth_replace_nth_diff__leaf_loop. exact H.
Qed.
Lemma Znth_default_irrel__leaf_loop :
  forall {A : Type} (l : list A) (i : Z) (d1 d2 : A),
  0 <= i < Zlength l -> Znth i l d1 = Znth i l d2.
Proof.
  intros A l i d1 d2 H. unfold Znth. apply nth_indep.
  rewrite Zlength_correct in H. lia.
Qed.
Lemma skipn_firstn_single__leaf_loop :
  forall {A : Type} (d : A) (l : list A) (n : nat),
  (n < length l)%nat -> skipn n (firstn (S n) l) = [nth n l d].
Proof.
  intros A d l. induction l as [| x l IH]; intros n Hn; simpl in *.
  - lia.
  - destruct n as [| n']; simpl.
    + reflexivity.
    + apply IH. lia.
Qed.
Lemma sublist_single__leaf_loop :
  forall {A : Type} (d : A) (l : list A) (i : Z),
  0 <= i < Zlength l -> sublist i (i + 1) l = [Znth i l d].
Proof.
  intros A d l i H. unfold sublist, Znth.
  rewrite Zlength_correct in H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply skipn_firstn_single__leaf_loop. lia.
Qed.
Lemma node_slice_single__leaf_loop : forall arr hi,
  1 <= hi <= Zlength arr -> NodeSlice arr hi hi = [Znth (hi - 1) arr 0].
Proof.
  intros arr hi H. unfold NodeSlice.
  assert (Hs : sublist (hi - 1) hi arr = sublist (hi - 1) (hi - 1 + 1) arr).
  { f_equal. lia. }
  rewrite Hs. apply sublist_single__leaf_loop. lia.
Qed.
Lemma periods_znth__leaf_loop : forall arr j,
  PeriodsOK arr -> 0 <= j < Zlength arr -> 2 <= Znth j arr 0 <= 6.
Proof.
  intros arr j HP Hj. unfold PeriodsOK in HP.
  rewrite Forall_forall in HP. apply HP.
  unfold Znth. apply nth_In.
  rewrite Zlength_correct in Hj. lia.
Qed.
Lemma node_fits_bounds__leaf_loop : forall v lo hi,
  NodeFits v lo hi -> 1 <= v /\ v < 400020 /\ 1 <= lo /\ lo <= hi.
Proof.
  intros v lo hi H. unfold NodeFits in H.
  destruct H as [Hv [Hlo [Hle [k [Hk0 [Hk1 Hk2]]]]]].
  assert (H1k : 1 <= 2 ^ k).
  { rewrite <- (Z.pow_0_r 2). apply Z.pow_le_mono_r; lia. }
  repeat split; try nia.
Qed.
Lemma leaf_slice_delta__leaf_loop : forall arr hi r,
  1 <= hi <= Zlength arr ->
  delta (NodeSlice arr hi hi) r
    = (if Z.eqb (r mod (Znth (hi - 1) arr 0)) 0 then 2 else 1).
Proof.
  intros arr hi r H. rewrite node_slice_single__leaf_loop by lia.
  apply delta_single.
Qed.
Lemma leaf_delta_rem_zero__leaf_loop : forall arr hi r,
  1 <= hi <= Zlength arr -> 0 <= r -> 2 <= Znth (hi - 1) arr 0 ->
  Z.rem r (Znth (hi - 1) arr 0) = 0 ->
  delta (NodeSlice arr hi hi) r = 2.
Proof.
  intros arr hi r Hhi Hr Hp Hrem.
  rewrite leaf_slice_delta__leaf_loop by lia.
  rewrite <- Zrem_Zmod_pos by lia.
  rewrite Hrem. reflexivity.
Qed.
Lemma leaf_delta_rem_nonzero__leaf_loop : forall arr hi r,
  1 <= hi <= Zlength arr -> 0 <= r -> 2 <= Znth (hi - 1) arr 0 ->
  Z.rem r (Znth (hi - 1) arr 0) <> 0 ->
  delta (NodeSlice arr hi hi) r = 1.
Proof.
  intros arr hi r Hhi Hr Hp Hrem.
  rewrite leaf_slice_delta__leaf_loop by lia.
  rewrite <- Zrem_Zmod_pos by lia.
  destruct (Z.eqb_spec (Z.rem r (Znth (hi - 1) arr 0)) 0).
  - exfalso. apply Hrem. assumption.
  - reflexivity.
Qed.
Lemma rows_agree_replace__leaf_loop : forall v cells cells' row,
  1 <= v ->
  RowsAgreeExcept v cells cells' ->
  RowsAgreeExcept v cells (replace_Znth v row cells').
Proof.
  intros v cells cells' row Hv H u Hu.
  rewrite Znth_replace_Znth_neq__leaf_loop by lia.
  apply H. exact Hu.
Qed.
Lemma row_prefix_step__leaf_loop :
  forall cells v ps r d val,
  Zlength cells = 400020 ->
  1 <= v < 400020 ->
  Zlength (Znth v cells []) = 60 ->
  0 <= r < 60 ->
  RowPrefixIs cells v ps r ->
  delta ps r = val ->
  RowPrefixIs (replace_Znth v (replace_Znth r (Some val) (Znth v cells d)) cells)
    v ps (r + 1).
Proof.
  intros cells v ps r d val Hlen Hv Hrow Hr Hpre Hval.
  assert (Hdd : Znth v cells d = Znth v cells (@nil (option Z))).
  { apply Znth_default_irrel__leaf_loop. lia. }
  unfold RowPrefixIs in *. intros r' Hr'.
  rewrite Znth_replace_Znth_Same by lia.
  rewrite Hdd.
  destruct (Z.eq_dec r' r) as [He | Hne].
  - subst r'. rewrite Znth_replace_Znth_Same by lia.
    rewrite Hval. reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hpre. lia.
Qed.
Lemma cells_shaped_replace__leaf_loop : forall cells v r val d,
  CellsShaped cells -> 1 <= v < 400020 -> 0 <= r < 60 ->
  CellsShaped (replace_Znth v (replace_Znth r (Some val) (Znth v cells d)) cells).
Proof.
  intros cells v r val d HC Hv Hr.
  destruct HC as [Hlen Hrows].
  assert (Hdd : Znth v cells d = Znth v cells (@nil (option Z))).
  { apply Znth_default_irrel__leaf_loop. lia. }
  split.
  - rewrite Zlength_replace_Znth__leaf_loop. exact Hlen.
  - intros i Hi. destruct (Z.eq_dec i v) as [He | Hne].
    + subst i. rewrite Znth_replace_Znth_Same by lia.
      rewrite Zlength_replace_Znth__leaf_loop. rewrite Hdd.
      apply Hrows. lia.
    + rewrite Znth_replace_Znth_Diff by lia. apply Hrows. lia.
Qed.
Lemma insub_single__leaf_loop : forall v hi u a b,
  InSub v hi hi u a b -> u = v /\ a = hi /\ b = hi.
Proof.
  intros v hi u a b H. inversion H; subst; repeat split; lia.
Qed.
Lemma leaf_tree_ok__leaf_loop : forall cells arr v hi r,
  60 <= r ->
  RowPrefixIs cells v (NodeSlice arr hi hi) r ->
  TreeOK cells arr v hi hi.
Proof.
  intros cells arr v hi r Hr Hpre. unfold TreeOK. intros u a b Hin.
  apply insub_single__leaf_loop in Hin.
  destruct Hin as [Hu [Ha Hb]]. subst u. subst a. subst b.
  unfold RowIs. intros r' Hr'. apply Hpre. lia.
Qed.
Lemma leaf_cells_agree__leaf_loop : forall v hi cells cells',
  RowsAgreeExcept v cells cells' -> CellsAgreeOutside v hi hi cells cells'.
Proof.
  intros v hi cells cells' H. unfold CellsAgreeOutside. intros u Hu.
  apply H. intro Heq. subst u. apply Hu.
  unfold NodeIn. exists hi, hi. apply InSub_self.
Qed.
Lemma insub_range__tree_frame : forall v lo hi u a b,
  InSub v lo hi u a b -> lo <= hi -> lo <= a /\ a <= b /\ b <= hi.
Proof.
  intros v lo hi u a b Hin.
  induction Hin as [v lo hi | v lo hi u a b Hlt Hin IH | v lo hi u a b Hlt Hin IH];
    intros Hle.
  - lia.
  - assert (Hm1 : lo <= (lo + hi) / 2) by (apply Z.div_le_lower_bound; lia).
    assert (Hm2 : (lo + hi) / 2 < hi) by (apply Z.div_lt_upper_bound; lia).
    specialize (IH ltac:(lia)). lia.
  - assert (Hm1 : lo <= (lo + hi) / 2) by (apply Z.div_le_lower_bound; lia).
    assert (Hm2 : (lo + hi) / 2 < hi) by (apply Z.div_lt_upper_bound; lia).
    specialize (IH ltac:(lia)). lia.
Qed.
Lemma insub_window__tree_frame : forall v lo hi u a b,
  InSub v lo hi u a b ->
  exists k, 0 <= k /\ v * 2 ^ k <= u /\ u < (v + 1) * 2 ^ k.
Proof.
  intros v lo hi u a b Hin.
  induction Hin as [v lo hi | v lo hi u a b Hlt Hin IH | v lo hi u a b Hlt Hin IH].
  - exists 0. rewrite Z.pow_0_r. lia.
  - destruct IH as [k [Hk [H1 H2]]].
    assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    exists (k + 1).
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
    split; [lia | nia].
  - destruct IH as [k [Hk [H1 H2]]].
    assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    exists (k + 1).
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
    split; [lia | nia].
Qed.
Lemma subtree_root_le__tree_frame : forall w lo hi u,
  1 <= w -> NodeIn w lo hi u -> w <= u.
Proof.
  intros w lo hi u Hw [a [b Hin]].
  apply insub_window__tree_frame in Hin.
  destruct Hin as [k [Hk [H1 H2]]].
  assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.
Lemma child_subtrees_disjoint__tree_frame : forall v lo1 hi1 lo2 hi2 u,
  1 <= v -> NodeIn (2 * v) lo1 hi1 u -> NodeIn (2 * v + 1) lo2 hi2 u -> False.
Proof.
  intros v lo1 hi1 lo2 hi2 u Hv [a1 [b1 HA]] [a2 [b2 HB]].
  apply insub_window__tree_frame in HA.
  apply insub_window__tree_frame in HB.
  destruct HA as [k [Hk [HkL HkR]]].
  destruct HB as [j [Hj [HjL HjR]]].
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpj : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z_le_gt_dec k j) as [Hkj | Hkj].
  - assert (Hmono : 2 ^ k <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
    assert (E : (2 * v + 1) * 2 ^ k <= (2 * v + 1) * 2 ^ j) by nia.
    lia.
  - assert (Hmono : 2 ^ j <= 2 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia).
    assert (Hpk1 : 0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hpow : 2 ^ k = 2 * 2 ^ (k - 1)).
    { replace k with (k - 1 + 1) at 1 by lia.
      rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. lia. }
    assert (E1 : (2 * v + 1 + 1) * 2 ^ j <= (2 * v + 1 + 1) * 2 ^ (k - 1)) by nia.
    assert (E2 : (2 * v + 1 + 1) * 2 ^ (k - 1) <= 2 * v * 2 ^ k) by nia.
    lia.
Qed.
Lemma mid_quot_div__tree_frame : forall lo hi,
  1 <= lo -> lo < hi ->
  (lo + hi) ÷ 2 = (lo + hi) / 2 /\ lo <= (lo + hi) / 2 /\ (lo + hi) / 2 < hi.
Proof.
  intros lo hi H1 H2.
  split; [apply Z.quot_div_nonneg; lia | split].
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.
Lemma nodefits_child_lt__tree_frame : forall v lo hi,
  NodeFits v lo hi -> lo < hi -> 2 * v + 1 < 400020.
Proof.
  intros v lo hi [Hv [Hlo [Hle [k [Hk [Hlen Hfit]]]]]] Hlt.
  assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.
Lemma rowis_frame__tree_frame : forall cells cells' u ps,
  Znth u cells' (@nil (option Z)) = Znth u cells (@nil (option Z)) ->
  RowIs cells u ps -> RowIs cells' u ps.
Proof.
  intros cells cells' u ps He H. unfold RowIs in *.
  intros r Hr. rewrite He. apply H. exact Hr.
Qed.
Lemma tree_ok_left__tree_frame : forall cells arr v lo hi,
  lo < hi -> TreeOK cells arr v lo hi ->
  TreeOK cells arr (2 * v) lo ((lo + hi) / 2).
Proof.
  intros cells arr v lo hi Hlt H u a b Hin.
  apply H. apply InSub_left; assumption.
Qed.
Lemma tree_ok_right__tree_frame : forall cells arr v lo hi,
  lo < hi -> TreeOK cells arr v lo hi ->
  TreeOK cells arr (2 * v + 1) ((lo + hi) / 2 + 1) hi.
Proof.
  intros cells arr v lo hi Hlt H u a b Hin.
  apply H. apply InSub_right; assumption.
Qed.
Lemma tree_ok_frame__tree_frame :
  forall cells cells' arr w lo hi w' lo' hi',
  TreeOK cells arr w lo hi ->
  CellsAgreeOutside w' lo' hi' cells cells' ->
  (forall u, NodeIn w lo hi u -> ~ NodeIn w' lo' hi' u) ->
  TreeOK cells' arr w lo hi.
Proof.
  intros cells cells' arr w lo hi w' lo' hi' Htree Hout Hdisj u a b Hin.
  apply rowis_frame__tree_frame with (cells := cells).
  - apply Hout. apply Hdisj. exists a, b. exact Hin.
  - apply Htree. exact Hin.
Qed.
Lemma sublist_ext__tree_frame : forall (l1 l2 : list Z) lo hi,
  0 <= lo -> lo <= hi -> hi <= Zlength l1 -> Zlength l1 = Zlength l2 ->
  (forall j, lo <= j < hi -> Znth j l1 0 = Znth j l2 0) ->
  sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros l1 l2 lo hi Hlo Hle Hhi Hlen Hpt.
  apply (proj2 (list_eq_ext (sublist lo hi l1) (sublist lo hi l2) 0)).
  split.
  - rewrite !Zlength_sublist by lia. lia.
  - intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite !Znth_sublist by lia.
    apply Hpt. lia.
Qed.
Lemma slice_stable_outside__tree_frame : forall arr0 arr k a b,
  AgreeExceptIdx k arr0 arr ->
  1 <= a -> a <= b -> b <= Zlength arr0 ->
  (k < a - 1 \/ b <= k) ->
  NodeSlice arr0 a b = NodeSlice arr a b.
Proof.
  intros arr0 arr k a b [Hlen Hpt] Ha Hab Hb Hk.
  unfold NodeSlice.
  apply sublist_ext__tree_frame; try lia.
  intros j Hj. apply Hpt; lia.
Qed.
Lemma tree_ok_stale_frame__tree_frame :
  forall cells cells' arr arr0 k w lo hi w' lo' hi',
  TreeOK cells arr0 w lo hi ->
  CellsAgreeOutside w' lo' hi' cells cells' ->
  (forall u, NodeIn w lo hi u -> ~ NodeIn w' lo' hi' u) ->
  AgreeExceptIdx k arr0 arr ->
  1 <= lo -> lo <= hi -> hi <= Zlength arr0 ->
  (k < lo - 1 \/ hi <= k) ->
  TreeOK cells' arr w lo hi.
Proof.
  intros cells cells' arr arr0 k w lo hi w' lo' hi'
         Htree Hout Hdisj Hagree Hlo Hlohi Hhi Hk u a b Hin.
  pose proof (insub_range__tree_frame _ _ _ _ _ _ Hin Hlohi) as [Ha [Hab Hb]].
  rewrite <- (slice_stable_outside__tree_frame arr0 arr k a b Hagree)
    by (try lia).
  apply rowis_frame__tree_frame with (cells := cells).
  - apply Hout. apply Hdisj. exists a, b. exact Hin.
  - apply Htree. exact Hin.
Qed.
Lemma tree_ok_compose__tree_frame : forall cells2 cells1 arr v lo hi,
  1 <= v -> lo < hi ->
  RowIs cells1 v (NodeSlice arr lo hi) ->
  RowsAgreeExcept v cells2 cells1 ->
  TreeOK cells2 arr (2 * v) lo ((lo + hi) / 2) ->
  TreeOK cells2 arr (2 * v + 1) ((lo + hi) / 2 + 1) hi ->
  TreeOK cells1 arr v lo hi.
Proof.
  intros cells2 cells1 arr v lo hi Hv Hlt Hrow Hagree HL HR u a b Hin.
  inversion Hin; subst.
  - exact Hrow.
  - assert (Hle : 2 * v <= u).
    { apply subtree_root_le__tree_frame with (lo := lo) (hi := (lo + hi) / 2);
        [lia | exists a, b; assumption]. }
    apply rowis_frame__tree_frame with (cells := cells2).
    + apply Hagree. lia.
    + apply HL. assumption.
  - assert (Hle : 2 * v + 1 <= u).
    { apply subtree_root_le__tree_frame
        with (lo := (lo + hi) / 2 + 1) (hi := hi);
        [lia | exists a, b; assumption]. }
    apply rowis_frame__tree_frame with (cells := cells2).
    + apply Hagree. lia.
    + apply HR. assumption.
Qed.
Lemma cells_agree_outside_compose__tree_frame :
  forall cells cellsa cellsb v lo hi,
  1 <= lo -> lo < hi ->
  CellsAgreeOutside (2 * v) lo ((lo + hi) / 2) cells cellsa ->
  CellsAgreeOutside (2 * v + 1) ((lo + hi) / 2 + 1) hi cellsa cellsb ->
  CellsAgreeOutside v lo hi cells cellsb.
Proof.
  intros cells cellsa cellsb v lo hi Hlo Hlt HA HB u Hnot.
  rewrite HB.
  - apply HA. intros [a [b Hin]]. apply Hnot. exists a, b.
    apply InSub_left; assumption.
  - intros [a [b Hin]]. apply Hnot. exists a, b.
    apply InSub_right; assumption.
Qed.
Lemma cells_agree_outside_row__tree_frame :
  forall cells cells2 cells1 v lo hi,
  CellsAgreeOutside v lo hi cells cells2 ->
  RowsAgreeExcept v cells2 cells1 ->
  CellsAgreeOutside v lo hi cells cells1.
Proof.
  intros cells cells2 cells1 v lo hi Hout Hrow u Hnot.
  rewrite Hrow.
  - apply Hout. exact Hnot.
  - intros Heq. apply Hnot. subst u. exists lo, hi. apply InSub_self.
Qed.
Lemma cells_agree_outside_left__tree_frame : forall cells cells' v lo hi,
  lo < hi ->
  CellsAgreeOutside (2 * v) lo ((lo + hi) / 2) cells cells' ->
  CellsAgreeOutside v lo hi cells cells'.
Proof.
  intros cells cells' v lo hi Hlt H u Hnot.
  apply H. intros [a [b Hin]]. apply Hnot. exists a, b.
  apply InSub_left; assumption.
Qed.
Lemma cells_agree_outside_right__tree_frame : forall cells cells' v lo hi,
  lo < hi ->
  CellsAgreeOutside (2 * v + 1) ((lo + hi) / 2 + 1) hi cells cells' ->
  CellsAgreeOutside v lo hi cells cells'.
Proof.
  intros cells cells' v lo hi Hlt H u Hnot.
  apply H. intros [a [b Hin]]. apply Hnot. exists a, b.
  apply InSub_right; assumption.
Qed.
Lemma mid_quot_div__tree_descent : forall lo hi : Z,
  1 <= lo -> lo < hi ->
  (lo + hi) ÷ 2 = (lo + hi) / 2 /\ lo <= (lo + hi) ÷ 2 < hi.
Proof.
  intros lo hi Hlo Hlt.
  assert (Hq : (lo + hi) ÷ 2 = (lo + hi) / 2)
    by (apply Z.quot_div_nonneg; lia).
  split; [exact Hq |].
  rewrite Hq. split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(* Halving the NodeFits exponent: a range holding at least two elements has
   an exponent [k >= 1], and [k - 1] witnesses both children. *)
Lemma node_fits_child__tree_descent : forall v lo hi : Z,
  NodeFits v lo hi -> lo < hi ->
  NodeFits (2 * v) lo ((lo + hi) ÷ 2) /\
  NodeFits (2 * v + 1) ((lo + hi) ÷ 2 + 1) hi.
Proof.
  intros v lo hi HF Hlt.
  destruct HF as [Hv [Hlo [Hle [k [Hk [Hlen Hcap]]]]]].
  destruct (mid_quot_div__tree_descent lo hi Hlo Hlt) as [Hq [Hml Hmr]].
  assert (Hk1 : 1 <= k).
  { destruct (Z.le_gt_cases 1 k) as [Hgt | Hgt]; [exact Hgt |].
    assert (Hk0 : k = 0) by lia. subst k.
    change (2 ^ 0) with 1 in Hlen. lia. }
  assert (Hm : 0 <= k - 1) by lia.
  assert (Hpow : 2 ^ k = 2 * 2 ^ (k - 1)).
  { replace k with (Z.succ (k - 1)) at 1 by lia.
    rewrite Z.pow_succ_r by lia. reflexivity. }
  assert (Hpos : 0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdm : 2 * ((lo + hi) ÷ 2) <= lo + hi <= 2 * ((lo + hi) ÷ 2) + 1).
  { rewrite Hq.
    pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
    pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
    lia. }
  assert (Hcap2 : (2 * v + 2) * 2 ^ (k - 1) <= 400020).
  { replace ((2 * v + 2) * 2 ^ (k - 1)) with ((v + 1) * (2 * 2 ^ (k - 1))) by ring.
    rewrite <- Hpow. exact Hcap. }
  assert (Hcapl : (2 * v + 1) * 2 ^ (k - 1) <= 400020) by nia.
  split.
  - unfold NodeFits.
    split; [lia |]. split; [lia |]. split; [lia |].
    exists (k - 1). split; [lia |]. split; [lia |]. exact Hcapl.
  - unfold NodeFits.
    split; [lia |]. split; [lia |]. split; [lia |].
    exists (k - 1). split; [lia |]. split; [lia |].
    replace ((2 * v + 1 + 1) * 2 ^ (k - 1)) with ((2 * v + 2) * 2 ^ (k - 1)) by ring.
    exact Hcap2.
Qed.

(* A child subtree embeds into its parent through InSub_left / InSub_right,
   so the parent invariant restricts to either child. *)
Lemma insub_child_embed__tree_descent :
  forall (cells : list (list (option Z))) (arr : list Z) (v lo hi : Z),
  1 <= lo -> lo < hi -> TreeOK cells arr v lo hi ->
  TreeOK cells arr (2 * v) lo ((lo + hi) ÷ 2) /\
  TreeOK cells arr (2 * v + 1) ((lo + hi) ÷ 2 + 1) hi.
Proof.
  intros cells arr v lo hi Hlo Hlt HT.
  destruct (mid_quot_div__tree_descent lo hi Hlo Hlt) as [Hq _].
  rewrite Hq. split.
  - intros u a b Hin. apply HT. apply InSub_left; [lia | exact Hin].
  - intros u a b Hin. apply HT. apply InSub_right; [lia | exact Hin].
Qed.

(* Descending with a stale root: the same [arr0] witness serves the child,
   because [AgreeExceptIdx] does not mention the node range at all. *)
Lemma stale_child_descend__tree_descent :
  forall (cells : list (list (option Z))) (arr : list Z) (v lo hi pos : Z),
  1 <= lo -> lo < hi -> TreeStaleAt cells arr v lo hi pos ->
  TreeStaleAt cells arr (2 * v) lo ((lo + hi) ÷ 2) pos /\
  TreeStaleAt cells arr (2 * v + 1) ((lo + hi) ÷ 2 + 1) hi pos.
Proof.
  intros cells arr v lo hi pos Hlo Hlt HS.
  destruct HS as [arr0 [Hag Hok]].
  destruct (insub_child_embed__tree_descent cells arr0 v lo hi Hlo Hlt Hok)
    as [HL HR].
  split; unfold TreeStaleAt; exists arr0; split; assumption.
Qed.
Lemma node_fits_int_bounds__node_safety : forall v lo hi : Z,
  NodeFits v lo hi -> 1 <= v /\ v < 400020 /\ 1 <= lo /\ lo <= hi.
Proof.
  intros v lo hi [Hv [Hlo [Hle [k [Hk [Hlen Hfit]]]]]].
  assert (0 < 2 ^ k) as Hpow by (apply Z.pow_pos_nonneg; lia).
  assert ((v + 1) * 1 <= (v + 1) * 2 ^ k) as Hmono
    by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.
Lemma quot2_bounds__node_safety : forall a : Z,
  0 <= a -> 0 <= a ÷ 2 /\ a ÷ 2 <= a.
Proof.
  intros a Ha.
  rewrite Z.quot_div_nonneg by lia.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; lia.
Qed.
Lemma Forall_firstn__query_node : forall {A : Type} (P : A -> Prop) (n : nat) (l : list A),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [| n IH]; intros l H; simpl.
  - constructor.
  - destruct l as [| x l]; simpl.
    + constructor.
    + constructor.
      * exact (Forall_inv H).
      * apply IH. exact (Forall_inv_tail H).
Qed.
Lemma Forall_skipn__query_node : forall {A : Type} (P : A -> Prop) (n : nat) (l : list A),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n. induction n as [| n IH]; intros l H; simpl.
  - exact H.
  - destruct l as [| x l]; simpl.
    + constructor.
    + apply IH. exact (Forall_inv_tail H).
Qed.
Lemma Znth_default_eq__query_node : forall {A : Type} (i : Z) (l : list A) (d1 d2 : A),
  0 <= i < Zlength l -> Znth i l d1 = Znth i l d2.
Proof.
  intros A i l d1 d2 H. unfold Znth. apply nth_indep.
  rewrite Zlength_correct in H. lia.
Qed.
Lemma cross_bounds__query_node : forall ps t,
  t + Zlength ps <= cross ps t <= t + 2 * Zlength ps.
Proof.
  intros ps. induction ps as [| p ps IH]; intros t.
  - rewrite cross_nil. rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    change (cross (p :: ps) t)
      with (cross ps (if Z.eqb (t mod p) 0 then t + 2 else t + 1)).
    destruct (Z.eqb (t mod p) 0); cbv iota;
      [ pose proof (IH (t + 2)) | pose proof (IH (t + 1)) ]; lia.
Qed.
Lemma delta_bounds__query_node : forall ps r,
  Zlength ps <= delta ps r <= 2 * Zlength ps.
Proof.
  intros ps r. unfold delta.
  pose proof (cross_bounds__query_node ps r). lia.
Qed.
Lemma mod_of_mod60__query_node : forall p t,
  2 <= p <= 6 -> t mod p = (t mod 60) mod p.
Proof.
  intros p t Hp.
  assert (Hd : exists k : Z, 60 = k * p).
  { assert (Hcase : p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6) by lia.
    destruct Hcase as [-> | [-> | [-> | [-> | ->]]]].
    - exists 30. reflexivity.
    - exists 20. reflexivity.
    - exists 15. reflexivity.
    - exists 12. reflexivity.
    - exists 10. reflexivity. }
  destruct Hd as [k Hk].
  pose proof (Z_div_mod_eq_full t 60) as Heq.
  remember (t mod 60) as m eqn:Hm.
  remember (t / 60) as q eqn:Hq.
  rewrite Heq.
  replace (60 * q + m) with (m + (k * q) * p) by (rewrite Hk; ring).
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma cross_mod60__query_node : forall ps t u,
  PeriodsOK ps -> t mod 60 = u mod 60 -> cross ps t - t = cross ps u - u.
Proof.
  unfold PeriodsOK. intros ps.
  induction ps as [| p ps IH]; intros t u HP H.
  - rewrite !cross_nil. lia.
  - pose proof (Forall_inv HP) as Hp.
    pose proof (Forall_inv_tail HP) as HPs.
    assert (Hpm : t mod p = u mod p).
    { rewrite (mod_of_mod60__query_node p t Hp).
      rewrite (mod_of_mod60__query_node p u Hp).
      rewrite H. reflexivity. }
    change (cross (p :: ps) t)
      with (cross ps (if Z.eqb (t mod p) 0 then t + 2 else t + 1)).
    change (cross (p :: ps) u)
      with (cross ps (if Z.eqb (u mod p) 0 then u + 2 else u + 1)).
    rewrite Hpm.
    destruct (Z.eqb (u mod p) 0); cbv iota.
    + assert (H2 : (t + 2) mod 60 = (u + 2) mod 60).
      { rewrite Zplus_mod. rewrite H. rewrite <- Zplus_mod. reflexivity. }
      pose proof (IH (t + 2) (u + 2) HPs H2). lia.
    + assert (H1 : (t + 1) mod 60 = (u + 1) mod 60).
      { rewrite Zplus_mod. rewrite H. rewrite <- Zplus_mod. reflexivity. }
      pose proof (IH (t + 1) (u + 1) HPs H1). lia.
Qed.
Lemma delta_mod60__query_node : forall ps t,
  PeriodsOK ps -> 0 <= t -> cross ps t = t + delta ps (Z.rem t 60).
Proof.
  intros ps t HP Ht.
  rewrite Zrem_Zmod_pos by lia.
  unfold delta.
  assert (Hmm : t mod 60 = (t mod 60) mod 60).
  { rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (cross_mod60__query_node ps t (t mod 60) HP Hmm). lia.
Qed.
Lemma node_slice_facts__query_node : forall arr lo hi,
  1 <= lo -> lo <= hi -> hi <= Zlength arr -> PeriodsOK arr ->
  Zlength (NodeSlice arr lo hi) = hi - lo + 1 /\ PeriodsOK (NodeSlice arr lo hi).
Proof.
  intros arr lo hi H1 H2 H3 HP. split.
  - unfold NodeSlice. rewrite Zlength_sublist by lia. lia.
  - unfold PeriodsOK, NodeSlice, sublist in *.
    apply Forall_skipn__query_node. apply Forall_firstn__query_node. exact HP.
Qed.
Lemma query_slice_full__query_node : forall arr lo hi ql qr,
  ql <= lo -> hi <= qr -> QuerySlice arr lo hi ql qr = NodeSlice arr lo hi.
Proof.
  intros arr lo hi ql qr H1 H2. unfold QuerySlice.
  rewrite Z.max_l by lia. rewrite Z.min_l by lia. reflexivity.
Qed.
Lemma root_row_is__query_node : forall cells arr v lo hi,
  TreeOK cells arr v lo hi -> RowIs cells v (NodeSlice arr lo hi).
Proof.
  intros cells arr v lo hi H. apply H. apply InSub_self.
Qed.
Lemma root_row_cell__query_node :
  forall (cells : list (list (option Z))) (arr : list Z) (v lo hi : Z)
         (d : list (option Z)) (r : Z),
  0 <= v < Zlength cells ->
  TreeOK cells arr v lo hi ->
  0 <= r < 60 ->
  Znth r (Znth v cells d) None = Some (delta (NodeSlice arr lo hi) r).
Proof.
  intros cells arr v lo hi d r Hv HT Hr.
  rewrite (Znth_default_eq__query_node v cells d []) by exact Hv.
  exact (root_row_is__query_node cells arr v lo hi HT r Hr).
Qed.
Lemma mid_quot_div__query_compose : forall lo hi : Z,
  1 <= lo -> lo <= hi -> lo <= (lo + hi) ÷ 2 <= hi.
Proof.
  intros lo hi Hlo Hhi.
  rewrite Z.quot_div_nonneg by lia.
  split.
  - apply Z.le_trans with ((lo * 2) / 2).
    + rewrite Z.div_mul by lia. lia.
    + apply Z.div_le_mono; lia.
  - apply Z.le_trans with ((hi * 2) / 2).
    + apply Z.div_le_mono; lia.
    + rewrite Z.div_mul by lia. lia.
Qed.
Lemma query_slice_split__query_compose :
  forall (arr : list Z) (lo hi ql qr mid : Z),
  1 <= lo -> lo <= mid -> mid <= hi -> hi <= Zlength arr ->
  (ql <= mid -> mid < qr ->
     QuerySlice arr lo hi ql qr
       = QuerySlice arr lo mid ql qr ++ QuerySlice arr (mid + 1) hi ql qr) /\
  (mid < ql -> QuerySlice arr lo hi ql qr = QuerySlice arr (mid + 1) hi ql qr) /\
  (qr <= mid -> QuerySlice arr lo hi ql qr = QuerySlice arr lo mid ql qr).
Proof.
  intros arr lo hi ql qr mid H1 H2 H3 H4.
  unfold QuerySlice, NodeSlice.
  split; [| split].
  - intros Hql Hqr.
    replace (Z.min mid qr) with mid by lia.
    replace (Z.max (mid + 1) ql) with (mid + 1) by lia.
    replace (mid + 1 - 1) with mid by lia.
    apply sublist_split; lia.
  - intros Hql.
    replace (Z.max lo ql) with ql by lia.
    replace (Z.max (mid + 1) ql) with ql by lia.
    reflexivity.
  - intros Hqr.
    replace (Z.min hi qr) with qr by lia.
    replace (Z.min mid qr) with qr by lia.
    reflexivity.
Qed.
Lemma mid_quot_div__query_descent : forall lo hi,
  1 <= lo -> lo < hi ->
  (lo + hi) ÷ 2 = (lo + hi) / 2 /\ lo <= (lo + hi) / 2 < hi.
Proof.
  intros lo hi Hlo Hlt.
  assert (Hq : (lo + hi) ÷ 2 = (lo + hi) / 2).
  { apply Z.quot_div_nonneg; lia. }
  split; [exact Hq |].
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmb.
  lia.
Qed.
Lemma node_fits_child__query_descent : forall v lo hi,
  lo < hi -> NodeFits v lo hi ->
  NodeFits (2 * v) lo ((lo + hi) / 2) /\
  NodeFits (2 * v + 1) ((lo + hi) / 2 + 1) hi.
Proof.
  intros v lo hi Hlt [Hv [Hlo [Hle [k [Hk [Hlen Hfit]]]]]].
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmb.
  assert (Hk1 : 1 <= k).
  { destruct (Z_le_gt_dec 1 k) as [Hle1 | Hgt1]; [exact Hle1 |].
    assert (k = 0) by lia. subst k. simpl in Hlen. lia. }
  assert (Hpow : 2 ^ k = 2 * 2 ^ (k - 1)).
  { replace k with (1 + (k - 1)) at 1 by lia.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. reflexivity. }
  assert (Hm : 1 <= 2 ^ (k - 1)).
  { apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := k - 1); lia. }
  split; unfold NodeFits.
  - split; [lia | split; [lia | split; [lia |]]].
    exists (k - 1). split; [lia | split; [lia | nia]].
  - split; [lia | split; [lia | split; [lia |]]].
    exists (k - 1). split; [lia | split; [lia | nia]].
Qed.
Lemma tree_ok_child__query_descent : forall cells arr v lo hi,
  lo < hi -> TreeOK cells arr v lo hi ->
  TreeOK cells arr (2 * v) lo ((lo + hi) / 2) /\
  TreeOK cells arr (2 * v + 1) ((lo + hi) / 2 + 1) hi.
Proof.
  intros cells arr v lo hi Hlt HT.
  split; intros u a b Hin.
  - apply HT. apply InSub_left; [lia | exact Hin].
  - apply HT. apply InSub_right; [lia | exact Hin].
Qed.
Lemma node_fits_left__query_descent : forall v lo hi,
  lo < hi -> NodeFits v lo hi -> NodeFits (2 * v) lo ((lo + hi) ÷ 2).
Proof.
  intros v lo hi Hlt HN.
  assert (Hlo : 1 <= lo) by (destruct HN as [_ [H _]]; exact H).
  destruct (mid_quot_div__query_descent lo hi Hlo Hlt) as [Hq _].
  rewrite Hq.
  apply (node_fits_child__query_descent v lo hi Hlt HN).
Qed.
Lemma node_fits_right__query_descent : forall v lo hi,
  lo < hi -> NodeFits v lo hi -> NodeFits (2 * v + 1) ((lo + hi) ÷ 2 + 1) hi.
Proof.
  intros v lo hi Hlt HN.
  assert (Hlo : 1 <= lo) by (destruct HN as [_ [H _]]; exact H).
  destruct (mid_quot_div__query_descent lo hi Hlo Hlt) as [Hq _].
  rewrite Hq.
  apply (node_fits_child__query_descent v lo hi Hlt HN).
Qed.
Lemma tree_ok_left__query_descent : forall cells arr v lo hi,
  1 <= lo -> lo < hi -> TreeOK cells arr v lo hi ->
  TreeOK cells arr (2 * v) lo ((lo + hi) ÷ 2).
Proof.
  intros cells arr v lo hi Hlo Hlt HT.
  destruct (mid_quot_div__query_descent lo hi Hlo Hlt) as [Hq _].
  rewrite Hq.
  apply (tree_ok_child__query_descent cells arr v lo hi Hlt HT).
Qed.
Lemma tree_ok_right__query_descent : forall cells arr v lo hi,
  1 <= lo -> lo < hi -> TreeOK cells arr v lo hi ->
  TreeOK cells arr ((2 * v) + 1) ((lo + hi) ÷ 2 + 1) hi.
Proof.
  intros cells arr v lo hi Hlo Hlt HT.
  destruct (mid_quot_div__query_descent lo hi Hlo Hlt) as [Hq _].
  rewrite Hq.
  apply (tree_ok_child__query_descent cells arr v lo hi Hlt HT).
Qed.
Lemma zlength_repeat__solver_init : forall (A : Type) (x : A) (n : nat),
  Zlength (repeat x n) = Z.of_nat n.
Proof.
  intros A x n. rewrite Zlength_correct. f_equal.
  induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma node_slice_nil__solver_init : forall (l : list Z) (lo hi : Z),
  hi <= lo - 1 -> NodeSlice l lo hi = nil.
Proof. intros l lo hi H. unfold NodeSlice. apply Zsublist_nil. lia. Qed.
Lemma node_slice_prefix__solver_init : forall (l : list Z) (i : Z),
  1 <= i -> i <= Zlength l ->
  NodeSlice l 1 (i - 1) ++ (Znth (i - 1) l 0 :: nil) = NodeSlice l 1 i.
Proof.
  intros l i H1 H2. unfold NodeSlice.
  replace (1 - 1) with 0 by lia.
  assert (Hs : sublist (i - 1) i l = (Znth (i - 1) l 0 :: nil)).
  { pose proof (sublist_single 0 (i - 1) l) as Hss.
    replace (i - 1 + 1) with i in Hss by lia.
    apply Hss. lia. }
  rewrite (sublist_split 0 i (i - 1) l) by lia.
  rewrite Hs. reflexivity.
Qed.
Lemma node_slice_all__solver_init : forall (l : list Z),
  NodeSlice l 1 (Zlength l) = l.
Proof.
  intros l. unfold NodeSlice. replace (1 - 1) with 0 by lia.
  apply sublist_self. reflexivity.
Qed.
Lemma node_fits_root__solver_init : forall n : Z,
  1 <= n -> n <= 100000 -> NodeFits 1 1 n.
Proof.
  intros n H1 H2. unfold NodeFits.
  assert (Hp : 2 ^ 17 = 131072) by reflexivity.
  repeat split; try lia.
  exists 17. repeat split; lia.
Qed.
Lemma periods_ok_of_znth__solver_init : forall (l : list Z),
  (forall i : Z, 0 <= i < Zlength l -> 2 <= Znth i l 0 /\ Znth i l 0 <= 6) ->
  PeriodsOK l.
Proof.
  unfold PeriodsOK. intros l. induction l as [| a l IH]; intros H.
  - constructor.
  - pose proof (Zlength_nonneg l) as Hnn.
    constructor.
    + specialize (H 0). rewrite Zlength_cons in H.
      unfold Znth in H. simpl in H. apply H. lia.
    + apply IH. intros i Hi. specialize (H (i + 1)).
      rewrite Zlength_cons in H.
      assert (Hz : Znth (i + 1) (a :: l) 0 = Znth i l 0).
      { unfold Znth. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity. }
      rewrite Hz in H. apply H. lia.
Qed.
Lemma undef_cells__solver_init :
  CellsShaped (repeat (repeat (@None Z) (Z.to_nat 60)) (Z.to_nat 400020)).
Proof.
  unfold CellsShaped. split.
  - rewrite zlength_repeat__solver_init. lia.
  - intros i Hi.
    rewrite (Znth_repeat_lt nil (Z.to_nat 400020) i (repeat (@None Z) (Z.to_nat 60))) by lia.
    rewrite zlength_repeat__solver_init. lia.
Qed.
Lemma node_fits_root__solver_step : forall n : Z,
  1 <= n -> n <= 100000 -> NodeFits 1 1 n.
Proof.
  intros n Hlo Hhi. unfold NodeFits.
  split; [lia |]. split; [lia |]. split; [lia |].
  exists 17.
  assert (H17 : 2 ^ 17 = 131072) by (vm_compute; reflexivity).
  rewrite H17. lia.
Qed.
Lemma forall_replace_Znth__solver_step :
  forall (A : Type) (P : A -> Prop) (l : list A) (k : Z) (v : A),
  Forall P l -> P v -> Forall P (replace_Znth k v l).
Proof.
  intros A P l k v Hl Hv. unfold replace_Znth.
  set (m := Z.to_nat k). clearbody m. revert m.
  induction Hl as [| x xs Hx Hxs IH]; intros m; simpl.
  - destruct m; constructor.
  - destruct m.
    + constructor; assumption.
    + constructor; [assumption | apply IH].
Qed.
Lemma periods_ok_replace__solver_step : forall (l : list Z) (k v : Z),
  PeriodsOK l -> 2 <= v -> v <= 6 -> PeriodsOK (replace_Znth k v l).
Proof.
  intros l k v Hl H2 H6. unfold PeriodsOK in *.
  apply forall_replace_Znth__solver_step; [exact Hl | lia].
Qed.
Lemma zlength_replace_Znth__solver_step :
  forall {A : Type} (l : list A) (n : Z) (v : A),
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. unfold replace_Znth.
  set (m := Z.to_nat n). clearbody m. revert m.
  induction l as [| x l IH]; intros m; simpl.
  - destruct m; reflexivity.
  - destruct m; simpl.
    + reflexivity.
    + rewrite !Zlength_cons. rewrite IH. reflexivity.
Qed.
Lemma znth_replace_diff__solver_step :
  forall (l : list Z) (i j v : Z),
  0 <= i < Zlength l -> 0 <= j -> i <> j ->
  Znth j (replace_Znth i v l) 0 = Znth j l 0.
Proof.
  intros l i j v Hi Hj Hne.
  destruct (Z_lt_dec j (Zlength l)) as [Hlt | Hge].
  - apply (Znth_replace_Znth_Diff 0 l i j v); [lia | lia | lia].
  - assert (Hz : Zlength (replace_Znth i v l) = Zlength l)
      by apply zlength_replace_Znth__solver_step.
    rewrite !Zlength_correct in Hz. rewrite !Zlength_correct in Hge.
    assert (Hlen : (length l <= Z.to_nat j)%nat) by lia.
    assert (Hlen' : (length (replace_Znth i v l) <= Z.to_nat j)%nat) by lia.
    unfold Znth. rewrite (nth_overflow _ _ Hlen').
    rewrite (nth_overflow _ _ Hlen). reflexivity.
Qed.
Lemma stale_after_write__solver_step :
  forall (cells : list (list (option Z))) (arr : list Z) (n x y : Z),
  Zlength arr = n -> 1 <= x -> x <= n ->
  TreeOK cells arr 1 1 n ->
  TreeStaleAt cells (replace_Znth (x - 1) y arr) 1 1 n x.
Proof.
  intros cells arr n x y Hlen Hx1 Hxn Htree.
  unfold TreeStaleAt. exists arr. split; [| exact Htree].
  unfold AgreeExceptIdx. split.
  - rewrite zlength_replace_Znth__solver_step. reflexivity.
  - intros j Hj Hne. symmetry.
    apply (znth_replace_diff__solver_step arr (x - 1) j y); lia.
Qed.
Lemma fold_sum_perm__solver_step :
  forall (A : Type) (f : A -> Z) (l1 l2 : list A),
  Permutation l1 l2 ->
  fold_right (fun x acc => f x + acc) 0 l1 =
  fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  intros A f l1 l2 Hp. induction Hp; simpl; lia.
Qed.
Lemma set_card_ext__solver_step :
  forall (A : Type) (P Q : A -> Prop) (HP : Finite P) (HQ : Finite Q),
  (forall x, P x <-> Q x) -> @set_card A P HP = @set_card A Q HQ.
Proof.
  intros A P Q HP HQ Hiff.
  unfold set_card, sum.
  apply fold_sum_perm__solver_step.
  apply NoDup_Permutation.
  - apply (@enum_nodup A P HP).
  - apply (@enum_nodup A Q HQ).
  - intros x. split; intros Hin.
    + apply (@enum_ok A Q HQ). apply Hiff. apply (@enum_ok A P HP). exact Hin.
    + apply (@enum_ok A P HP). apply Hiff. apply (@enum_ok A Q HQ). exact Hin.
Qed.
Lemma ask_count_step__solver_step : forall (qs : list TrafficQuery) (i : Z),
  (let ' (d, _, _) := Znth i qs (0, 0, 0) in d <> 65) ->
  AskCount qs (i + 1) = AskCount qs i.
Proof.
  intros qs i Hne. unfold AskCount.
  apply set_card_ext__solver_step.
  intros x. split.
  - intros [Hr Hq]. split; [| exact Hq].
    destruct (Z.eq_dec x i) as [Heq | Hneq].
    + exfalso. subst x. revert Hq Hne.
      destruct (Znth i qs (0, 0, 0)) as [[d a] b]. intros Hq Hne. contradiction.
    + lia.
  - intros [Hr Hq]. split; [lia | exact Hq].
Qed.
Lemma znth_app_last__solver_step :
  forall (A : Type) (d : A) (l : list A) (v : A),
  Znth (Zlength l) (l ++ (v :: nil)) d = v.
Proof.
  intros A d l v.
  rewrite (app_Znth2 d l (v :: nil) (Zlength l)) by lia.
  replace (Zlength l - Zlength l) with 0 by lia.
  reflexivity.
Qed.
Lemma query_steps_extend__solver_step :
  forall (qs : list TrafficQuery) (states : list (list Z)) (v : list Z) (i : Z),
  0 <= i -> Zlength states = i + 1 ->
  QueryStepsOK qs states i -> QueryStepsOK qs (states ++ (v :: nil)) i.
Proof.
  intros qs states v i Hi Hlen H j Hj.
  specialize (H j Hj). unfold QueryStep in *.
  destruct (Znth j qs (0, 0, 0)) as [[c x] y].
  rewrite (app_Znth1 (@nil Z) states (v :: nil) j) by lia.
  rewrite (app_Znth1 (@nil Z) states (v :: nil) (j + 1)) by lia.
  exact H.
Qed.
Lemma answers_extend__solver_step :
  forall (qs : list TrafficQuery) (states : list (list Z)) (answers : list Z)
         (v : list Z) (i : Z),
  0 <= i -> Zlength states = i + 1 ->
  AnswersOK qs states answers i -> AnswersOK qs (states ++ (v :: nil)) answers i.
Proof.
  intros qs states answers v i Hi Hlen H j Hj.
  specialize (H j Hj).
  destruct (Znth j qs (0, 0, 0)) as [[c x] y].
  intros Hc. specialize (H Hc).
  rewrite (app_Znth1 (@nil Z) states (v :: nil) j) by lia.
  exact H.
Qed.
Lemma query_steps_step__solver_step :
  forall (qs : list TrafficQuery) (states : list (list Z)) (i x y : Z),
  0 <= i -> Zlength states = i + 1 ->
  Znth i qs (0, 0, 0) = (67, x, y) ->
  QueryStepsOK qs states i ->
  QueryStepsOK qs
    (states ++ (replace_Znth (x - 1) y (Znth i states nil) :: nil)) (i + 1).
Proof.
  intros qs states i x y Hi Hlen Hq H j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hne].
  - subst j. unfold QueryStep. rewrite Hq. left. split; [reflexivity |].
    rewrite (app_Znth1 (@nil Z) states _ i) by lia.
    replace (i + 1) with (Zlength states) by lia.
    rewrite (znth_app_last__solver_step (list Z) (@nil Z) states _).
    reflexivity.
  - apply (query_steps_extend__solver_step qs states _ i Hi Hlen H j). lia.
Qed.
Lemma answers_step__solver_step :
  forall (qs : list TrafficQuery) (states : list (list Z)) (answers : list Z)
         (v : list Z) (i x y : Z),
  0 <= i -> Zlength states = i + 1 ->
  Znth i qs (0, 0, 0) = (67, x, y) ->
  AnswersOK qs states answers i ->
  AnswersOK qs (states ++ (v :: nil)) answers (i + 1).
Proof.
  intros qs states answers v i x y Hi Hlen Hq H j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hne].
  - subst j. rewrite Hq. intros Hc. discriminate Hc.
  - apply (answers_extend__solver_step qs states answers v i Hi Hlen H j). lia.
Qed.
Lemma fold_Zsum_one_Zlength__solver_final : forall (l : list Z),
  fold_right (fun (_ : Z) acc => 1 + acc) 0 l = Zlength l.
Proof.
  induction l as [| x l IH]; [reflexivity |].
  change (fold_right (fun (_ : Z) acc => 1 + acc) 0 (x :: l))
    with (1 + fold_right (fun (_ : Z) acc => 1 + acc) 0 l).
  rewrite IH. rewrite Zlength_cons. lia.
Qed.
Lemma ask_count_filter__solver_final : forall (qs : list TrafficQuery) (i : Z),
  AskCount qs i =
  Zlength (filter (fun j : Z =>
             if prop_dec (let '(d, _, _) := Znth j qs (0, 0, 0) in d = 65)
             then true else false)
           (Zrange 0 i)).
Proof.
  intros qs i. unfold AskCount, set_card, sum.
  apply fold_Zsum_one_Zlength__solver_final.
Qed.
Lemma ask_count_zero__solver_step : forall (qs : list TrafficQuery),
  AskCount qs 0 = 0.
Proof.
  intros qs. rewrite (ask_count_filter__solver_final qs 0).
  unfold Zrange. simpl. reflexivity.
Qed.
Lemma zrange_split__solver_final : forall lo mid hi,
  lo <= mid -> mid <= hi ->
  Zrange lo hi = Zrange lo mid ++ Zrange mid hi.
Proof.
  intros lo mid hi H1 H2. unfold Zrange.
  replace (Z.to_nat (hi - lo))
    with (Z.to_nat (mid - lo) + Z.to_nat (hi - mid))%nat by lia.
  rewrite Zrange_aux_app.
  replace (lo + Z.of_nat (Z.to_nat (mid - lo))) with mid by lia.
  reflexivity.
Qed.
Lemma ask_count_mono__solver_final : forall (qs : list TrafficQuery) (j i : Z),
  0 <= j -> j <= i -> AskCount qs j <= AskCount qs i.
Proof.
  intros qs j i Hj Hji.
  rewrite (ask_count_filter__solver_final qs j).
  rewrite (ask_count_filter__solver_final qs i).
  rewrite (zrange_split__solver_final 0 j i) by lia.
  rewrite filter_app. rewrite Zlength_app.
  pose proof (Zlength_nonneg (filter (fun j0 : Z =>
             if prop_dec (let '(d, _, _) := Znth j0 qs (0, 0, 0) in d = 65)
             then true else false) (Zrange j i))).
  lia.
Qed.
Lemma ask_count_ask__solver_final : forall (qs : list TrafficQuery) (i x y : Z),
  0 <= i -> Znth i qs (0, 0, 0) = (65, x, y) ->
  AskCount qs (i + 1) = AskCount qs i + 1.
Proof.
  intros qs i x y Hi Hq.
  rewrite (ask_count_filter__solver_final qs (i + 1)).
  rewrite (ask_count_filter__solver_final qs i).
  rewrite (zrange_split__solver_final 0 i (i + 1)) by lia.
  rewrite filter_app. rewrite Zlength_app.
  assert (Zrange i (i + 1) = i :: nil) as Hr.
  { unfold Zrange. replace (i + 1 - i) with 1 by lia. reflexivity. }
  rewrite Hr. cbn [filter]. rewrite Hq. cbn iota beta.
  destruct (prop_dec (65 = 65)) as [_ | Hno]; [| exfalso; apply Hno; reflexivity].
  rewrite Zlength_cons. rewrite Zlength_nil. lia.
Qed.
Lemma cross_scan__solver_final : forall (ps : list Z) (t : Z),
  exists times : list Z,
    Zlength times = Zlength ps + 1 /\
    Znth 0 times 0 = t /\
    Znth (Zlength ps) times 0 = cross ps t /\
    (forall k, 0 <= k < Zlength ps ->
       Znth (k + 1) times 0 =
       (if Z.eqb (Znth k times 0 mod Znth k ps 0) 0
        then Znth k times 0 + 2 else Znth k times 0 + 1)).
Proof.
  intros ps. induction ps as [| p ps IH] using rev_ind; intros t.
  - exists (t :: nil).
    assert (Hz : Zlength (t :: nil) = 1) by (rewrite Zlength_cons, Zlength_nil; lia).
    split; [rewrite Hz, Zlength_nil; lia |].
    split; [reflexivity |].
    split; [rewrite Zlength_nil; reflexivity |].
    intros k Hk. rewrite Zlength_nil in Hk. lia.
  - destruct (IH t) as [times [HL [H0 [HN Hstep]]]].
    pose proof (Zlength_nonneg ps) as Hps.
    remember (if Z.eqb (Znth (Zlength ps) times 0 mod p) 0
              then Znth (Zlength ps) times 0 + 2
              else Znth (Zlength ps) times 0 + 1) as v eqn:Hv.
    assert (HPL : Zlength (ps ++ p :: nil) = Zlength ps + 1)
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    assert (HTL : Zlength (times ++ v :: nil) = Zlength times + 1)
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    assert (Hnth : forall k, 0 <= k < Zlength times ->
              Znth k (times ++ v :: nil) 0 = Znth k times 0)
      by (intros k Hk; apply app_Znth1; lia).
    assert (Hlast : Znth (Zlength times) (times ++ v :: nil) 0 = v).
    { rewrite app_Znth2 by lia.
      replace (Zlength times - Zlength times) with 0 by lia. reflexivity. }
    assert (Hpsn : forall k, 0 <= k < Zlength ps ->
              Znth k (ps ++ p :: nil) 0 = Znth k ps 0)
      by (intros k Hk; apply app_Znth1; lia).
    assert (Hpsl : Znth (Zlength ps) (ps ++ p :: nil) 0 = p).
    { rewrite app_Znth2 by lia.
      replace (Zlength ps - Zlength ps) with 0 by lia. reflexivity. }
    exists (times ++ v :: nil).
    rewrite HPL. rewrite HTL.
    split; [lia |].
    split; [rewrite Hnth by lia; exact H0 |].
    split.
    + replace (Zlength ps + 1) with (Zlength times) by lia.
      rewrite Hlast. rewrite cross_app. simpl. rewrite <- HN. exact Hv.
    + intros k Hk.
      destruct (Z.eq_dec k (Zlength ps)) as [Hke | Hkne].
      * subst k.
        replace (Zlength ps + 1) with (Zlength times) by lia.
        rewrite Hlast. rewrite Hnth by lia. rewrite Hpsl. exact Hv.
      * rewrite Hnth by lia. rewrite Hnth by lia. rewrite Hpsn by lia.
        apply Hstep. lia.
Qed.
Lemma ride_time_cross__solver_final : forall (arr : list Z) (x y : Z),
  PeriodsOK arr ->
  1 <= x -> x < y -> y <= Zlength arr + 1 ->
  RideTime arr x y (cross (sublist (x - 1) (y - 1) arr) 0).
Proof.
  intros arr x y Hp Hx Hxy Hy. unfold PeriodsOK in Hp.
  assert (Hlen : Zlength (sublist (x - 1) (y - 1) arr) = y - x).
  { rewrite Zlength_sublist by lia. lia. }
  destruct (cross_scan__solver_final (sublist (x - 1) (y - 1) arr) 0)
    as [times [HL [H0 [HN Hstep]]]].
  rewrite Hlen in HL, HN, Hstep.
  unfold RideTime. split; [lia |]. split; [lia |].
  exists times. split.
  - unfold RideTimes. split; [exact HL |]. split; [exact H0 |].
    intros i Hi.
    assert (Hidx : 0 <= x + i - 1 < Zlength arr) by lia.
    assert (Hpi : Znth i (sublist (x - 1) (y - 1) arr) 0 = Znth (x + i - 1) arr 0).
    { rewrite Znth_sublist by lia. f_equal. lia. }
    assert (Hd2 : Znth (x + i - 1) arr 2 = Znth (x + i - 1) arr 0)
      by (apply Znth_indep; lia).
    assert (Hrange : 2 <= Znth (x + i - 1) arr 0 <= 6)
      by (apply (Forall_Znth_Zlength _ _ _ _ Hp Hidx)).
    specialize (Hstep i ltac:(lia)).
    rewrite Hpi in Hstep.
    unfold CrossSegment. rewrite Hd2.
    destruct (Z.eqb_spec (Znth i times 0 mod Znth (x + i - 1) arr 0) 0) as [He | He].
    + left. split; [| exact Hstep].
      apply Z.mod_divide; [lia | exact He].
    + right. split; [| exact Hstep].
      intros Hdiv. apply He. apply Z.mod_divide; [lia | exact Hdiv].
  - symmetry. exact HN.
Qed.
Lemma ask_count_nonneg__solver_final : forall (qs : list TrafficQuery) (i : Z),
  0 <= AskCount qs i.
Proof.
  intros qs i. rewrite ask_count_filter__solver_final. apply Zlength_nonneg.
Qed.
Lemma query_steps_extend__solver_final :
  forall (qs : list TrafficQuery) (states : list (list Z)) (i x y : Z),
  0 <= i ->
  Zlength states = i + 1 ->
  QueryStepsOK qs states i ->
  Znth i qs (0, 0, 0) = (65, x, y) ->
  QueryStepsOK qs (states ++ (Znth i states nil) :: nil) (i + 1).
Proof.
  intros qs states i x y Hi HL Hok Hq.
  assert (Hn : forall k, 0 <= k < i + 1 ->
            Znth k (states ++ (Znth i states nil) :: nil) nil = Znth k states nil)
    by (intros k Hk; apply app_Znth1; lia).
  assert (Hlast : Znth (i + 1) (states ++ (Znth i states nil) :: nil) nil
                  = Znth i states nil).
  { rewrite app_Znth2 by lia.
    replace (i + 1 - Zlength states) with 0 by lia. reflexivity. }
  unfold QueryStepsOK in *. intros j Hj.
  destruct (Z.eq_dec j i) as [He | Hne].
  - subst j. unfold QueryStep. rewrite Hq. cbn iota beta.
    right. split; [reflexivity |]. rewrite Hlast. rewrite Hn by lia. reflexivity.
  - specialize (Hok j ltac:(lia)). unfold QueryStep in *.
    rewrite Hn by lia. rewrite Hn by lia. exact Hok.
Qed.
Lemma answers_extend__solver_final :
  forall (qs : list TrafficQuery) (states : list (list Z)) (answers : list Z)
         (i x y t : Z),
  0 <= i ->
  Zlength states = i + 1 ->
  Zlength answers = AskCount qs i ->
  AnswersOK qs states answers i ->
  Znth i qs (0, 0, 0) = (65, x, y) ->
  RideTime (Znth i states nil) x y t ->
  AnswersOK qs (states ++ (Znth i states nil) :: nil) (answers ++ t :: nil) (i + 1).
Proof.
  intros qs states answers i x y t Hi HSL HAL Hok Hq Hride.
  assert (Hn : forall k, 0 <= k < i + 1 ->
            Znth k (states ++ (Znth i states nil) :: nil) nil = Znth k states nil)
    by (intros k Hk; apply app_Znth1; lia).
  unfold AnswersOK in *. intros j Hj.
  destruct (Z.eq_dec j i) as [He | Hne].
  - subst j. rewrite Hq. cbn iota beta. intros _.
    exists t. split.
    + rewrite Hn by lia. exact Hride.
    + rewrite app_Znth2 by lia. rewrite HAL.
      replace (AskCount qs i - AskCount qs i) with 0 by lia. reflexivity.
  - specialize (Hok j ltac:(lia)).
    remember (Znth j qs (0, 0, 0)) as qj eqn:Hj0.
    destruct qj as [[c xx] yy].
    cbn iota beta in Hok |- *.
    intros Hc. specialize (Hok Hc). destruct Hok as [t0 [Hr Ha]].
    assert (Hqj : Znth j qs (0, 0, 0) = (65, xx, yy))
      by (rewrite <- Hj0; rewrite Hc; reflexivity).
    pose proof (ask_count_ask__solver_final qs j xx yy ltac:(lia) Hqj) as Hstepj.
    pose proof (ask_count_mono__solver_final qs (j + 1) i ltac:(lia) ltac:(lia)) as Hmono.
    pose proof (ask_count_nonneg__solver_final qs j) as Hnn.
    exists t0. split.
    + rewrite Hn by lia. exact Hr.
    + rewrite app_Znth1 by lia. exact Ha.
Qed.
Lemma traffic_trace_of_invariant__solver_final :
  forall (qs : list TrafficQuery) (states : list (list Z)) (answers init : list Z)
         (q : Z),
  Zlength qs = q ->
  Zlength states = q + 1 ->
  Znth 0 states nil = init ->
  Zlength answers = AskCount qs q ->
  QueryStepsOK qs states q ->
  AnswersOK qs states answers q ->
  TrafficTrace init qs states answers.
Proof.
  intros qs states answers init q HQ HS H0 HA HStep HAns. subst q.
  unfold TrafficTrace.
  split; [exact HS |]. split; [exact H0 |]. split; [exact HA |].
  split; [exact HStep | exact HAns].
Qed.
