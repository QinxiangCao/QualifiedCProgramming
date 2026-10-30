Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Field.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.

From Coq Require Reals SpecFloat.
From Flocq.Core Require Core.
From Flocq.IEEE754 Require Import Binary.
From CDCLLib Require Export cdcl_shared_lib.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_tactics.
From SimpleC.EE.Applications_human.minisat Require Export vec_qcp_lib.

Notation "'UINT64_MAX'" := (18446744073709551615).

(** Activity values admit both signed zeros, positive finite values, and
    +infinity. NaNs and negative nonzero values are excluded. *)
Definition msat_fp32_nonnegative (x : fp32) : Prop :=
  match x with
  | Binary.B754_zero _ _ _ => True
  | Binary.B754_infinity _ _ false => True
  | Binary.B754_finite _ _ false _ _ _ => True
  | _ => False
  end.

Definition msat_fp64_nonnegative (x : fp64) : Prop :=
  match x with
  | Binary.B754_zero _ _ _ => True
  | Binary.B754_infinity _ _ false => True
  | Binary.B754_finite _ _ false _ _ _ => True
  | _ => False
  end.

Definition msat_fp32_positive_finite (x : fp32) : Prop :=
  Binary.is_finite 24 128 x = true /\
  Binary.Bsign 24 128 x = false /\
  x <> Binary.B754_zero 24 128 false.

Definition msat_fp64_count_limit (count : Z) (x : fp64) : Prop :=
  0 < count -> msat_fp64_nonnegative x.

(** A fixed default makes floating-array reads stable under symbolic
    matching. *)
Definition msat_fp64_zero : fp64 := Binary.B754_zero 53 1024 false.

(** * S2 -- packed encodings.
    Literals use [2*var + sign], lbool cells use [-1,0,1], and watcher words
    are even clause pointers or odd literal tags [2*lit+1]. *)

(** ----- literal encoding ----- *)

Definition lit_denote (l : Z) : literal :=
  if Z.odd l then Neg (l / 2) else Pos (l / 2).

Definition lits_denote : list Z -> clause := map lit_denote.

Definition lit_wf_c (n l : Z) : Prop := 0 <= l < 2 * n.

Definition lit_neg_c (l : Z) : Z := Z.lxor l 1.

Definition lit_var_c (l : Z) : Z := l / 2.

Definition lbool_val (b : Z) : option bool :=
  if b =? 1 then Some true else if b =? -1 then Some false else None.

(** the [assigns] cell value that makes packed literal [l] true *)
Definition lit_sig (l : Z) : Z := if Z.odd l then -1 else 1.

Definition tag_of_lit (l : Z) : Z := 2 * l + 1.

Definition is_tag (w : Z) : bool := Z.odd w.

Definition tag_lit (w : Z) : Z := w / 2.

(** ----- lbool cells and the partial valuation they induce ----- *)

Definition assigns_val (assigns : list Z) (x : Z) : option bool :=
  lbool_val (Znth x assigns 0).

Definition assigns_pv (assigns : list Z) : partial_valuation :=
  fun x => assigns_val assigns x.

Lemma lbool_val_none : forall v, lbool_val v = None <-> (v <> 1 /\ v <> -1).
Proof.
  intros v. unfold lbool_val. split; intros H.
  - destruct (v =? 1) eqn:H1; [discriminate|].
    destruct (v =? -1) eqn:H2; [discriminate|].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2. split; assumption.
  - destruct H as [H1 H2].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2.
    rewrite H1, H2. reflexivity.
Qed.

Lemma lit_sig_values : forall l, lit_sig l = 1 \/ lit_sig l = -1.
Proof. intros l. unfold lit_sig. destruct (Z.odd l); [right|left]; reflexivity. Qed.

Lemma lits_denote_perm : forall ls ls',
  Permutation ls ls' -> Permutation (lits_denote ls) (lits_denote ls').
Proof. intros. unfold lits_denote. apply Permutation_map. assumption. Qed.

(** * S4 -- concrete trail and CDCL view.
    [mtrail] mirrors assigns, levels, trail, trail_lim, and qhead.
    [mtrail_wf] constrains their shape; [view_of] uses trail positions as
    assignment ranks. [mt_enqueue], [mt_decide], and [mt_cancel] model the
    state changes, while [trail_implied] tracks their logical consequences. *)

(** ===== A. list arithmetic used by the trail ===== *)

Definition ztake (k : Z) (l : list Z) : list Z := firstn (Z.to_nat k) l.

Definition zdrop (k : Z) (l : list Z) : list Z := skipn (Z.to_nat k) l.

Lemma ztake_zdrop : forall k l, ztake k l ++ zdrop k l = l.
Proof. intros k l. apply firstn_skipn. Qed.

Lemma Zlength_ztake : forall k l, 0 <= k <= Zlength l -> Zlength (ztake k l) = k.
Proof.
  intros k l [H1 H2]. unfold ztake.
  rewrite Zlength_correct in H2.
  rewrite Zlength_correct, length_firstn. lia.
Qed.

Lemma In_ztake : forall x k l, In x (ztake k l) -> In x l.
Proof.
  intros x k l H. rewrite <- (ztake_zdrop k l). apply in_or_app. left. exact H.
Qed.

Lemma In_zdrop : forall x k l, In x (zdrop k l) -> In x l.
Proof.
  intros x k l H. rewrite <- (ztake_zdrop k l). apply in_or_app. right. exact H.
Qed.

Lemma nth_firstn_lt : forall (l : list Z) (m j : nat) (d : Z),
  (j < m)%nat -> nth j (firstn m l) d = nth j l d.
Proof.
  induction l as [|a l IH]; intros m j d Hj.
  - rewrite firstn_nil. reflexivity.
  - destruct m as [|m]; [lia|].
    simpl. destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma Znth_ztake : forall k l i d, 0 <= i < k -> Znth i (ztake k l) d = Znth i l d.
Proof.
  intros k l i d Hi. unfold Znth, ztake. apply nth_firstn_lt. lia.
Qed.

Lemma map_ztake_zdrop : forall (f : Z -> Z) k l,
  map f l = map f (ztake k l) ++ map f (zdrop k l).
Proof. intros. rewrite <- map_app, ztake_zdrop. reflexivity. Qed.

Lemma NoDup_app_disjoint : forall (A B : list Z) x,
  NoDup (A ++ B) -> In x A -> ~ In x B.
Proof.
  induction A as [|a A IH]; intros B x Hnd Hin; simpl in *.
  - contradiction.
  - inversion Hnd as [|? ? Hna Hnd']; subst.
    destruct Hin as [<-|Hin].
    + intro HinB. apply Hna. apply in_or_app. right. exact HinB.
    + eapply IH; eauto.
Qed.

(** ----- counting the [trail_lim] entries at or below a trail index ----- *)

Fixpoint count_le (i : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: rest => (if x <=? i then 1 else 0) + count_le i rest
  end.

Lemma count_le_nonneg : forall i l, 0 <= count_le i l.
Proof.
  intros i l; induction l as [|x l IH]; simpl; [lia|].
  destruct (x <=? i); lia.
Qed.

(** ----- strictly increasing lists (this is the shape of [trail_lim]) ----- *)

Fixpoint strict_sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: rest => Forall (fun y => x < y) rest /\ strict_sorted rest
  end.

Lemma strict_sorted_count_suffix : forall l i k,
  strict_sorted l -> count_le i l <= k -> 0 <= k < Zlength l -> i < Znth k l 0.
Proof.
  induction l as [|a l IH]; intros i k Hs Hcnt [Hk0 Hk].
  - rewrite Zlength_nil in Hk; lia.
  - rewrite Zlength_cons in Hk. pose proof (Zlength_nonneg l).
    destruct Hs as [Hall Hs]. simpl in Hcnt.
    destruct (a <=? i) eqn:Ha.
    + assert (Hk0' : k <> 0).
      { intro; subst k. pose proof (count_le_nonneg i l). lia. }
      rewrite Znth_cons by lia. apply IH; [exact Hs|lia|lia].
    + apply Z.leb_gt in Ha.
      destruct (Z.eq_dec k 0) as [->|Hk0'].
      * rewrite Znth0_cons; exact Ha.
      * rewrite Znth_cons by lia.
        assert (Hin : In (Znth (k - 1) l 0) l) by (apply Znth_In; lia).
        rewrite Forall_forall in Hall.
        pose proof (Hall _ Hin). lia.
Qed.

Fixpoint find_var_pos (v : Z) (l : list Z) : option nat :=
  match l with
  | [] => None
  | x :: rest =>
      if lit_var_c x =? v then Some O else option_map S (find_var_pos v rest)
  end.

Lemma find_var_pos_none_iff : forall v l,
  find_var_pos v l = None <-> ~ In v (map lit_var_c l).
Proof.
  induction l as [|x l IH]; simpl.
  - split; [intros _ []|reflexivity].
  - destruct (lit_var_c x =? v) eqn:Hx.
    + apply Z.eqb_eq in Hx. split.
      * discriminate.
      * intro H; exfalso; apply H; left; exact Hx.
    + apply Z.eqb_neq in Hx. split.
      * intros H [Heq|Hin].
        -- apply Hx; exact Heq.
        -- apply (proj1 IH); [|exact Hin].
           destruct (find_var_pos v l); [discriminate H|reflexivity].
      * intro H.
        assert (Hnone : find_var_pos v l = None).
        { apply IH. intro Hin. apply H. right. exact Hin. }
        rewrite Hnone. reflexivity.
Qed.

Lemma find_var_pos_bound : forall v l k,
  find_var_pos v l = Some k -> (k < List.length l)%nat.
Proof.
  induction l as [|x l IH]; intros k H; simpl in *; [discriminate|].
  destruct (lit_var_c x =? v).
  - inversion H; lia.
  - destruct (find_var_pos v l) as [j|] eqn:Hf; simpl in H; [|discriminate].
    inversion H; subst k. pose proof (IH j eq_refl). lia.
Qed.

Lemma find_var_pos_hit : forall v l k,
  find_var_pos v l = Some k -> lit_var_c (nth k l 0) = v.
Proof.
  induction l as [|x l IH]; intros k H; simpl in *; [discriminate|].
  destruct (lit_var_c x =? v) eqn:Hx.
  - inversion H; subst k. simpl. apply Z.eqb_eq in Hx. exact Hx.
  - destruct (find_var_pos v l) as [j|] eqn:Hf; simpl in H; [|discriminate].
    inversion H; subst k. simpl. apply (IH j eq_refl).
Qed.

(** ===== B. the concrete trail and its shape ===== *)

Record mtrail := {
  mt_assigns : list Z;   (* [s->assigns] : one lbool cell per variable      *)
  mt_levels  : list Z;   (* [s->levels]  : written by enqueue, never wiped  *)
  mt_trail   : list Z;   (* [s->trail][0, qtail) : packed literals          *)
  mt_lim     : list Z;   (* [s->trail_lim] : length = solver_dlevel         *)
  mt_qhead   : Z         (* [s->qhead] : propagation frontier               *)
}.

Definition lbool_cell (v : Z) : Prop := v = -1 \/ v = 0 \/ v = 1.

Definition trail_var (t : mtrail) (i : Z) : Z := lit_var_c (Znth i (mt_trail t) 0).

(** The decision level of trail position [i]: the number of [trail_lim]
    boundaries at or below [i].  [assume] pushes [qtail] before enqueueing the
    decision, so [trail_lim[k]] is the trail index of
    the level-[k+1] decision and this count is exactly [levels[trail[i]]]. *)
Definition level_of_index (t : mtrail) (i : Z) : Z := count_le i (mt_lim t).

Lemma lit_sig_nonzero : forall l, lit_sig l <> 0.
Proof. intro l. destruct (lit_sig_values l) as [H|H]; rewrite H; discriminate. Qed.

Lemma lit_var_c_in_range : forall n l, lit_wf_c n l -> 0 <= lit_var_c l < n.
Proof.
  intros n l [H1 H2]. unfold lit_var_c. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Record mtrail_wf (n : Z) (t : mtrail) : Prop := {
  mtw_n_nonneg    : 0 <= n;
  mtw_assigns_len : Zlength (mt_assigns t) = n;
  mtw_levels_len  : Zlength (mt_levels t) = n;
  mtw_cells       : Forall lbool_cell (mt_assigns t);
  mtw_qhead_range : 0 <= mt_qhead t <= Zlength (mt_trail t);
  mtw_trail_bound : Zlength (mt_trail t) <= n;
  mtw_trail_lits  : Forall (lit_wf_c n) (mt_trail t);
  mtw_trail_nodup : NoDup (map lit_var_c (mt_trail t));
  mtw_trail_true  :
    Forall (fun l => Znth (lit_var_c l) (mt_assigns t) 0 = lit_sig l) (mt_trail t);
  mtw_lim_sorted  : strict_sorted (mt_lim t);
  mtw_lim_range   : Forall (fun b => 0 <= b < Zlength (mt_trail t)) (mt_lim t);
  mtw_levels_agree :
    forall i, 0 <= i < Zlength (mt_trail t) ->
      Znth (trail_var t i) (mt_levels t) 0 = level_of_index t i;
  mtw_assigned_iff :
    forall v, 0 <= v < n ->
      (Znth v (mt_assigns t) 0 <> 0 <-> In v (map lit_var_c (mt_trail t)))
}.

Arguments mtw_n_nonneg {n t} _.

Arguments mtw_assigns_len {n t} _.

Arguments mtw_levels_len {n t} _.

Arguments mtw_cells {n t} _.

Arguments mtw_qhead_range {n t} _.

Arguments mtw_trail_bound {n t} _.

Arguments mtw_trail_lits {n t} _.

Arguments mtw_trail_nodup {n t} _.

Arguments mtw_trail_true {n t} _.

Arguments mtw_lim_sorted {n t} _.

Arguments mtw_lim_range {n t} _.

Arguments mtw_levels_agree {n t} _.

Arguments mtw_assigned_iff {n t} _.

(** Every decision boundary sits at or below the propagation frontier. *)
Definition prop_level (t : mtrail) : Prop :=
  Forall (fun b => b <= mt_qhead t) (mt_lim t).

Lemma trail_var_range : forall n t v,
  mtrail_wf n t -> In v (map lit_var_c (mt_trail t)) -> 0 <= v < n.
Proof.
  intros n t v Hwf Hin. apply in_map_iff in Hin. destruct Hin as [x [<- Hx]].
  apply (lit_var_c_in_range n).
  pose proof (mtw_trail_lits Hwf) as HF. rewrite Forall_forall in HF. auto.
Qed.

(* An unassigned variable is absent from the distinct bounded trail. *)
Lemma mtrail_unassigned_room : forall n t v,
  mtrail_wf n t -> 0 <= v < n -> Znth v (mt_assigns t) 0 = 0 ->
  Zlength (mt_trail t) < n.
Proof.
  intros n t v Hwf Hv Hzero.
  assert (Hfresh : ~ In v (map lit_var_c (mt_trail t))).
  { intro Hin. apply (proj2 (mtw_assigned_iff Hwf v Hv) Hin). exact Hzero. }
  assert (Hdistinct : NoDup (v :: map lit_var_c (mt_trail t))).
  { constructor; [exact Hfresh | exact (mtw_trail_nodup Hwf)]. }
  assert (Hrange : forall x, In x (v :: map lit_var_c (mt_trail t)) -> 0 <= x < n).
  { intros x [<- | Hin]; [exact Hv | eapply trail_var_range; eauto]. }
  pose proof (NoDup_Z_bounded_length _ n (mtw_n_nonneg Hwf) Hdistinct Hrange) as Hbound.
  simpl List.length in Hbound. rewrite List.length_map in Hbound.
  rewrite Zlength_correct. lia.
Qed.

Lemma lim_lt_trail : forall n t k,
  mtrail_wf n t -> 0 <= k < Zlength (mt_lim t) ->
  0 <= Znth k (mt_lim t) 0 < Zlength (mt_trail t).
Proof.
  intros n t k Hwf Hk.
  exact (Forall_Znth_elim _ _ _ 0 k (mtw_lim_range Hwf) Hk).
Qed.

(** ===== C. the projection to [cdcl_view] ===== *)

(** [assigns_pv] reads [Znth v], which for a negative [v] silently returns cell
    zero; the view therefore guards the negative half-line.  Every other index
    outside [0, n) falls out of the array and reads the default 0 = unassigned. *)
Definition mt_pv (t : mtrail) : partial_valuation :=
  fun v => if 0 <=? v then assigns_pv (mt_assigns t) v else None.

Definition trail_pos (t : mtrail) (v : Z) : option nat :=
  find_var_pos v (mt_trail t).

(** The ghost rank is the trail position; the level is the boundary count at
    that position; a reason is visible only for an assigned variable
    ([canceluntil] clears [reasons] for everything it unassigns). *)
Definition view_of (n : Z) (t : mtrail) (reasons : Z -> option clause)
                   (db : list clause) : cdcl_view :=
  {| assignment := mt_pv t;
     level_of :=
       fun v => option_map (fun k => level_of_index t (Z.of_nat k)) (trail_pos t v);
     reason_of :=
       fun v => match trail_pos t v with Some _ => reasons v | None => None end;
     assignment_rank := trail_pos t;
     installed_clauses := db;
     current_level := Zlength (mt_lim t) |}.

Lemma mt_pv_nonneg : forall t v,
  0 <= v -> mt_pv t v = lbool_val (Znth v (mt_assigns t) 0).
Proof.
  intros t v H. unfold mt_pv, assigns_pv, assigns_val.
  assert (Hb : (0 <=? v) = true) by (apply Z.leb_le; lia).
  rewrite Hb. reflexivity.
Qed.

Lemma mt_pv_neg : forall t v, v < 0 -> mt_pv t v = None.
Proof.
  intros t v H. unfold mt_pv.
  assert (Hb : (0 <=? v) = false) by (apply Z.leb_gt; lia).
  rewrite Hb. reflexivity.
Qed.

Lemma mt_pv_zero_cell : forall t v,
  0 <= v -> Znth v (mt_assigns t) 0 = 0 -> mt_pv t v = None.
Proof.
  intros t v H0 Hz. rewrite mt_pv_nonneg by lia. rewrite Hz.
  apply lbool_val_none. split; discriminate.
Qed.

Lemma mt_pv_none_iff : forall n t v,
  mtrail_wf n t ->
  (mt_pv t v = None <-> ~ In v (map lit_var_c (mt_trail t))).
Proof.
  intros n t v Hwf.
  destruct (Z_lt_le_dec v 0) as [Hneg|Hpos].
  { split.
    - intros _ Hin. pose proof (trail_var_range n t v Hwf Hin). lia.
    - intros _. apply mt_pv_neg; lia. }
  destruct (Z_lt_le_dec v n) as [Hlt|Hge].
  - pose proof (Forall_Znth_elim _ _ _ 0 v (mtw_cells Hwf)) as Hcell.
    rewrite (mtw_assigns_len Hwf) in Hcell.
    specialize (Hcell (conj Hpos Hlt)).
    rewrite mt_pv_nonneg by lia.
    destruct (mtw_assigned_iff Hwf v (conj Hpos Hlt)) as [Hfwd Hbwd].
    split.
    + intros Hnone Hin. apply lbool_val_none in Hnone.
      apply Hbwd in Hin. destruct Hcell as [H|[H|H]]; lia.
    + intro Hnin. apply lbool_val_none.
      assert (Hz : Znth v (mt_assigns t) 0 = 0).
      { destruct Hcell as [H|[H|H]]; [|exact H|]; exfalso; apply Hnin; apply Hfwd; lia. }
      rewrite Hz. split; discriminate.
  - assert (Hz : Znth v (mt_assigns t) 0 = 0).
    { apply znth_out_of_bounds; [lia|]. rewrite (mtw_assigns_len Hwf). lia. }
    split.
    + intros _ Hin. pose proof (trail_var_range n t v Hwf Hin). lia.
    + intros _. apply mt_pv_zero_cell; assumption.
Qed.

Lemma trail_pos_none_iff : forall t v,
  trail_pos t v = None <-> ~ In v (map lit_var_c (mt_trail t)).
Proof. intros. apply find_var_pos_none_iff. Qed.

Lemma view_unassigned_iff : forall n t v,
  mtrail_wf n t -> (mt_pv t v = None <-> trail_pos t v = None).
Proof.
  intros n t v Hwf.
  rewrite (mt_pv_none_iff n t v Hwf), trail_pos_none_iff. reflexivity.
Qed.

Lemma trail_pos_bound : forall t v k,
  trail_pos t v = Some k -> Z.of_nat k < Zlength (mt_trail t).
Proof.
  intros t v k H. apply find_var_pos_bound in H.
  rewrite Zlength_correct. lia.
Qed.

Lemma trail_pos_var : forall t v k,
  trail_pos t v = Some k -> trail_var t (Z.of_nat k) = v.
Proof.
  intros t v k H. unfold trail_var, Znth. rewrite Nat2Z.id.
  apply find_var_pos_hit. exact H.
Qed.

(** ===== D. the three state transitions ===== *)

(** [enqueue] and [assume] differ only in whether a new
    [trail_lim] boundary was pushed first, so both go through one constructor:
    [levels[v] := solver_dlevel] is [Zlength lim'] in both cases. *)
Definition mt_push (t : mtrail) (l : Z) (lim' : list Z) : mtrail :=
  {| mt_assigns := replace_Znth (lit_var_c l) (lit_sig l) (mt_assigns t);
     mt_levels  := replace_Znth (lit_var_c l) (Zlength lim') (mt_levels t);
     mt_trail   := mt_trail t ++ [l];
     mt_lim     := lim';
     mt_qhead   := mt_qhead t |}.

Definition mt_enqueue (t : mtrail) (l : Z) : mtrail := mt_push t l (mt_lim t).

Definition mt_decide (t : mtrail) (l : Z) : mtrail :=
  mt_push t l (mt_lim t ++ [Zlength (mt_trail t)]).

(** [solver_canceluntil]: drop the trail above [trail_lim[level]],
    clear [assigns] (and, logically, [reasons]) for the dropped variables,
    shrink [trail_lim] to [level] and set [qhead = qtail = bound].  [levels] is
    deliberately left untouched -- stale cells are allowed. *)
Fixpoint clear_vars (ls : list Z) (a : list Z) : list Z :=
  match ls with
  | [] => a
  | x :: rest => clear_vars rest (replace_Znth (lit_var_c x) 0 a)
  end.

Definition mt_cancel (t : mtrail) (level : Z) : mtrail :=
  {| mt_assigns :=
       clear_vars (zdrop (Znth level (mt_lim t) 0) (mt_trail t)) (mt_assigns t);
     mt_levels  := mt_levels t;
     mt_trail   := ztake (Znth level (mt_lim t) 0) (mt_trail t);
     mt_lim     := ztake level (mt_lim t);
     mt_qhead   := Znth level (mt_lim t) 0 |}.

Lemma clear_vars_notin : forall ls a v,
  0 <= v < Zlength a ->
  (forall x, In x ls -> 0 <= lit_var_c x < Zlength a) ->
  ~ In v (map lit_var_c ls) ->
  Znth v (clear_vars ls a) 0 = Znth v a 0.
Proof.
  induction ls as [|x ls IH]; intros a v Hv Hrange Hnin; simpl; [reflexivity|].
  simpl in Hnin.
  assert (Hxv : lit_var_c x <> v) by (intro H; apply Hnin; left; exact H).
  rewrite IH.
  - apply Znth_replace_Znth_Diff;
      [apply Hrange; left; reflexivity|exact Hv|exact Hxv].
  - rewrite Zlength_replace_Znth. exact Hv.
  - intros y Hy. rewrite Zlength_replace_Znth. apply Hrange. right. exact Hy.
  - intro Hin. apply Hnin. right. exact Hin.
Qed.

Lemma clear_vars_in : forall ls a v,
  0 <= v < Zlength a ->
  (forall x, In x ls -> 0 <= lit_var_c x < Zlength a) ->
  In v (map lit_var_c ls) ->
  Znth v (clear_vars ls a) 0 = 0.
Proof.
  induction ls as [|x ls IH]; intros a v Hv Hrange Hin; simpl in *;
    [contradiction|].
  destruct (List.in_dec Z.eq_dec v (map lit_var_c ls)) as [Hrest|Hrest].
  - apply IH.
    + rewrite Zlength_replace_Znth. exact Hv.
    + intros y Hy. rewrite Zlength_replace_Znth. apply Hrange. right. exact Hy.
    + exact Hrest.
  - destruct Hin as [Heq|Hin]; [|contradiction].
    rewrite clear_vars_notin.
    + rewrite Heq. apply Znth_replace_Znth_Same. exact Hv.
    + rewrite Zlength_replace_Znth. exact Hv.
    + intros y Hy. rewrite Zlength_replace_Znth. apply Hrange. right. exact Hy.
    + exact Hrest.
Qed.

Lemma find_var_pos_some_in : forall v l k,
  find_var_pos v l = Some k -> In v (map lit_var_c l).
Proof.
  intros v l k H.
  destruct (List.in_dec Z.eq_dec v (map lit_var_c l)) as [H1|H1]; [exact H1|].
  apply find_var_pos_none_iff in H1. rewrite H1 in H. discriminate.
Qed.

(** ===== F. the backjump bridge ===== *)

Lemma mt_cancel_trail : forall t level,
  mt_trail (mt_cancel t level) = ztake (Znth level (mt_lim t) 0) (mt_trail t).
Proof. reflexivity. Qed.

Lemma mt_cancel_assigns : forall t level,
  mt_assigns (mt_cancel t level)
  = clear_vars (zdrop (Znth level (mt_lim t) 0) (mt_trail t)) (mt_assigns t).
Proof. reflexivity. Qed.

Lemma mt_cancel_levels : forall t level, mt_levels (mt_cancel t level) = mt_levels t.
Proof. reflexivity. Qed.

Lemma mt_pv_cancel_keep : forall n t level v,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  In v (map lit_var_c (mt_trail (mt_cancel t level))) ->
  mt_pv (mt_cancel t level) v = mt_pv t v.
Proof.
  intros n t level v Hwf Hlevel Hin.
  pose proof (lim_lt_trail n t level Hwf Hlevel) as Hb.
  rewrite mt_cancel_trail in Hin.
  assert (Hvr : 0 <= v < Zlength (mt_assigns t)).
  { apply in_map_iff in Hin. destruct Hin as [x [<- Hx]].
    rewrite (mtw_assigns_len Hwf). apply (lit_var_c_in_range n).
    pose proof (mtw_trail_lits Hwf) as HF. rewrite Forall_forall in HF.
    apply HF. eapply In_ztake; eauto. }
  rewrite !mt_pv_nonneg by lia.
  rewrite mt_cancel_assigns. f_equal.
  apply clear_vars_notin.
  - exact Hvr.
  - intros x Hx. rewrite (mtw_assigns_len Hwf). apply (lit_var_c_in_range n).
    pose proof (mtw_trail_lits Hwf) as HF. rewrite Forall_forall in HF.
    apply HF. eapply In_zdrop; eauto.
  - eapply NoDup_app_disjoint; [|exact Hin].
    rewrite <- map_ztake_zdrop. exact (mtw_trail_nodup Hwf).
Qed.

Definition decisions_upto (t : mtrail) (d : Z) : list literal :=
  map (fun b => lit_denote (Znth b (mt_trail t) 0)) (ztake d (mt_lim t)).

(** Every trail literal is entailed by [F] together with the decisions of the
    levels at or below its own.  Backjump-stability is built in: the hypothesis
    set is indexed by the literal's level, so a surviving literal only ever
    mentions surviving decisions. *)
Definition trail_implied (F : cnf) (t : mtrail) : Prop :=
  forall i l, 0 <= i < Zlength (mt_trail t) -> Znth i (mt_trail t) 0 = l ->
    entails_clause (cnf_with_units F (decisions_upto t (level_of_index t i)))
                   [lit_denote l].

(** * S5 -- watched literals.
    [wmap_exact] tracks occurrences with multiplicity. The propagation
    frontier tracks processed work, including the list under active rewrite.
    A drained frontier and total assignment imply database satisfaction. *)

Lemma Zlength_perm_eq :
  forall (A : Type) (l l' : list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
  intros A l l' H. rewrite !Zlength_correct.
  f_equal. apply Permutation_length. exact H.
Qed.

(** ** Ghost model of the clause database and the watcher map. *)

Record clause_obj := {
  co_lits : list Z;      (* packed literals, in memory order *)
  co_learnt : bool       (* the low bit of [size_learnt] *)
}.

Definition clause_obj_with_lits (co : clause_obj) (lits : list Z) : clause_obj :=
  {| co_lits := lits; co_learnt := co_learnt co |}.

Definition denote_obj (co : clause_obj) : clause := lits_denote (co_lits co).

Definition dbmap := list (Z * clause_obj).

Definition db_words (db : dbmap) : list Z := map fst db.

(** Boolean constants with names that cannot be shadowed by MiniSat's native
    integer-valued [true]/[false] identifiers in annotation expressions. *)
Definition msat_true : bool := true.

(** Exact two-database update induced by changing the selected object's
    literal order.  Exactly one of the problem/learnt maps contains [p], and
    the other map is byte-for-byte unchanged at the ghost level. *)
Definition db_pair_lits_update
    (prob learnt : dbmap) (p : Z) (old_lits new_lits : list Z)
    (prob' learnt' : dbmap) : Prop :=
  (exists co pre post,
      prob = pre ++ ((p, co) :: post) /\
      co_lits co = old_lits /\
      prob' = pre ++ ((p, clause_obj_with_lits co new_lits) :: post) /\
      learnt' = learnt) \/
  (exists co pre post,
      learnt = pre ++ ((p, co) :: post) /\
      co_lits co = old_lits /\
      prob' = prob /\
      learnt' = pre ++ ((p, clause_obj_with_lits co new_lits) :: post)).

(** [wmap] is [s->wlists]: [2*n] lists of watcher words.  A word is either
    an even clause pointer or an odd [tag_of_lit] tag. *)
Definition wmap := list (list Z).

Definition co_watch0 (co : clause_obj) : Z := Znth 0 (co_lits co) 0.

Definition co_watch1 (co : clause_obj) : Z := Znth 1 (co_lits co) 0.

Definition obj_wf (n : Z) (co : clause_obj) : Prop :=
  2 <= Zlength (co_lits co) /\
  Forall (lit_wf_c n) (co_lits co) /\
  NoDup (map lit_var_c (co_lits co)).

Definition db_wf (n : Z) (db : dbmap) : Prop :=
  NoDup (map fst db) /\
  Forall (fun e => 0 < fst e /\ Z.even (fst e) = true) db /\
  Forall (fun e => obj_wf n (snd e)) db.

(** The shared watch theory sees one logical occurrence for each live
    database entry.  The list map is exact, so duplicate entries would remain
    duplicate occurrences; [db_wf] independently rules out duplicate owners
    for this MiniSat representation. *)
Definition minisat_occurrence_of_entry
    (e : Z * clause_obj) : watch_occurrence Z :=
  match e with
  | (p, co) =>
      {| watch_owner := p;
         watch_body := denote_obj co;
         watch_left := lit_denote (co_watch0 co);
         watch_right := lit_denote (co_watch1 co) |}
  end.

Definition minisat_watch_occurrences
    (db : dbmap) : list (watch_occurrence Z) :=
  map minisat_occurrence_of_entry db.

(** ** INV-W1: expected watcher words.
    Clauses of size >= 3 contribute their pointer at the negations of both
    watched literals. Binary clauses contribute tags of the opposite literal. *)

Definition entry_watchers (e : Z * clause_obj) (l : Z) : list Z :=
  let (p, co) := e in
  (if lit_neg_c (co_watch0 co) =? l
   then [if 3 <=? Zlength (co_lits co) then p else tag_of_lit (co_watch1 co)]
   else nil)
  ++
  (if lit_neg_c (co_watch1 co) =? l
   then [if 3 <=? Zlength (co_lits co) then p else tag_of_lit (co_watch0 co)]
   else nil).

Definition expected_watchers (db : dbmap) (l : Z) : list Z :=
  flat_map (fun e => entry_watchers e l) db.

Definition minisat_focus_contribution : Type :=
  (watch_occurrence Z * Z)%type.

Definition minisat_entry_focus_contributions
    (p : Z) (e : Z * clause_obj) : list minisat_focus_contribution :=
  map (fun w => (minisat_occurrence_of_entry e, w)) (entry_watchers e p).

Definition minisat_focus_contributions
    (db : dbmap) (p : Z) : list minisat_focus_contribution :=
  flat_map (minisat_entry_focus_contributions p) db.

Definition minisat_focus_words
    (cs : list minisat_focus_contribution) : list Z :=
  map snd cs.

Definition minisat_occurrence_safe
    (P : literal -> Prop) (o : watch_occurrence Z) : Prop :=
  ~ (P (literal_neg (watch_left o)) /\
     P (literal_neg (watch_right o))).

(** [scanned] and [pending] are occurrence-indexed ghost tokens aligned with
    the compacted prefix and uninspected suffix.  The permutation is exact:
    duplicate physical words remain duplicate logical contributions. *)
Definition minisat_focus_scan_carrier
    (db : dbmap) (p : Z) (P : literal -> Prop)
    (kept rest : list Z) : Prop :=
  exists scanned pending : list minisat_focus_contribution,
    Permutation
      (scanned ++ pending)
      (minisat_focus_contributions db p) /\
    minisat_focus_words scanned = kept /\
    minisat_focus_words pending = rest /\
    Forall (fun c => minisat_occurrence_safe P (fst c)) scanned.

Definition wmap_exact (n : Z) (db : dbmap) (wm : wmap) : Prop :=
  Zlength wm = 2 * n /\
  forall l, 0 <= l < 2 * n -> Permutation (Znth l wm nil) (expected_watchers db l).

(** ** Literal status over the concrete lbool / level arrays. *)

Definition lit_true (assigns : list Z) (l : Z) : Prop :=
  Znth (lit_var_c l) assigns 0 = lit_sig l.

Definition lit_false (assigns : list Z) (l : Z) : Prop :=
  Znth (lit_var_c l) assigns 0 = - lit_sig l.

(** ** INV-W2: the processed-watch-list invariant. *)

(** [l] is *processed*: it is true and it sits strictly before [qhead] on
    the trail (so [solver_propagate] has already scanned [wlists[l]]). *)
Definition processed (assigns trail : list Z) (qhead l : Z) : Prop :=
  lit_true assigns l /\
  exists i, 0 <= i < qhead /\ Znth i trail 0 = l.

Definition minisat_processed
    (n : Z) (assigns trail : list Z) (qhead : Z) (l : literal) : Prop :=
  exists packed,
    lit_wf_c n packed /\
    lit_denote packed = l /\
    processed assigns trail qhead packed.

Definition minisat_watch_frontier
    (n : Z) (db : dbmap) (assigns trail : list Z) (qhead : Z) : Prop :=
  watch_frontier (minisat_watch_occurrences db)
    (minisat_processed n assigns trail qhead).

Definition minisat_watch_frontier_except
    (n : Z) (db : dbmap) (assigns trail : list Z) (qhead : Z)
    (focus : literal) : Prop :=
  watch_frontier_except (minisat_watch_occurrences db)
    (minisat_processed n assigns trail qhead) focus.

(** The watcher scan partitions words into [kept], [moved], and uninspected
    [rest]. It resizes the source list to [kept] and reattaches [moved]
    elsewhere; [kept ++ moved] is the [wmap_move] difference witness. *)
Definition wlist_scan_inv (ws0 kept moved rest : list Z) : Prop :=
  Permutation (kept ++ moved ++ rest) ws0.

(** ----- the order heap ----- *)

Record mheap := {
  mh_heap : list Z;      (* s->order: the heap array, variables *)
  mh_orderpos : list Z   (* s->orderpos: length n, [-1] = absent *)
}.

Definition heap_wf (n : Z) (h : mheap) : Prop :=
  Zlength (mh_orderpos h) = n /\
  NoDup (mh_heap h) /\
  Forall (fun v => 0 <= v < n) (mh_heap h) /\
  (forall v, 0 <= v < n ->
     Znth v (mh_orderpos h) (-1) = -1 \/
     (0 <= Znth v (mh_orderpos h) (-1) < Zlength (mh_heap h) /\
      Znth (Znth v (mh_orderpos h) (-1)) (mh_heap h) (-1) = v)) /\
  (forall i, 0 <= i < Zlength (mh_heap h) ->
     Znth (Znth i (mh_heap h) (-1)) (mh_orderpos h) (-1) = i).

(** ORD-INV: a variable outside the heap is assigned and its
    trail position is below [qhead] (i.e. it has been propagated). *)
Definition heap_covers (n : Z) (h : mheap)
                       (assigns trail : list Z) (qhead : Z) : Prop :=
  forall v, 0 <= v < n -> Znth v (mh_orderpos h) (-1) = -1 ->
    Znth v assigns 0 <> 0 /\
    (exists i, 0 <= i < qhead /\ lit_var_c (Znth i trail 0) = v).

(** ----- the pop/assume transient ----- *)

(** After popping a decision candidate, heap coverage may fail only for
    [v0]: first it is unassigned, then queued at [qhead]. The first dequeue
    restores ordinary coverage. *)
Definition heap_covers_except (n : Z) (h : mheap)
    (assigns trail : list Z) (qhead : Z) (v0 : Z) : Prop :=
  forall v, 0 <= v < n -> v <> v0 ->
    Znth v (mh_orderpos h) (-1) = -1 ->
    Znth v assigns 0 <> 0 /\
    (exists i, 0 <= i < qhead /\ lit_var_c (Znth i trail 0) = v).


Definition heap_of_lists (order orderpos : list Z) : mheap :=
  {| mh_heap := order; mh_orderpos := orderpos |}.

Definition seed_ok (s : Z) : Prop := 1 <= s <= 2147483646.

(** * S8 -- spatial representations.
    QCP names [A::B] resolve to Rocq [A.B]. Array predicates come from the
    framework; clause predicates are defined in [MiniSatClause].
    Struct fields use their C tags. Flexible literal arrays begin at the
    [lits] field address, and watcher-table strides use [sizeof("vecp_t")],
    matching the frontend's native indexing without hardcoded byte offsets. *)

(** ** Clause objects.
    The header packs [2 * size + learnt], followed by the literals.
    Only learned clauses have a float activity tail; its initialized value
    satisfies [msat_fp32_nonnegative]. [activity_undef] and [owned] retain
    the same conditional footprint without fixing the stored values. *)

Definition clause_hdr_addr (c : Z) : Z := &( c # "clause_t" ->ₛ "size_learnt").

Definition clause_lits_addr (c : Z) : Z := &( c # "clause_t" ->ₛ "lits").

Definition clause_act_addr (c size : Z) : Z :=
  clause_lits_addr c + size * sizeof(INT).

(** A stable carrier for the address returned by [clause_begin].  The C
    symbolic executor deliberately keeps this relation opaque so successive
    calls can share the same array base without rewriting spatial addresses
    through a pure pointer equality. *)
Definition clause_lits_pointer (c p : Z) : Prop :=
  p = clause_lits_addr c.

Definition clause_hdr_word (learnt : bool) (size : Z) : Z :=
  2 * size + (if learnt then 1 else 0).

Definition activity_undef (c : Z) (learnt : bool) (size : Z) : Assertion :=
  if learnt then clause_act_addr c size # Float |->_ else emp.

Definition activity_state (c : Z) (learnt : bool) (size : Z) : Assertion :=
  if learnt
  then EX a : fp32,
         “ msat_fp32_nonnegative a ” &&
         clause_act_addr c size # Float |-> a
  else emp.

Module MiniSatClause.

  Definition undef (c : Z) (learnt : bool) (size : Z) : Assertion :=
    “ 0 <= size /\ 0 < c /\ c mod 2 = 0 ” &&
    (clause_hdr_addr c # Int |->_ **
     activity_undef c learnt size **
     IntArray.undef_seg (clause_lits_addr c) 0 size).

  Definition rep (c : Z) (learnt : bool) (lits : list Z) : Assertion :=
    “ 0 <= Zlength lits /\ 0 < c /\ c mod 2 = 0 ” &&
    (clause_hdr_addr c # Int |-> clause_hdr_word learnt (Zlength lits) **
     activity_state c learnt (Zlength lits) **
     IntArray.seg (clause_lits_addr c) 0 (Zlength lits) lits).

  Definition owned (c : Z) (learnt : bool) (size : Z) : Assertion :=
    “ 0 <= size /\ 0 < c /\ c mod 2 = 0 ” &&
    (clause_hdr_addr c # Int |->_ **
     activity_undef c learnt size **
     IntArray.undef_seg (clause_lits_addr c) 0 size).

End MiniSatClause.

(** A scratch clause always has a two-literal allocation and header.  The
    empty logical list marks storage whose literal cells have not both been
    initialized; it is not the contents of an empty clause.  Only nonempty
    scratch contents may be exposed to conflict analysis. *)
Definition binary_scratch_rep (c : Z) (words : list Z) : Assertion :=
  match words with
  | [] =>
      “ 0 < c /\ c mod 2 = 0 ” &&
      (clause_hdr_addr c # Int |-> clause_hdr_word false 2 **
       activity_state c false 2 **
       IntArray.undef_seg (clause_lits_addr c) 0 2)
  | _ :: _ => MiniSatClause.rep c false words
  end.

(** ** Integer and pointer vectors.
    [veci] and [vecp] are the growable vectors of [vec_qcp.h]
    ([vec_qcp_lib]); a pointer is stored as its [Z] address.  [Veci.rep v l]
    says the vector at [v] holds [l]; [Veci.rep_at v p l cap] also names its
    buffer [p] and capacity [cap]. *)

Definition clause_watch_word
    (c : Z) (lits : list Z) (other : Z) : Z :=
  if Z.ltb 2 (Zlength lits) then c else tag_of_lit other.

(** The watcher table is an array of [2*n] pointer vectors, one per literal:
    slot [Vecp.slot base i] holds the watchers of literal [i]. *)

Definition wlists_rep (base n : Z) (wm : wmap) : Assertion :=
  “ Zlength wm = 2 * n ” && VecpArray.full base (2 * n) wm.

(** The database owns clause objects separately from the vectors of their
    pointers, allowing reduction to remove pointers and free objects in
    separate steps. [clause_db_rep] iterates [MiniSatClause.rep]. *)

Fixpoint clause_db_rep (entries : dbmap) : Assertion :=
  match entries with
  | nil => emp
  | e :: rest =>
      MiniSatClause.rep (fst e) (co_learnt (snd e)) (co_lits (snd e)) **
      clause_db_rep rest
  end.

(** Every entry in [s->learnts] carries an initialized activity cell. *)
Definition learnt_db (entries : dbmap) : Prop :=
  Forall (fun e => co_learnt (snd e) = true) entries.

(** Problem-clause tags distinguish the two database halves: a learned
    object in [ms_prob ++ ms_learnt] must belong to [ms_learnt]. *)
Definition prob_db (entries : dbmap) : Prop :=
  Forall (fun e => co_learnt (snd e) = false) entries.

(** Activity is absent from [clause_obj] because it has no SAT semantics, but
    quicksort safety needs comparator results to remain stable across swaps.
    This representation aligns one concrete activity value with every learnt
    database entry while owning the same clause cells as [clause_db_rep]. *)
Fixpoint learnt_sort_rep (db : dbmap) (activities : list fp32) : Assertion :=
  match db, activities with
  | nil, nil => emp
  | (p, co) :: db', a :: activities' =>
      “ co_learnt co = true /\ 0 < p /\ p mod 2 = 0 /\
        msat_fp32_nonnegative a ” &&
      (clause_hdr_addr p # Int |->
         clause_hdr_word true (Zlength (co_lits co)) **
       clause_act_addr p (Zlength (co_lits co)) # Float |-> a **
       IntArray.seg (clause_lits_addr p) 0
         (Zlength (co_lits co)) (co_lits co) **
       learnt_sort_rep db' activities')
  | _, _ => “ False ”
  end.

Fixpoint learnt_sort_key
    (db : dbmap) (activities : list fp32)
    (p : Z) (co : clause_obj) (a : fp32) : Prop :=
  match db, activities with
  | nil, nil => False
  | (q, cq) :: db', aq :: activities' =>
      (p = q /\ co = cq /\ a = aq) \/
      learnt_sort_key db' activities' p co a
  | _, _ => False
  end.

Definition learnt_cmp_lt
    (db : dbmap) (activities : list fp32) (x y : Z) : Prop :=
  exists cox coy ax ay,
    learnt_sort_key db activities x cox ax /\
    learnt_sort_key db activities y coy ay /\
    2 < Zlength (co_lits cox) /\
    (Zlength (co_lits coy) = 2 \/ fp32_lt ax ay).

Definition learnt_cmp_stop
    (db : dbmap) (activities : list fp32) (x y : Z) : Prop :=
  ~ learnt_cmp_lt db activities x y.

Definition learnt_cmp_result
    (db : dbmap) (activities : list fp32) (x y ret : Z) : Prop :=
  (ret = -1 /\ learnt_cmp_lt db activities x y) \/
  (ret = 1 /\ learnt_cmp_stop db activities x y).

Definition learnt_clause_snapshot_raw
    (p : Z) (lits : list Z) (activity : fp32) : Assertion :=
  “ 0 < p /\ p mod 2 = 0 /\ msat_fp32_nonnegative activity ” &&
  (clause_hdr_addr p # Int |-> clause_hdr_word true (Zlength lits) **
   clause_act_addr p (Zlength lits) # Float |-> activity **
   IntArray.seg (clause_lits_addr p) 0 (Zlength lits) lits).

Definition learnt_sort_alias_remainder
    (db : dbmap) (activities : list fp32)
    (x : Z) (xlits : list Z) (xa : fp32) : Assertion :=
  EX co : clause_obj, EX pre post : dbmap,
  EX apre apost : list fp32,
    “ db = pre ++ (x, co) :: post /\
      activities = apre ++ xa :: apost /\
      Zlength pre = Zlength apre /\
      co_lits co = xlits /\ co_learnt co = true /\
      msat_fp32_nonnegative xa ” &&
    (learnt_sort_rep pre apre ** learnt_sort_rep post apost).

Definition learnt_sort_two_remainder
    (db : dbmap) (activities : list fp32)
    (x : Z) (xlits : list Z) (xa : fp32)
    (y : Z) (ylits : list Z) (ya : fp32) : Assertion :=
  (EX cox coy : clause_obj, EX pre mid post : dbmap,
   EX apre amid apost : list fp32,
    “ db = pre ++ (x, cox) :: mid ++ (y, coy) :: post /\
      activities = apre ++ xa :: amid ++ ya :: apost /\
      Zlength pre = Zlength apre /\ Zlength mid = Zlength amid /\
      co_lits cox = xlits /\ co_lits coy = ylits /\
      co_learnt cox = true /\ co_learnt coy = true /\
      msat_fp32_nonnegative xa /\ msat_fp32_nonnegative ya ” &&
    (learnt_sort_rep pre apre ** learnt_sort_rep mid amid **
     learnt_sort_rep post apost)) ||
  (EX cox coy : clause_obj, EX pre mid post : dbmap,
   EX apre amid apost : list fp32,
    “ db = pre ++ (y, coy) :: mid ++ (x, cox) :: post /\
      activities = apre ++ ya :: amid ++ xa :: apost /\
      Zlength pre = Zlength apre /\ Zlength mid = Zlength amid /\
      co_lits cox = xlits /\ co_lits coy = ylits /\
      co_learnt cox = true /\ co_learnt coy = true /\
      msat_fp32_nonnegative xa /\ msat_fp32_nonnegative ya ” &&
    (learnt_sort_rep pre apre ** learnt_sort_rep mid amid **
     learnt_sort_rep post apost)).

Definition clause_db_pair_remainder
    (prob learnt : dbmap) (p : Z) (is_learnt : bool)
    (lits : list Z) : Assertion :=
  (EX co : clause_obj, EX pre post : dbmap,
     “ prob = pre ++ ((p, co) :: post) /\
       co_lits co = lits /\ co_learnt co = is_learnt ” &&
     (clause_db_rep pre ** clause_db_rep post ** clause_db_rep learnt)) ||
  (EX co : clause_obj, EX pre post : dbmap,
     “ learnt = pre ++ ((p, co) :: post) /\
       co_lits co = lits /\ co_learnt co = is_learnt ” &&
     (clause_db_rep prob ** clause_db_rep pre ** clause_db_rep post)).

(** Header/activity ownership retained while a focused clause's literal array
    is exposed to C. *)
Definition clause_db_pair_frame
    (prob learnt : dbmap) (p : Z) (lits : list Z) : Assertion :=
  EX is_learnt : bool,
    clause_hdr_addr p # Int |->
      clause_hdr_word is_learnt (Zlength lits) **
    activity_state p is_learnt (Zlength lits) **
    clause_db_pair_remainder prob learnt p is_learnt lits.

Lemma clause_db_rep_app_intro : forall db1 db2,
  clause_db_rep db1 ** clause_db_rep db2 |-- clause_db_rep (db1 ++ db2).
Proof.
  induction db1 as [| e db1 IH]; intros db2; simpl.
  - (Intros; cancel).
  - sep_apply (IH db2). cancel.
Qed.

(** Statistics are eleven owned uint64 counters. *)

Definition stats_starts           (l : list Z) : Z := Znth 0  l 0.

Definition stats_decisions        (l : list Z) : Z := Znth 1  l 0.

Definition stats_propagations     (l : list Z) : Z := Znth 2  l 0.

Definition stats_inspects         (l : list Z) : Z := Znth 3  l 0.

Definition stats_conflicts        (l : list Z) : Z := Znth 4  l 0.

Definition stats_clauses          (l : list Z) : Z := Znth 5  l 0.

Definition stats_clauses_literals (l : list Z) : Z := Znth 6  l 0.

Definition stats_learnts          (l : list Z) : Z := Znth 7  l 0.

Definition stats_learnts_literals (l : list Z) : Z := Znth 8  l 0.

Definition stats_max_literals     (l : list Z) : Z := Znth 9  l 0.

Definition stats_tot_literals     (l : list Z) : Z := Znth 10 l 0.

Definition stats_rep (p : Z) (st : list Z) : Assertion :=
  “ Zlength st = 11 ” &&
  (&( p # "stats_t" ->ₛ "starts")           # UInt64 |-> stats_starts st **
   &( p # "stats_t" ->ₛ "decisions")        # UInt64 |-> stats_decisions st **
   &( p # "stats_t" ->ₛ "propagations")     # UInt64 |-> stats_propagations st **
   &( p # "stats_t" ->ₛ "inspects")         # UInt64 |-> stats_inspects st **
   &( p # "stats_t" ->ₛ "conflicts")        # UInt64 |-> stats_conflicts st **
   &( p # "stats_t" ->ₛ "clauses")          # UInt64 |-> stats_clauses st **
   &( p # "stats_t" ->ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
   &( p # "stats_t" ->ₛ "learnts")          # UInt64 |-> stats_learnts st **
   &( p # "stats_t" ->ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st **
   &( p # "stats_t" ->ₛ "max_literals")     # UInt64 |-> stats_max_literals st **
   &( p # "stats_t" ->ₛ "tot_literals")     # UInt64 |-> stats_tot_literals st).

(** ** Solver state.
    Core, database, watchers, and heuristics share one record. Raw reason
    words and ghost clauses remain separate: the semantic invariant decodes
    both real pointers and odd binary-reason tags. *)

Record msolver := {
  (* --- sizes ------------------------------------------------------------ *)
  ms_size        : Z;                  (* s->size : number of variables      *)
  ms_cap         : Z;                  (* s->cap  : varmap capacity          *)
  ms_qtail       : Z;
  ms_capacity_pending_qhead : Z;
  ms_capacity_root_propagation_pending : Z;
  (* --- assignment core (S4) --------------------------------------------- *)
  ms_core        : mtrail;             (* assigns/levels/trail/trail_lim/qhead *)
  ms_root_level  : Z;
  (* --- reasons ----------------------------------------------------------- *)
  ms_reason_words : list Z;            (* s->reasons, raw words              *)
  ms_reason_of   : Z -> option clause; (* ghost reason clauses *)
  (* --- clause database ---------------------------------------------------- *)
  ms_prob        : dbmap;
  ms_learnt      : dbmap;
  ms_binary      : Z;                  (* s->binary, the temp binary clause  *)
  ms_binary_lits : list Z;
  (* --- watcher table ------------------------------------------------------ *)
  ms_wm          : wmap;               (* s->wlists contents                 *)
  (* --- heuristics --------------------------------------------------------- *)
  ms_activity    : list fp64;
  ms_orderpos    : list Z;
  ms_order       : list Z;
  ms_model       : list Z;
  ms_tags        : list Z;
  ms_tagged      : list Z;
  ms_stack       : list Z;
  (* --- floating-point knobs ----------------------------------------------- *)
  ms_var_inc     : fp64;
  ms_var_decay   : fp64;
  ms_cla_inc     : fp32;
  ms_cla_decay   : fp32;
  ms_random_seed : fp64;
  ms_progress    : fp64;
  (* --- misc scalars -------------------------------------------------------- *)
  ms_simpdb_assigns : Z;
  ms_simpdb_props   : Z;
  ms_verbosity      : Z;
  ms_stats          : list Z
}.


Definition msolver_propagation_update (M : msolver)
    (cap : Z)
    (qtail : Z)
    (capacity_root_propagation_pending : Z)
    (core : mtrail)
    (reason_words : list Z)
    (reason_of : Z -> option clause)
    (prob : dbmap)
    (learnt : dbmap)
    (binary_lits : list Z)
    (wm : wmap)
    (simpdb_props : Z)
    (stats : list Z) : msolver := {|
  ms_size := ms_size M;
  ms_cap := cap;
  ms_qtail := qtail;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending := capacity_root_propagation_pending;
  ms_core := core;
  ms_root_level := ms_root_level M;
  ms_reason_words := reason_words;
  ms_reason_of := reason_of;
  ms_prob := prob;
  ms_learnt := learnt;
  ms_binary := ms_binary M;
  ms_binary_lits := binary_lits;
  ms_wm := wm;
  ms_activity := ms_activity M;
  ms_orderpos := ms_orderpos M;
  ms_order := ms_order M;
  ms_model := ms_model M;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M;
  ms_stack := ms_stack M;
  ms_var_inc := ms_var_inc M;
  ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M;
  ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M;
  ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := simpdb_props;
  ms_verbosity := ms_verbosity M;
  ms_stats := stats
|}.

(** A narrow overlay for the fields that can genuinely evolve while one
    propagation watcher vector is open. *)
Definition msolver_propagation_overlay
    (M : msolver) (core : mtrail) (qtail : Z)
    (reason_words : list Z) (reason_of : Z -> option clause)
    (prob learnt : dbmap) (binary_lits : list Z)
    (wm : wmap) (stats : list Z) : msolver :=
  msolver_propagation_update M (ms_cap M) (qtail) (ms_capacity_root_propagation_pending M) (core) (reason_words)
    (reason_of) (prob) (learnt) (binary_lits) (wm) (ms_simpdb_props M) (stats).

(** Recording has one additional enqueue shape that propagation never uses:
    a unary learned consequence is installed with the raw null reason and the
    ghost reason map entry [None]. *)
Definition msolver_enqueue_fresh
    (M : msolver) (l reason_word : Z) (reason_opt : option clause) : msolver :=
  let v := lit_var_c l in
  msolver_propagation_overlay M
    (mt_enqueue (ms_core M) l) (ms_qtail M + 1)
    (replace_Znth v reason_word (ms_reason_words M))
    (sat_function_update (ms_reason_of M) v reason_opt)
    (ms_prob M) (ms_learnt M) (ms_binary_lits M)
    (ms_wm M) (ms_stats M).

(** Exact solver state after [assume]: one decision boundary and literal are
    appended, and the fresh variable receives a null reason. *)
Definition msolver_assume
    (M : msolver) (l : Z) : msolver := {|
  ms_size := ms_size M; ms_cap := ms_cap M; ms_qtail := ms_qtail M + 1;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending :=
    ms_capacity_root_propagation_pending M;
  ms_core := mt_decide (ms_core M) l; ms_root_level := ms_root_level M;
  ms_reason_words := replace_Znth
    (lit_var_c l) 0 (ms_reason_words M);
  ms_reason_of := sat_function_update
    (ms_reason_of M) (lit_var_c l) None;
  ms_prob := ms_prob M; ms_learnt := ms_learnt M;
  ms_binary := ms_binary M; ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M; 
  ms_activity := ms_activity M; ms_orderpos := ms_orderpos M;
  ms_order := ms_order M; 
  ms_model := ms_model M;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M; 
  ms_stack := ms_stack M; 
  ms_var_inc := ms_var_inc M; ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M; ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M; ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M; ms_stats := ms_stats M
|}.

Definition msolver_propagation_db_wmap_update
    (M : msolver) (prob learnt : dbmap) (wm : wmap)
    : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    prob learnt (ms_binary_lits M) wm (ms_stats M).

(** Remove exactly one database pointer while retaining every component that
    clause deletion does not mutate. *)
Fixpoint db_remove_ptr (p : Z) (db : dbmap) : dbmap :=
  match db with
  | [] => []
  | e :: rest =>
      if Z.eq_dec (fst e) p then rest else e :: db_remove_ptr p rest
  end.

Definition msolver_remove_clause
    (M : msolver) (from_learnt : bool) (p : Z)
    (wm : wmap) (stats : list Z) : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    (if from_learnt then ms_prob M else db_remove_ptr p (ms_prob M))
    (if from_learnt then db_remove_ptr p (ms_learnt M) else ms_learnt M)
    (ms_binary_lits M) wm stats.

Definition msolver_core_heap_update
    (M : msolver) (core : mtrail) (qtail : Z)
    (reason_words : list Z) (reason_of : Z -> option clause)
    (orderpos order : list Z) (root : Z) : msolver := {|
  ms_size           := ms_size M;
  ms_cap            := ms_cap M;
  ms_qtail          := qtail;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending :=
    ms_capacity_root_propagation_pending M;
  ms_core           := core;
  ms_root_level     := root;
  ms_reason_words   := reason_words;
  ms_reason_of      := reason_of;
  ms_prob           := ms_prob M;
  ms_learnt         := ms_learnt M;
  ms_binary         := ms_binary M;
  ms_binary_lits    := ms_binary_lits M;
  ms_wm             := ms_wm M;
  ms_activity       := ms_activity M;
  ms_orderpos       := orderpos;
  ms_order          := order;
  ms_model          := ms_model M;
  ms_tags           := ms_tags M;
  ms_tagged         := ms_tagged M;
  ms_stack          := ms_stack M;
  ms_var_inc        := ms_var_inc M;
  ms_var_decay      := ms_var_decay M;
  ms_cla_inc        := ms_cla_inc M;
  ms_cla_decay      := ms_cla_decay M;
  ms_random_seed    := ms_random_seed M;
  ms_progress       := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props   := ms_simpdb_props M;
  ms_verbosity      := ms_verbosity M;
  ms_stats          := ms_stats M
|}.

Fixpoint clear_reason_fun
    (trail_suffix : list Z) (r : Z -> option clause) : Z -> option clause :=
  match trail_suffix with
  | [] => r
  | l :: rest =>
      clear_reason_fun rest (sat_function_update r (lit_var_c l) None)
  end.

Lemma clear_reason_fun_notin : forall suffix r v,
  ~ In v (map lit_var_c suffix) ->
  clear_reason_fun suffix r v = r v.
Proof.
  induction suffix as [|l suffix IH]; intros r v Hnot; simpl; [reflexivity|].
  simpl in Hnot.
  rewrite IH.
  - apply sat_function_update_neq. intro Heq.
    apply Hnot. left. exact Heq.
  - intro Hin. apply Hnot. right. exact Hin.
Qed.

Definition msolver_cancel_project
    (M : msolver) (level : Z) (orderpos order : list Z)
    (root : Z)
    : msolver :=
  let bound := Znth level (mt_lim (ms_core M)) 0 in
  msolver_core_heap_update M (mt_cancel (ms_core M) level) bound
    (clear_vars (zdrop bound (mt_trail (ms_core M))) (ms_reason_words M))
    (clear_reason_fun (zdrop bound (mt_trail (ms_core M))) (ms_reason_of M))
    orderpos order root.

Definition wmap_push_word (wm : wmap) (i word : Z) : wmap :=
  replace_Znth i (Znth i wm [] ++ [word]) wm.

Definition clause_new_watch_map
    (M : msolver) (c : Z) (words : list Z) : wmap :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  let wm0 := wmap_push_word (ms_wm M) i0
    (clause_watch_word c words (Znth 1 words 0)) in
  wmap_push_word wm0 i1
    (clause_watch_word c words (Znth 0 words 0)).

Definition msolver_install_learnt_clause
    (M : msolver) (c : Z) (words : list Z) : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    (ms_prob M)
    (ms_learnt M ++ [(c, {| co_lits := words; co_learnt := true |})])
    (ms_binary_lits M) (clause_new_watch_map M c words) (ms_stats M).

(** Dimensions guaranteed by the spatial bundle. Semantic invariants stay
    separate so function handoffs can frame and cancel the representation. *)
Definition solver_shape (M : msolver) : Prop :=
  0 <= ms_size M <= ms_cap M /\
  ms_cap M <= INT_MAX /\
  2 * ms_size M <= INT_MAX /\
  Zlength (mt_assigns (ms_core M)) = ms_size M /\
  Zlength (mt_levels (ms_core M)) = ms_size M /\
  Zlength (ms_reason_words M) = ms_size M /\
  Zlength (ms_orderpos M) = ms_size M /\
  Zlength (ms_activity M) = ms_size M /\
  Zlength (ms_tags M) = ms_size M /\
  Zlength (mt_trail (ms_core M)) = ms_qtail M /\
  0 <= mt_qhead (ms_core M) <= ms_qtail M /\
  0 <= ms_capacity_pending_qhead M <= INT_MAX /\
  (ms_capacity_root_propagation_pending M = 0 \/
   ms_capacity_root_propagation_pending M = 1) /\
  (ms_capacity_root_propagation_pending M = 1 ->
     ms_capacity_pending_qhead M < ms_qtail M /\
     mt_qhead (ms_core M) = ms_qtail M /\
     ms_root_level M = 0 /\
     Zlength (mt_lim (ms_core M)) = 0) /\
  0 <= ms_qtail M <= ms_cap M /\
  Zlength (ms_wm M) = 2 * ms_size M /\
  (ms_binary_lits M = [] \/ Zlength (ms_binary_lits M) = 2) /\
  Zlength (ms_stats M) = 11 /\
  0 <= ms_root_level M /\
  (* The binary scratch pointer is non-null for conflict detection and even
     for the real-clause branch of [clause_is_lit]. *)
  ms_binary M <> 0 /\
  Z.even (ms_binary M) = true.

(** *** The [solver_t] fields, in four groups. *)

Definition solver_scalars_rep (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size")           # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap")            # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qhead")          # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "qtail")          # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "root_level")     # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props")   # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity")      # Int |-> ms_verbosity M.

Definition solver_fp_rep (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "var_inc")           # Double |-> ms_var_inc M **
  &( s # "solver_t" ->ₛ "var_decay")         # Double |-> ms_var_decay M **
  &( s # "solver_t" ->ₛ "cla_inc")           # Float  |-> ms_cla_inc M **
  &( s # "solver_t" ->ₛ "cla_decay")         # Float  |-> ms_cla_decay M **
  &( s # "solver_t" ->ₛ "random_seed")       # Double |-> ms_random_seed M **
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M.

(** The seven embedded vectors.  [clauses]/[learnts] hold the DB pointers, so
    their contents are [map fst] of the corresponding [dbmap]. *)
Definition solver_vecs_rep (s : Z) (M : msolver) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")    (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")     (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")     (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model")     (ms_model M).

(** Outer arrays retain their full physical allocation when a later member
    of a growth batch falls back to a smaller common logical capacity.
    These extents are ghost witnesses, not additional native fields. An array
    without physical extent stores NULL ([vec_buf_ok]), which keeps its first
    realloc defined. *)
Definition solver_array_tail
    (tail : Z -> Z -> Z -> Assertion) (p lo cap : Z) : Assertion :=
  EX physical : Z,
    “ cap <= physical /\ physical <= INT_MAX /\ vec_buf_ok physical p ” &&
    tail p lo physical.

Definition solver_int_tail := solver_array_tail IntArray.undef_seg.
Definition solver_ptr_tail := solver_array_tail PtrArray.undef_seg.
Definition solver_char_tail := solver_array_tail CharArray.undef_seg.
Definition solver_double_tail := solver_array_tail DoubleArray.undef_seg.
Definition solver_wlists_tail := solver_array_tail VecpArray.undef_seg.

Lemma solver_array_tail_exact : forall tail p lo cap,
  cap <= INT_MAX -> vec_buf_ok cap p ->
  tail p lo cap |-- solver_array_tail tail p lo cap.
Proof.
  intros; unfold solver_array_tail; Exists cap; (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
Qed.

Lemma solver_array_tail_lower : forall tail p lo cap smaller,
  smaller <= cap ->
  solver_array_tail tail p lo cap |-- solver_array_tail tail p lo smaller.
Proof.
  intros; unfold solver_array_tail; Intros physical; Exists physical;
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia) | vec_buf_solve] ..]).
Qed.


Definition solver_var_arrays_rep
    (M : msolver) (act asg opos rsn lvl tgs : Z) : Assertion :=
  DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
  solver_double_tail act (ms_size M) (ms_cap M) **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  solver_char_tail asg (ms_size M) (ms_cap M) **
  IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
  solver_int_tail opos (ms_size M) (ms_cap M) **
  PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
  solver_ptr_tail rsn (ms_size M) (ms_cap M) **
  IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
  solver_int_tail lvl (ms_size M) (ms_cap M) **
  CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
  solver_char_tail tgs (ms_size M) (ms_cap M).

Definition solver_trail_array_rep (M : msolver) (trl : Z) : Assertion :=
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  solver_int_tail trl (ms_qtail M) (ms_cap M).

Definition solver_levels_slice_at
    (s : Z) (M : msolver) (lvl : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
  IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
  solver_int_tail lvl (ms_size M) (ms_cap M).

Definition solver_nonlevel_rep_nostats_at
    (s : Z) (M : msolver)
    (wl act asg opos rsn trl tgs : Z) : Assertion :=
  solver_scalars_rep s M **
  solver_fp_rep s M **
  solver_vecs_rep s M **
  (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
   &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
   &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
   &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
   &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
   &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
   &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
   &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
  (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
   solver_double_tail act (ms_size M) (ms_cap M) **
   CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
   solver_char_tail asg (ms_size M) (ms_cap M) **
   IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
   solver_int_tail opos (ms_size M) (ms_cap M) **
   PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
   solver_ptr_tail rsn (ms_size M) (ms_cap M) **
   CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
   solver_char_tail tgs (ms_size M) (ms_cap M)) **
  solver_trail_array_rep M trl **
  wlists_rep wl (ms_size M) (ms_wm M) **
  clause_db_rep (ms_prob M) **
  clause_db_rep (ms_learnt M) **
  binary_scratch_rep (ms_binary M) (ms_binary_lits M).

Definition solver_nonlevel_rep_at
    (s : Z) (M : msolver)
    (wl act asg opos rsn trl tgs : Z) : Assertion  :=
  solver_nonlevel_rep_nostats_at s M wl act asg opos rsn trl tgs **
  stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

Definition solver_nonlevel_rep (s : Z) (M : msolver) : Assertion :=
  EX wl act asg opos rsn trl tgs : Z,
    solver_nonlevel_rep_at s M wl act asg opos rsn trl tgs.

(** A clause-allocation transaction opens only the learned database vector,
    learned objects, watcher table, table pointer, and [size].  Everything
    else stays in this named frame across all three reserve stages. *)
Definition clause_new_scalars_frame (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "cap")            # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qhead")          # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "qtail")          # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "root_level")     # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props")   # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity")      # Int |-> ms_verbosity M.

Definition solver_vecs_without_learnts_rep (s : Z) (M : msolver) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
           (ms_model M).

Definition clause_new_ptrs_frame
    (s : Z) (M : msolver) (act asg opos rsn lvl trl tgs : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
  &( s # "solver_t" ->ₛ "assigns")  # Ptr |-> asg **
  &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
  &( s # "solver_t" ->ₛ "reasons")  # Ptr |-> rsn **
  &( s # "solver_t" ->ₛ "levels")   # Ptr |-> lvl **
  &( s # "solver_t" ->ₛ "trail")    # Ptr |-> trl **
  &( s # "solver_t" ->ₛ "binary")   # Ptr |-> ms_binary M **
  &( s # "solver_t" ->ₛ "tags")     # Ptr |-> tgs.

Definition clause_new_frame_at (s : Z) (M : msolver) (lvl : Z) : Assertion :=
  EX act asg opos rsn trl tgs : Z,
    clause_new_scalars_frame s M ** solver_fp_rep s M **
    solver_vecs_without_learnts_rep s M **
    clause_new_ptrs_frame s M act asg opos rsn lvl trl tgs **
    solver_var_arrays_rep M act asg opos rsn lvl tgs **
    solver_trail_array_rep M trl **
    clause_db_rep (ms_prob M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** Complement of the exact [enqueue_state_at] footprint. *)
Definition solver_scalars_without_qtail_rep
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns")
    # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M.

Definition solver_vecs_without_lim_rep (s : Z) (M : msolver) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
    (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
    (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
    (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
    (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
    (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
    (ms_model M).

Definition solver_enqueue_cells_at
    (s : Z) (M : msolver) (wl act opos tgs : Z) (scalars : Assertion) : Assertion :=
    scalars ** solver_fp_rep s M **
    solver_vecs_without_lim_rep s M **
    (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
     &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
     &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
     &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
     &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
    (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
     solver_double_tail act (ms_size M) (ms_cap M) **
     IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
     solver_int_tail opos (ms_size M) (ms_cap M) **
     CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
     solver_char_tail tgs (ms_size M) (ms_cap M)) **
    wlists_rep wl (ms_size M) (ms_wm M) **
    clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** [assume] consumes [qhead] in addition to [enqueue_state_at]; every other
    solver cell is the exact frame below. *)
Definition solver_assume_scalars_frame
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns")
    # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M.

Definition solver_cancel_owned (s : Z) (M : msolver) (wl : Z) : Assertion :=
  “ solver_shape M ” && (EX act asg opos rsn trl tgs : Z,
    solver_nonlevel_rep_at s M wl act asg opos rsn trl tgs).

(** Stable remainder for [solver_lit_removable].  The six resources it opens
    (size, reasons, levels, tags, tagged, stack) and the three clause-object
    regions are deliberately absent. *)
Definition solver_removable_frame_at
    (s : Z) (M : msolver) (trl : Z) (wl : Z) : Assertion :=
  clause_new_scalars_frame s M ** solver_fp_rep s M **
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) **
  &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
  (EX act asg opos : Z,
    &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
    &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
    DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
    solver_double_tail act (ms_size M) (ms_cap M) **
    CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
    solver_char_tail asg (ms_size M) (ms_cap M) **
    IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
    solver_int_tail opos (ms_size M) (ms_cap M) **
    solver_trail_array_rep M trl **
    wlists_rep wl (ms_size M) (ms_wm M)) **
  stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** Analyzer-owned fields are opened in C because the resolution pass bumps
    both kinds of activity, grows the scratch vectors, compacts the learned
    vector, and updates the two literal counters.  This frame owns exactly
    the untouched complement. *)
Definition stats_analyze_frame (p : Z) (st : list Z) : Assertion :=
  “ Zlength st = 11 ” &&
  (&( p # "stats_t" ->ₛ "starts")           # UInt64 |-> stats_starts st **
   &( p # "stats_t" ->ₛ "decisions")        # UInt64 |-> stats_decisions st **
   &( p # "stats_t" ->ₛ "propagations")     # UInt64 |-> stats_propagations st **
   &( p # "stats_t" ->ₛ "inspects")         # UInt64 |-> stats_inspects st **
   &( p # "stats_t" ->ₛ "conflicts")        # UInt64 |-> stats_conflicts st **
   &( p # "stats_t" ->ₛ "clauses")          # UInt64 |-> stats_clauses st **
   &( p # "stats_t" ->ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
   &( p # "stats_t" ->ₛ "learnts")          # UInt64 |-> stats_learnts st **
   &( p # "stats_t" ->ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st).

(** Embedded cells of the analyze frame, excluding its separately named
    watch/assignment payload and statistics. *)
Definition solver_analyze_frame_cells (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M **
  &( s # "solver_t" ->ₛ "var_decay") # Double |-> ms_var_decay M **
  &( s # "solver_t" ->ₛ "cla_decay") # Float |-> ms_cla_decay M **
  &( s # "solver_t" ->ₛ "random_seed") # Double |-> ms_random_seed M **
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M **
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) **
  &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M.

Definition solver_analyze_frame (s : Z) (M : msolver) (wl : Z) : Assertion :=
  solver_analyze_frame_cells s M **
  (EX asg : Z,
    &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
    &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
    solver_char_tail asg (ms_size M) (ms_cap M) **
    wlists_rep wl (ms_size M) (ms_wm M)) **
  stats_analyze_frame &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** Recombination frame used after resolution: [solver_removable_frame_at]
    with all resources except the named focus. *)
Definition solver_reason_levels_frame_at
    (s : Z) (M : msolver) (trl tags_ptr : Z) (wl : Z) : Assertion :=
    &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tags_ptr **
    CharArray.seg tags_ptr 0 (ms_size M) (ms_tags M) **
    solver_char_tail tags_ptr (ms_size M) (ms_cap M) **
    Veci.rep &( s # "solver_t" ->ₛ "tagged")
             (ms_tagged M) **
    Veci.rep &( s # "solver_t" ->ₛ "stack")
             (ms_stack M) **
    clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
    solver_removable_frame_at s M trl wl.

Definition stats_propagate_frame (p : Z) (st : list Z) : Assertion :=
  “ Zlength st = 11 ” &&
  (&( p # "stats_t" ->ₛ "starts")           # UInt64 |-> stats_starts st **
   &( p # "stats_t" ->ₛ "decisions")        # UInt64 |-> stats_decisions st **
   &( p # "stats_t" ->ₛ "conflicts")        # UInt64 |-> stats_conflicts st **
   &( p # "stats_t" ->ₛ "clauses")          # UInt64 |-> stats_clauses st **
   &( p # "stats_t" ->ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
   &( p # "stats_t" ->ₛ "learnts")          # UInt64 |-> stats_learnts st **
   &( p # "stats_t" ->ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st **
   &( p # "stats_t" ->ₛ "max_literals")     # UInt64 |-> stats_max_literals st **
   &( p # "stats_t" ->ₛ "tot_literals")     # UInt64 |-> stats_tot_literals st).

(** Remainder used while propagation has its queue, core arrays, watcher
    table, clause objects, binary scratch object, and two statistics counters
    physically open. *)
Definition solver_propagate_frame (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M **
  solver_fp_rep s M **
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) **
  (EX act opos tgs : Z,
    &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
    DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
    solver_double_tail act (ms_size M) (ms_cap M) **
    IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
    solver_int_tail opos (ms_size M) (ms_cap M) **
    CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
    solver_char_tail tgs (ms_size M) (ms_cap M)) **
  stats_propagate_frame &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** The binary scratch object is kept separate in propagation annotations:
    unlike a real database clause it is never a member of either DB vector,
    but the binary-conflict arm mutates its two literal cells in place. *)
Definition solver_binary_rep (M : msolver) : Assertion :=
  binary_scratch_rep (ms_binary M) (ms_binary_lits M).

(** Literal-array contents after propagation has made the currently false
    watched literal occupy slot 1.  Slots from index 2 onward are unchanged. *)
Definition propagation_normalized_clause
    (watch0 false_lit : Z) (old : list Z) : list Z :=
  watch0 :: false_lit :: sublist 2 (Zlength old) old.

Definition propagation_replacement_scan_inv
    (n : Z) (M : msolver) (false_lit : Z) (words : list Z) (k : Z)
    : Prop :=
  2 <= k <= Zlength words /\
  Forall (lit_wf_c n) words /\
  Znth 1 words 0 = false_lit /\
  lit_false (mt_assigns (ms_core M)) false_lit /\
  (forall j, 2 <= j < k ->
     lit_false (mt_assigns (ms_core M)) (Znth j words 0)).

(** A real clause pointer present in watcher list [p] watches the negation of
    [p] in one of its first two literal slots. *)
Definition real_watch_pair (p : Z) (lits : list Z) : Prop :=
  Znth 0 lits 0 = lit_neg_c p \/ Znth 1 lits 0 = lit_neg_c p.

Definition enqueue_transition
    (l from qtail ret qtail' : Z)
    (assigns levels reasons trail lim
     assigns' levels' reasons' trail' : list Z) : Prop :=
  let v := lit_var_c l in
  let sig := lit_sig l in
  ((Znth v assigns 0 = sig /\ ret = 1 /\
    assigns' = assigns /\ levels' = levels /\ reasons' = reasons /\
    trail' = trail /\ qtail' = qtail) \/
   (Znth v assigns 0 <> 0 /\ Znth v assigns 0 <> sig /\ ret = 0 /\
    assigns' = assigns /\ levels' = levels /\ reasons' = reasons /\
    trail' = trail /\ qtail' = qtail) \/
   (Znth v assigns 0 = 0 /\ ret = 1 /\
    assigns' = replace_Znth v sig assigns /\
    levels' = replace_Znth v (Zlength lim) levels /\
    reasons' = replace_Znth v from reasons /\
    trail' = trail ++ [l] /\ qtail' = qtail + 1)).

(** The exact spatial footprint of [enqueue]. *)
Definition enqueue_state_at
    (s asg lvl n cap qtail : Z)
    (assigns levels reasons trail lim : list Z) : Assertion :=
  EX rsn trl : Z,
    “ 0 <= n <= cap /\ cap <= INT_MAX /\
      Zlength assigns = n /\ Zlength levels = n /\
      Zlength reasons = n /\ Zlength trail = qtail /\
      0 <= qtail <= cap ” &&
    (&( s # "solver_t" ->ₛ "qtail") # Int |-> qtail **
     &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
     &( s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
     &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
     &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
     CharArray.seg asg 0 n assigns **
     solver_char_tail asg n cap **
     IntArray.seg lvl 0 n levels **
     solver_int_tail lvl n cap **
     PtrArray.seg rsn 0 n reasons **
     solver_ptr_tail rsn n cap **
     IntArray.seg trl 0 qtail trail **
     solver_int_tail trl qtail cap **
     Veci.rep &( s # "solver_t" ->ₛ "trail_lim") lim).

Definition enqueue_post_at
    (s asg lvl l reason n cap qtail ret : Z)
    (assigns levels reasons trail lim : list Z) : Assertion :=
  EX qtail' : Z, EX assigns' : list Z, EX levels' : list Z,
  EX reasons' : list Z, EX trail' : list Z,
    “ enqueue_transition l reason qtail ret qtail'
        assigns levels reasons trail lim
        assigns' levels' reasons' trail' ” &&
    enqueue_state_at s asg lvl n cap qtail'
      assigns' levels' reasons' trail' lim.

Definition assume_post_at
    (s asg lvl l n cap qtail : Z)
    (assigns levels reasons trail lim : list Z) : Assertion :=
  &( s # "solver_t" ->ₛ "qhead") # Int |-> qtail **
  enqueue_post_at s asg lvl l 0 n cap qtail 1
    assigns levels reasons trail (lim ++ [qtail]).

(** The pointer-exposed variant: the shape a body that has just loaded the
    eight cached pointers works against. *)
Definition solver_rep_at
    (s : Z) (M : msolver) (wl act asg opos rsn lvl trl tgs : Z) : Assertion :=
  “ solver_shape M ” &&
  (solver_nonlevel_rep_at s M wl act asg opos rsn trl tgs **
   solver_levels_slice_at s M lvl).


Definition solver_rep_analyze_at
    (s : Z) (M : msolver) (rsn lvl trl tgs : Z) (wl : Z) : Assertion :=
  EX act asg opos : Z,
    solver_rep_at s M wl act asg opos rsn lvl trl tgs.

Lemma solver_shape_wm_len : forall M,
  solver_shape M -> Zlength (ms_wm M) = 2 * ms_size M.
Proof. intros M H. unfold solver_shape in H. tauto. Qed.

(** Reason words encode either an even clause pointer or an odd tag
    [2*l+1]. This pure bridge uses the live database, so deleting a real
    reason's object affects validity. *)

Definition db_lookup (db : dbmap) (p : Z) (co : clause_obj) : Prop :=
  In (p, co) db.

Definition trail_lit_of (t : mtrail) (v : Z) : Z :=
  if Znth v (mt_assigns t) 0 =? -1 then 2 * v + 1 else 2 * v.

(** Binary-reason polarity: a tag stores the true propagator [p], while
    the justified clause is [q, lit_neg(p)]. The trail and variable recover
    the enqueued literal [q], which the tag alone cannot identify. *)
Definition reason_word_ok (t : mtrail) (v : Z) (db : dbmap) (w : Z)
                          (r : option clause) : Prop :=
  if w =? 0 then r = None
  else Znth v (mt_assigns t) 0 <> 0 /\
       if is_tag w
       then r = Some [lit_denote (trail_lit_of t v);
                      literal_neg (lit_denote (tag_lit w))]
       else exists co, db_lookup db w co /\ r = Some (denote_obj co).

Definition reasons_match (n : Z) (t : mtrail) (db : dbmap) (words : list Z)
                         (r : Z -> option clause) : Prop :=
  forall v, 0 <= v < n -> reason_word_ok t v db (Znth v words 0) (r v).

(** A transparent one-field carrier for applying the watcher-table address
    accessor inside the large propagation frame. *)
Definition solver_wlists_handle (s wl : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl.

(** * S9 -- solver invariants. *)

(** ** Ghost projections of the solver record. *)

(** The clause database the solver actually owns: problem clauses first, then
    learnt clauses.  [solver_reducedb] and [solver_simplify] shrink the two
    halves independently, so they stay separate in the record and are joined
    only here. *)
Definition msolver_db (M : msolver) : dbmap := ms_prob M ++ ms_learnt M.

Definition db_clauses (db : dbmap) : list clause :=
  map (fun e => denote_obj (snd e)) db.

Lemma db_clauses_in : forall db p co,
  In (p, co) db -> In (denote_obj co) (db_clauses db).
Proof.
  intros db p co Hin. unfold db_clauses.
  apply (in_map (fun e => denote_obj (snd e)) db (p, co)). exact Hin.
Qed.

Lemma db_clauses_in_inv : forall db c,
  In c (db_clauses db) -> exists p co, In (p, co) db /\ denote_obj co = c.
Proof.
  intros db c Hin. unfold db_clauses in Hin.
  apply in_map_iff in Hin. destruct Hin as [[p co] [Heq Hin]].
  exists p, co. split; [exact Hin | exact Heq].
Qed.

Definition msolver_clauses (M : msolver) : list clause :=
  db_clauses (msolver_db M).

Definition msolver_heap (M : msolver) : mheap :=
  {| mh_heap := ms_order M; mh_orderpos := ms_orderpos M |}.

Definition msolver_view (n : Z) (M : msolver) : cdcl_view :=
  view_of n (ms_core M) (ms_reason_of M) (msolver_clauses M).

(** ** Database matching (the two halves of DB-IMPLIED) and DB-COMPLETE. *)

Definition db_matches_cnf (F : cnf) (M : msolver) : Prop :=
  Forall (fun c => exists c0, In c0 F /\ Permutation c c0)
         (db_clauses (ms_prob M)).

Definition db_implied (F : cnf) (M : msolver) : Prop :=
  Forall (entails_clause F) (db_clauses (ms_learnt M)).

(** A clause is already satisfied by a root (level-0) assignment.  This is the
    removal certificate [solver_simplify] leaves behind: level-0 cells survive
    every [canceluntil], so the certificate is still valid at model time. *)
Definition root_satisfied (t : mtrail) (c : clause) : Prop :=
  exists l, In l c /\
    eval_partial_literal (mt_pv t) l = Some true /\
    Znth (literal_var l) (mt_levels t) 0 = 0.

(** DB-COMPLETE: nothing of [F] was lost.  A clause of [F] is either still
    represented in the problem database (up to permutation) or it was removed
    with a root-satisfaction certificate.  Unit clauses of [F] never enter the
    database at all ([clause_new] asserts size > 1); they enter as level-0
    trail facts, which is exactly the second arm. *)
Definition db_complete (F : cnf) (M : msolver) : Prop :=
  forall c, In c F ->
    (exists c', In c' (db_clauses (ms_prob M)) /\ Permutation c' c) \/
    root_satisfied (ms_core M) c.

(** lits[0] discipline: a clause object serving as a real reason
    keeps the implied literal in slot 0. *)
Definition reason_head_ok (M : msolver) : Prop :=
  forall v co,
    0 <= v < ms_size M ->
    is_tag (Znth v (ms_reason_words M) 0) = false ->
    Znth v (ms_reason_words M) 0 <> 0 ->
    In (Znth v (ms_reason_words M) 0, co) (msolver_db M) ->
    lit_var_c (co_watch0 co) = v.

(** A binary reason's partner has a well-formed literal, the same level,
    and a different variable. The literal bound is essential: neither the
    tagged codec nor total [Znth] level lookups establish it. Positivity
    follows from this bound and oddness via [tag_pos_of_lit_wf]. *)
Definition binary_reason_same_level (M : msolver) : Prop :=
  forall v,
    0 <= v < ms_size M ->
    is_tag (Znth v (ms_reason_words M) 0) = true ->
    lit_wf_c (ms_size M) (tag_lit (Znth v (ms_reason_words M) 0)) /\
    Znth (lit_var_c (tag_lit (Znth v (ms_reason_words M) 0)))
         (mt_levels (ms_core M)) 0
    = Znth v (mt_levels (ms_core M)) 0 /\
    lit_var_c (tag_lit (Znth v (ms_reason_words M) 0)) <> v.

(** The semantic invariant records only that the binary64 seed is finite.
    C-facing contracts separately carry [msolver_seed_shadow], an audited
    exact-integer shadow assumption.  It is not derived here from finiteness
    or from an unproved binary64 rounding claim. *)
Definition msolver_seed_ok (M : msolver) : Prop :=
  fp64_isFinite (ms_random_seed M).

(** Exact operational shadow required by the audited random facade. *)
Definition msolver_seed_shadow (M : msolver) : Prop :=
  exists z, ms_random_seed M = Z_to_fp64 z /\ seed_ok z.

(** At a stable query point, every caller assumption is true at or below
    [root_level], whether skipped as already true or installed as a decision.
    Cancellation at or above the root preserves these cells. *)
Definition assump_true_at_root (t : mtrail) (root : Z) (a : literal) : Prop :=
  eval_partial_literal (mt_pv t) a = Some true /\
  Znth (literal_var a) (mt_levels t) 0 <= root.

(** Stable analysis scratch: every tag cell is clear and the rollback index
    vector is empty.  The DFS stack is intentionally absent: a failed
    [solver_lit_removable] may leave entries there, and its next call clears
    the stack before reading it. *)
Definition solver_tags_clear (M : msolver) : Prop :=
  Forall (fun z => z = 0) (ms_tags M) /\ ms_tagged M = [].

(** ** The invariant bundle: the weak persistent core. *)

Record msolver_inv_weak (n : Z) (F : cnf) (A_arr A_inst : list literal)
                        (M : msolver) : Prop := {
  (* --- sizes, ranges, well-formed inputs --- *)
  msw_size        : n = ms_size M;
  msw_n_range     : 0 <= n;
  msw_shape       : solver_shape M;
  msw_F_wf        : cnf_wf n F;
  msw_A_wf        : Forall (literal_wf n) A_arr;
  (* --- the concrete trail (S4) --- *)
  msw_trail_wf    : mtrail_wf n (ms_core M);
  msw_level_bound : Zlength (mt_lim (ms_core M)) <= n;
  msw_root_range  : 0 <= ms_root_level M <= Zlength (mt_lim (ms_core M));
  (* --- assumptions: installed sub-list + array satisfaction --- *)
  msw_assumptions : decisions_upto (ms_core M) (ms_root_level M) = A_inst;
  msw_assump_incl : incl A_inst A_arr;
  msw_assump_sat  : Forall (assump_true_at_root (ms_core M) (ms_root_level M))
                           A_arr;
  (* --- the CDCL algebra --- *)
  msw_stable      : stable_view (msolver_view n M);
  msw_reasons_ent : reasons_entailed F (msolver_view n M);
  msw_reasons_inj : reasons_var_injective (msolver_view n M);
  (* --- TRAIL-IMPLIED (S4) --- *)
  msw_trail_impl  : trail_implied F (ms_core M);
  (* --- the clause database --- *)
  msw_db_wf       : db_wf n (msolver_db M);
  msw_db_matches  : db_matches_cnf F M;
  msw_db_implied  : db_implied F M;
  msw_db_complete : db_complete F M;
  msw_learnt_db   : learnt_db (ms_learnt M);
  msw_prob_db     : prob_db (ms_prob M);
  msw_binary_out  : ~ In (ms_binary M) (map fst (msolver_db M));
  (* --- reason words vs ghost reasons --- *)
  msw_reasons_mem : reasons_match n (ms_core M) (msolver_db M)
                                  (ms_reason_words M) (ms_reason_of M);
  msw_reason_head : reason_head_ok M;
  msw_reason_bin  : binary_reason_same_level M;
  (* --- watcher table exactness (S5) --- *)
  msw_wmap_exact  : wmap_exact n (msolver_db M) (ms_wm M);
  (* --- stable analysis scratch --- *)
  msw_tags_clear  : solver_tags_clear M;
  (* --- heuristics (S7) --- *)
  msw_heap_wf     : heap_wf n (msolver_heap M);
  msw_cla_inc_nonnegative : msat_fp32_nonnegative (ms_cla_inc M);
  msw_seed        : msolver_seed_ok M
}.

Arguments msw_size        {n F A_arr A_inst M} _.

Arguments msw_n_range     {n F A_arr A_inst M} _.

Arguments msw_shape       {n F A_arr A_inst M} _.

Arguments msw_F_wf        {n F A_arr A_inst M} _.

Arguments msw_A_wf        {n F A_arr A_inst M} _.

Arguments msw_trail_wf    {n F A_arr A_inst M} _.

Arguments msw_level_bound {n F A_arr A_inst M} _.

Arguments msw_root_range  {n F A_arr A_inst M} _.

Arguments msw_assumptions {n F A_arr A_inst M} _.

Arguments msw_assump_incl {n F A_arr A_inst M} _.

Arguments msw_assump_sat  {n F A_arr A_inst M} _.

Arguments msw_stable      {n F A_arr A_inst M} _.

Arguments msw_reasons_ent {n F A_arr A_inst M} _.

Arguments msw_reasons_inj {n F A_arr A_inst M} _.

Arguments msw_trail_impl  {n F A_arr A_inst M} _.

Arguments msw_db_wf       {n F A_arr A_inst M} _.

Arguments msw_db_matches  {n F A_arr A_inst M} _.

Arguments msw_db_implied  {n F A_arr A_inst M} _.

Arguments msw_db_complete {n F A_arr A_inst M} _.

Arguments msw_learnt_db   {n F A_arr A_inst M} _.

Arguments msw_prob_db     {n F A_arr A_inst M} _.

Arguments msw_binary_out  {n F A_arr A_inst M} _.

Arguments msw_reasons_mem {n F A_arr A_inst M} _.

Arguments msw_reason_head {n F A_arr A_inst M} _.

Arguments msw_reason_bin  {n F A_arr A_inst M} _.

Arguments msw_wmap_exact  {n F A_arr A_inst M} _.

Arguments msw_tags_clear  {n F A_arr A_inst M} _.

Arguments msw_heap_wf     {n F A_arr A_inst M} _.

Arguments msw_cla_inc_nonnegative {n F A_arr A_inst M} _.

Arguments msw_seed        {n F A_arr A_inst M} _.

(** At every non-root decision level, a reasonless variable is exactly that
    level's decision-boundary cell.  Quantifying all surviving levels is
    essential for non-chronological backjumping: cancellation can make an old
    level current, so a current-level-only fact is not inductive.  Root units
    remain outside the discipline. *)
Definition current_reasonless_earliest (n : Z) (M : msolver) : Prop :=
  forall d,
  ms_root_level M < d <= Zlength (mt_lim (ms_core M)) ->
  forall v,
    level_of (msolver_view n M) v = Some d ->
    Znth v (ms_reason_words M) 0 = 0 ->
    ms_reason_of M v = None /\
    assignment_rank (msolver_view n M) v =
      Some (Z.to_nat (Znth (d - 1) (mt_lim (ms_core M)) 0)).

(** ** ...and the strong stable-point bundle. *)

Record msolver_inv (n : Z) (F : cnf) (A_arr A_inst : list literal)
                   (M : msolver) : Prop := {
  msi_weak        : msolver_inv_weak n F A_arr A_inst M;
  msi_prop_level  : prop_level (ms_core M);
  msi_watch_frontier : minisat_watch_frontier n (msolver_db M)
                                (mt_assigns (ms_core M))
                                (mt_trail (ms_core M))
                                (mt_qhead (ms_core M));
  msi_heap_covers : heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
                                (mt_trail (ms_core M)) (mt_qhead (ms_core M));
  msi_reasonless_current : current_reasonless_earliest n M
}.

Arguments msi_weak        {n F A_arr A_inst M} _.

Arguments msi_prop_level  {n F A_arr A_inst M} _.

Arguments msi_watch_frontier {n F A_arr A_inst M} _.

Arguments msi_heap_covers {n F A_arr A_inst M} _.

Arguments msi_reasonless_current {n F A_arr A_inst M} _.

Definition solver_at_root (M : msolver) : Prop :=
  Zlength (mt_lim (ms_core M)) = ms_root_level M.

(** ** Mid-assumption-loop invariant.
    The stored root stays stale while decision levels grow. This bundle
    indexes assumptions by the current level and processed prefix [A_proc],
    excluding the cursor and unvisited tail. It supports both false-cursor
    and propagation-conflict failures over the full caller array. *)

Record msolver_inv_assuming (n : Z) (F : cnf) (A_arr A_proc : list literal)
                            (M : msolver) : Prop := {
  msa_size        : n = ms_size M;
  msa_n_range     : 0 <= n;
  msa_shape       : solver_shape M;
  msa_F_wf        : cnf_wf n F;
  msa_A_wf        : Forall (literal_wf n) A_arr;
  msa_trail_wf    : mtrail_wf n (ms_core M);
  msa_level_bound : Zlength (mt_lim (ms_core M)) <= n;
  msa_decisions   : exists A_inst,
                      decisions_upto (ms_core M) (Zlength (mt_lim (ms_core M)))
                        = A_inst /\ incl A_inst A_proc;
  msa_proc_incl   : incl A_proc A_arr;
  msa_proc_sat    : Forall (assump_true_at_root (ms_core M)
                              (Zlength (mt_lim (ms_core M)))) A_proc;
  msa_stable      : stable_view (msolver_view n M);
  msa_reasons_ent : reasons_entailed F (msolver_view n M);
  msa_reasons_inj : reasons_var_injective (msolver_view n M);
  msa_trail_impl  : trail_implied F (ms_core M);
  msa_db_wf       : db_wf n (msolver_db M);
  msa_db_matches  : db_matches_cnf F M;
  msa_db_implied  : db_implied F M;
  msa_db_complete : db_complete F M;
  msa_learnt_db   : learnt_db (ms_learnt M);
  msa_prob_db     : prob_db (ms_prob M);
  msa_binary_out  : ~ In (ms_binary M) (map fst (msolver_db M));
  msa_reasons_mem : reasons_match n (ms_core M) (msolver_db M)
                                  (ms_reason_words M) (ms_reason_of M);
  msa_reason_head : reason_head_ok M;
  msa_reason_bin  : binary_reason_same_level M;
  msa_wmap_exact  : wmap_exact n (msolver_db M) (ms_wm M);
  msa_tags_clear  : solver_tags_clear M;
  msa_heap_wf     : heap_wf n (msolver_heap M);
  msa_cla_inc_nonnegative : msat_fp32_nonnegative (ms_cla_inc M);
  msa_seed        : msolver_seed_ok M
}.

Arguments msa_size        {n F A_arr A_proc M} _.

Arguments msa_n_range     {n F A_arr A_proc M} _.

Arguments msa_shape       {n F A_arr A_proc M} _.

Arguments msa_F_wf        {n F A_arr A_proc M} _.

Arguments msa_A_wf        {n F A_arr A_proc M} _.

Arguments msa_trail_wf    {n F A_arr A_proc M} _.

Arguments msa_level_bound {n F A_arr A_proc M} _.

Arguments msa_decisions   {n F A_arr A_proc M} _.

Arguments msa_proc_incl   {n F A_arr A_proc M} _.

Arguments msa_proc_sat    {n F A_arr A_proc M} _.

Arguments msa_stable      {n F A_arr A_proc M} _.

Arguments msa_reasons_ent {n F A_arr A_proc M} _.

Arguments msa_reasons_inj {n F A_arr A_proc M} _.

Arguments msa_trail_impl  {n F A_arr A_proc M} _.

Arguments msa_db_wf       {n F A_arr A_proc M} _.

Arguments msa_db_matches  {n F A_arr A_proc M} _.

Arguments msa_db_implied  {n F A_arr A_proc M} _.

Arguments msa_db_complete {n F A_arr A_proc M} _.

Arguments msa_learnt_db   {n F A_arr A_proc M} _.

Arguments msa_prob_db     {n F A_arr A_proc M} _.

Arguments msa_binary_out  {n F A_arr A_proc M} _.

Arguments msa_reasons_mem {n F A_arr A_proc M} _.

Arguments msa_reason_head {n F A_arr A_proc M} _.

Arguments msa_reason_bin  {n F A_arr A_proc M} _.

Arguments msa_wmap_exact  {n F A_arr A_proc M} _.

Arguments msa_tags_clear  {n F A_arr A_proc M} _.

Arguments msa_heap_wf     {n F A_arr A_proc M} _.

Arguments msa_cla_inc_nonnegative {n F A_arr A_proc M} _.

Arguments msa_seed        {n F A_arr A_proc M} _.

(** A propagation call is used either at an ordinary stable point or while
    [solver_solve] is extending the processed assumptions prefix. *)
Inductive solver_propagation_context : Type :=
| PropagationStable (A_inst : list literal)
| PropagationAssuming (A_proc : list literal).

(** The first queued decision may be absent from the heap. A successful
     dequeue restores coverage. *)
Definition propagation_heap_ready (n : Z) (M : msolver) : Prop :=
  heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) \/
  (0 < Zlength (mt_lim (ms_core M)) /\
   mt_qhead (ms_core M) < ms_qtail M /\
   heap_covers_except n (msolver_heap M) (mt_assigns (ms_core M))
     (mt_trail (ms_core M)) (mt_qhead (ms_core M))
     (lit_var_c (Znth (mt_qhead (ms_core M))
                       (mt_trail (ms_core M)) 0))).


Definition propagation_heap_rollback_ready (M : msolver) (p : Z) : Prop :=
  0 < mt_qhead (ms_core M) /\
  p = Znth (mt_qhead (ms_core M) - 1)
           (mt_trail (ms_core M)) 0 /\
  (0 < Zlength (mt_lim (ms_core M)) \/
   Znth (lit_var_c p) (ms_orderpos M) (-1) <> -1).

Record msolver_inv_propagation
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (M : msolver) : Prop := {
  msp_weak        : msolver_inv_weak n F A_arr A_inst M;
  msp_prop_level  : prop_level (ms_core M);
  msp_watch_frontier : minisat_watch_frontier n (msolver_db M)
                                (mt_assigns (ms_core M))
                                (mt_trail (ms_core M))
                                (mt_qhead (ms_core M));
  msp_heap_ready  : propagation_heap_ready n M;
  msp_reasonless_current : current_reasonless_earliest n M
}.

Record msolver_inv_assuming_propagation
    (n : Z) (F : cnf) (A_arr A_proc : list literal)
    (M : msolver) : Prop := {
  msap_weak        : msolver_inv_assuming n F A_arr A_proc M;
  msap_prop_level  : prop_level (ms_core M);
  msap_watch_frontier : minisat_watch_frontier n (msolver_db M)
                                 (mt_assigns (ms_core M))
                                 (mt_trail (ms_core M))
                                 (mt_qhead (ms_core M));
  msap_heap_ready  : propagation_heap_ready n M;
  msap_reasonless_current : current_reasonless_earliest n M
}.

Arguments msp_reasonless_current {n F A_arr A_inst M} _.

Arguments msap_reasonless_current {n F A_arr A_proc M} _.

Definition solver_propagation_inv
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) : Prop :=
  ms_capacity_root_propagation_pending M = 0 /\
  match K with
  | PropagationStable A_inst =>
      msolver_inv_propagation n F A_arr A_inst M
  | PropagationAssuming A_proc =>
      msolver_inv_assuming_propagation n F A_arr A_proc M
  end.

Definition solver_propagation_weak
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) : Prop :=
  ms_capacity_root_propagation_pending M = 0 /\
  match K with
  | PropagationStable A_inst => msolver_inv_weak n F A_arr A_inst M
  | PropagationAssuming A_proc => msolver_inv_assuming n F A_arr A_proc M
  end.

(** Conflict return strength needed by analysis and a subsequent backjump.
    A weak semantic bundle alone cannot recover the strong invariant: the
    cancellation proof also consumes propagation-level boundaries, the exact
    watcher frontier, and full heap coverage. *)
Definition propagation_cancel_ready
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (focus : Z) : Prop :=
  solver_propagation_weak n F A_arr K M /\
  prop_level (ms_core M) /\
  lit_wf_c n focus /\
  processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
            (mt_qhead (ms_core M)) focus /\
  level_of (msolver_view n M) (lit_var_c focus) =
    Some (Zlength (mt_lim (ms_core M))) /\
  minisat_watch_frontier_except n (msolver_db M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M))
    (mt_qhead (ms_core M)) (lit_denote focus) /\
  heap_wf n (msolver_heap M) /\
  heap_covers n (msolver_heap M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M))
    (mt_qhead (ms_core M)) /\
  current_reasonless_earliest n M.

(** The semantic content of either a real or temporary-binary propagation
    conflict. *)
Definition propagation_conflict_cert
    (n : Z) (F : cnf) (M : msolver) (C : clause) : Prop :=
  entails_clause F C /\
  clause_false (assigns_pv (mt_assigns (ms_core M))) C /\
  Forall (literal_wf n) C /\
  NoDup (map literal_var C) /\
  exists l, In l C /\
    level_of (msolver_view n M) (literal_var l) =
      Some (Zlength (mt_lim (ms_core M))).

Definition conflict_ptr_denotes (M : msolver) (p : Z) (C : clause) : Prop :=
  (p = ms_binary M /\ C = lits_denote (ms_binary_lits M) /\
   ~ In p (map fst (msolver_db M)) /\ ms_binary_lits M <> []) \/
  exists co, p <> ms_binary M /\
    In (p, co) (msolver_db M) /\ C = denote_obj co.

(** Propagation preserves decision boundaries, the root marker, the model
    vector, clause decay and variable capacity. *)
Definition propagation_caller_frame
    (entry current : msolver) : Prop :=
  mt_lim (ms_core current) = mt_lim (ms_core entry) /\
  ms_root_level current = ms_root_level entry /\
  ms_model current = ms_model entry /\
  ms_cla_decay current = ms_cla_decay entry /\
  ms_cap current = ms_cap entry.

(** Physical progress of the open source watcher array.  [kept] is the
    compacted prefix already written at [j], [moved] records words installed
    in other watcher lists, [rest] begins at [i], and [garbage] is the raw
    in-array gap left by moved words. *)
Definition propagation_watch_scan_physical
    (source kept moved rest garbage memory : list Z)
    (ii jj : Z) : Prop :=
  wlist_scan_inv source kept moved rest /\
  memory = kept ++ garbage ++ rest /\
  Zlength kept = jj /\
  Zlength (kept ++ garbage) = ii /\
  Zlength memory = Zlength source.

(** Queue-frontier facts that remain stable while successful unit enqueues
    may extend the trail behind the already advanced [qhead]. *)
Definition propagation_scan_frontier
    (entry current : msolver) (p : Z) : Prop :=
  mt_qhead (ms_core current) = mt_qhead (ms_core entry) + 1 /\
  p = Znth (mt_qhead (ms_core entry))
           (mt_trail (ms_core entry)) 0 /\
  ms_qtail entry <= ms_qtail current /\
  sublist 0 (ms_qtail entry) (mt_trail (ms_core current)) =
    mt_trail (ms_core entry) /\
  propagation_heap_rollback_ready current p.

(** The live scan retains weak semantics, propagation facts, and an
    occurrence-indexed frontier at [lit_denote p]. Occurrence identity
    distinguishes equal tags from different binary clauses. The conflict
    arm has consumed the source suffix and carries its conflict certificate. *)
Definition solver_propagation_scan_semantics
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p confl : Z) (kept rest : list Z) : Prop :=
  (confl = 0 /\
   solver_propagation_weak n F A_arr K M /\
   prop_level (ms_core M) /\
   propagation_heap_ready n M /\
   heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
     (mt_trail (ms_core M)) (mt_qhead (ms_core M)) /\
   current_reasonless_earliest n M /\
   level_of (msolver_view n M) (lit_var_c p) =
     Some (Zlength (mt_lim (ms_core M))) /\
   lit_wf_c n p /\
   processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
             (mt_qhead (ms_core M)) p /\
   minisat_watch_frontier_except
     n (msolver_db M)
     (mt_assigns (ms_core M)) (mt_trail (ms_core M))
     (mt_qhead (ms_core M)) (lit_denote p) /\
   minisat_focus_scan_carrier
     (msolver_db M) p
     (minisat_processed n
       (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)))
     kept rest) \/
  (confl <> 0 /\ rest = nil /\
   propagation_cancel_ready n F A_arr K M p /\
   exists C, propagation_conflict_cert n F M C /\
     conflict_ptr_denotes M confl C).

(** ** The spatial contract vocabulary. *)


(** The two statistics counters the watcher scan mutates; every other stats
    field stays inside [stats_propagate_frame]. *)
Definition stats_propagate_scan (q prop insp : Z) : Assertion :=
  &( q # "stats_t" ->ₛ "propagations") # UInt64 |-> prop **
  &( q # "stats_t" ->ₛ "inspects") # UInt64 |-> insp.

Definition solver_propagation_scan_core_at
    (s : Z) (M : msolver) (asg rsn lvl trl simp prop : Z) : Assertion :=
  PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
  solver_ptr_tail rsn (ms_size M) (ms_cap M) **
  IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
  solver_int_tail lvl (ms_size M) (ms_cap M) **
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  solver_int_tail trl (ms_qtail M) (ms_cap M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> simp **
  &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
  solver_binary_rep M **
  stats_propagate_scan &( s # "solver_t" ->ₛ "stats")
                       prop (stats_inspects (ms_stats M)) **
  solver_propagate_frame s M.

Definition solver_selected_db (type : Z) (M : msolver) : dbmap :=
  if Z.eqb type 0 then ms_prob M else ms_learnt M.

Definition solver_selected_vec (s type : Z) : Z :=
  if Z.eqb type 0
  then &( s # "solver_t" ->ₛ "clauses")
  else &( s # "solver_t" ->ₛ "learnts").

Definition solver_selected_is_learnt (type : Z) : bool :=
  negb (Z.eqb type 0).

Definition solver_other_db_vec_rep
    (s type : Z) (M : msolver) : Assertion :=
  if Z.eqb type 0 then
    Vecp.rep &( s # "solver_t" ->ₛ "learnts")
      (map fst (ms_learnt M))
  else
    Vecp.rep &( s # "solver_t" ->ₛ "clauses")
      (map fst (ms_prob M)).

Definition solver_other_clause_db_rep
    (type : Z) (M : msolver) : Assertion :=
  if Z.eqb type 0
  then clause_db_rep (ms_learnt M)
  else clause_db_rep (ms_prob M).

(** Complement used while the current selected clause, the live assignment
    prefix, and the empty decision-level vector are exposed to
    [clause_simplify]. *)
Definition solver_simplify_clause_frame_at
    (s type : Z) (M : msolver) (asg lvl : Z) : Assertion :=
  clause_new_scalars_frame s M ** solver_fp_rep s M **
  solver_other_db_vec_rep s type M **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
    (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
    (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
    (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
    (ms_model M) **
  (EX act opos trl tgs : Z,
    &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
    &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
    DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
    solver_double_tail act (ms_size M) (ms_cap M) **
    solver_char_tail asg (ms_size M) (ms_cap M) **
    IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
    solver_int_tail opos (ms_size M) (ms_cap M) **
    IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
    solver_int_tail trl (ms_qtail M) (ms_cap M) **
    CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
    solver_char_tail tgs (ms_size M) (ms_cap M)) **
  solver_levels_slice_at s M lvl **
  solver_other_clause_db_rep type M **
  binary_scratch_rep (ms_binary M) (ms_binary_lits M).

Definition solver_simplify_db_rest_at
    (s type : Z) (M : msolver) (reasons lvl wl asg : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  solver_wlists_handle s wl **
  wlists_rep wl (ms_size M) (ms_wm M) **
  &( s # "solver_t" ->ₛ "reasons") # Ptr |-> reasons **
  PtrArray.seg reasons 0 (ms_size M) (ms_reason_words M) **
  solver_ptr_tail reasons (ms_size M) (ms_cap M) **
  stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M) **
  solver_simplify_clause_frame_at s type M asg lvl.


(** Recording uses the post-backjump asserting-clause certificate: the
    head is unassigned and the tail false in the new view. *)
Definition record_ready_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) : Prop :=
  1 <= Zlength words /\ Forall (lit_wf_c n) words /\
  NoDup (map lit_var_c words) /\
  entails_clause F (lits_denote words) /\
  Znth (lit_var_c (Znth 0 words 0)) (mt_assigns (ms_core M)) 0 = 0 /\
  clause_false (mt_pv (ms_core M)) (tl (lits_denote words)) /\
  (Zlength words = 1 -> solver_at_root M).

Definition record_clause_cert := record_ready_cert.

Definition clause_allocator_fresh (M : msolver) (c : Z) : Prop :=
  0 < c /\ Z.even c = true /\ c <> ms_binary M /\
  ~ In c (map fst (msolver_db M)).

(** * Clause installation.
    The flag selects the learned or problem database. Problem installation
    extends [F] and inserts before the learned half of [msolver_db], so its
    algebra uses formula monotonicity and a database permutation bridge. *)

Definition clause_obj_of (words : list Z) (learnt : bool) : clause_obj :=
  {| co_lits := words; co_learnt := learnt |}.

Definition msolver_install_clause
    (M : msolver) (c : Z) (words : list Z) (learnt : bool) : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    (if learnt then ms_prob M
     else ms_prob M ++ [(c, clause_obj_of words false)])
    (if learnt then ms_learnt M ++ [(c, clause_obj_of words true)]
     else ms_learnt M)
    (ms_binary_lits M) (clause_new_watch_map M c words) (ms_stats M).

Lemma msolver_install_learnt_clause_gen : forall M c words,
  msolver_install_learnt_clause M c words =
  msolver_install_clause M c words true.
Proof. reflexivity. Qed.

Lemma ms_wm_install : forall M c words b,
  ms_wm (msolver_install_clause M c words b) = clause_new_watch_map M c words.
Proof. reflexivity. Qed.

Lemma clause_new_watch_map_Zlength : forall M c words,
  Zlength (clause_new_watch_map M c words) = Zlength (ms_wm M).
Proof.
  intros. unfold clause_new_watch_map, wmap_push_word.
  rewrite !Zlength_replace_Znth. reflexivity.
Qed.

Lemma clause_new_watch_map_Znth : forall M c words l,
  0 <= lit_neg_c (Znth 0 words 0) < Zlength (ms_wm M) ->
  0 <= lit_neg_c (Znth 1 words 0) < Zlength (ms_wm M) ->
  lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
  0 <= l < Zlength (ms_wm M) ->
  Znth l (clause_new_watch_map M c words) [] =
  (if lit_neg_c (Znth 0 words 0) =? l
   then Znth l (ms_wm M) [] ++ [clause_watch_word c words (Znth 1 words 0)]
   else if lit_neg_c (Znth 1 words 0) =? l
        then Znth l (ms_wm M) [] ++ [clause_watch_word c words (Znth 0 words 0)]
        else Znth l (ms_wm M) []).
Proof.
  intros M c words l H0 H1 Hne Hl.
  unfold clause_new_watch_map, wmap_push_word.
  set (i0 := lit_neg_c (Znth 0 words 0)) in *.
  set (i1 := lit_neg_c (Znth 1 words 0)) in *.
  set (wm := ms_wm M) in *.
  set (w0 := clause_watch_word c words (Znth 1 words 0)).
  set (w1 := clause_watch_word c words (Znth 0 words 0)).
  set (wm0 := replace_Znth i0 (Znth i0 wm [] ++ [w0]) wm).
  assert (Hlen0 : Zlength wm0 = Zlength wm)
    by (unfold wm0; apply Zlength_replace_Znth).
  assert (Hi1 : Znth i1 wm0 [] = Znth i1 wm []).
  { unfold wm0. apply Znth_replace_Znth_Diff; [lia | lia | congruence]. }
  rewrite Hi1.
  destruct (i0 =? l) eqn:E0.
  - apply Z.eqb_eq in E0. subst l.
    assert (E1 : i1 <> i0) by congruence.
    rewrite Znth_replace_Znth_Diff; [| lia | lia | congruence].
    unfold wm0. rewrite Znth_replace_Znth_Same by lia. reflexivity.
  - destruct (i1 =? l) eqn:E1.
    + apply Z.eqb_eq in E1. subst l.
      rewrite Znth_replace_Znth_Same by lia. reflexivity.
    + assert (Hl0 : i0 <> l) by (apply Z.eqb_neq; exact E0).
      assert (Hl1 : i1 <> l) by (apply Z.eqb_neq; exact E1).
      rewrite Znth_replace_Znth_Diff; [| lia | lia | congruence].
      unfold wm0. rewrite Znth_replace_Znth_Diff; [reflexivity | lia | lia | congruence].
Qed.

Lemma solver_shape_install : forall M c words b,
  solver_shape M -> solver_shape (msolver_install_clause M c words b).
Proof.
  intros M c words b H. unfold solver_shape in *.
  rewrite ms_wm_install. rewrite clause_new_watch_map_Zlength.
  exact H.
Qed.

Lemma Forall_of_perm : forall (A : Type) (P : A -> Prop) l l',
  Permutation l l' -> Forall P l -> Forall P l'.
Proof.
  intros A P l l' Hperm H. rewrite Forall_forall in *.
  intros x Hx. apply H.
  eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
Qed.

(** Problem-clause insertion keeps only unassigned literals. Its
    certificate differs from recording's unassigned head and false tail. *)
Definition problem_clause_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) : Prop :=
  2 <= Zlength words /\ Forall (lit_wf_c n) words /\
  NoDup (map lit_var_c words) /\
  In (lits_denote words) F /\
  Forall (fun l => Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0) words.

Definition clause_install_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) (learnt : bool) : Prop :=
  if learnt then record_clause_cert n F M words
            else problem_clause_cert n F M words.

Definition clause_new_success_transition
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (c : Z) (M' : msolver) : Prop :=
  clause_allocator_fresh entry c /\
    M' = msolver_install_learnt_clause entry c words /\
    msolver_inv n F A_arr A_inst M' /\
    ms_capacity_root_propagation_pending M' = 0 /\
    msolver_seed_shadow M' /\
    record_clause_cert n F M' words.

(** ** Exact seed shadow.
    C-facing random contracts require a [Z_to_fp64] image with [seed_ok],
    beyond semantic seed finiteness. Constructor-level zero has no such
    shadow. [w0s] uses MiniSat's default seed [91648253].
    Statements mentioning [Z_to_fp64] depend on Coq's real-number
    axioms even for reflexive equalities; the float proofs stay in
    [MSatFloatFacts]. *)

Module MSatFloatFacts.
Import Coq.Reals.Reals.
Import SpecFloat.
Import Flocq.Core.Core.
Import Flocq.IEEE754.BinarySingleNaN.
Import Flocq.IEEE754.Binary.
Local Open Scope R_scope.

Lemma fp32_finite_not_nan : forall x,
  Binary.is_finite 24 128 x = true ->
  Binary.is_nan 24 128 x = false.
Proof. intros [s | s | s p Hp | s m e Hm]; simpl; congruence. Qed.

Lemma fp32_nonnegative_eq_refl : forall x,
  msat_fp32_nonnegative x -> fp32_eq x x.
Proof.
  intros x Hx. unfold fp32_eq, fp32_compare.
  destruct x as [s | s | s p Hp | s m e Hm];
    destruct s; simpl in Hx |- *; try contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite Binary.Bcompare_correct by reflexivity.
    rewrite Flocq.Core.Raux.Rcompare_Eq; reflexivity.
Qed.

Lemma fp32_finite_sign_nonnegative : forall x,
  Binary.is_finite 24 128 x = true ->
  Binary.Bsign 24 128 x = false ->
  msat_fp32_nonnegative x.
Proof.
  intros [s | s | s p Hp | s m e Hm] Hfin Hsign;
    simpl in Hfin, Hsign |- *; try discriminate; subst s; exact I.
Qed.

Lemma fp32_positive_finite_B2R_nonzero : forall x,
  msat_fp32_positive_finite x -> Binary.B2R 24 128 x <> 0%R.
Proof.
  intros [s | s | s p Hp | s m e Hm] [Hfin [Hsign Hnz]];
    simpl in Hfin, Hsign, Hnz; try discriminate; subst s.
  - intro Heq. apply Hnz. reflexivity.
  - apply Rgt_not_eq.
    change (0 < F2R (Float radix2 (Z.pos m) e))%R.
    apply F2R_gt_0. apply Pos2Z.is_pos.
Qed.

Lemma fp32_nonnegative_finite_B2R_nonnegative : forall x,
  msat_fp32_nonnegative x -> Binary.is_finite 24 128 x = true ->
  (0 <= Binary.B2R 24 128 x)%R.
Proof.
  intros [s | s | s p Hp | s m e Hm] Hx Hfin;
    destruct s; simpl in Hx, Hfin |- *; try contradiction; try discriminate.
  - lra.
  - lra.
  - left. apply F2R_gt_0. apply Pos2Z.is_pos.
Qed.

Lemma fp32_positive_overflow_nonnegative : forall x,
  Binary.B2FF 24 128 x = Binary.binary_overflow 24 128 mode_NE false ->
  msat_fp32_nonnegative x.
Proof.
  intros [s | s | s p Hp | s m e Hm] H;
    unfold Binary.binary_overflow,
      BinarySingleNaN.binary_overflow,
      BinarySingleNaN.overflow_to_inf in H;
    simpl in H; try discriminate; inversion H; subst s; exact I.
Qed.

Lemma fp32_nonnegative_add_finite : forall x y,
  msat_fp32_nonnegative x -> msat_fp32_nonnegative y ->
  Binary.is_finite 24 128 x = true ->
  Binary.is_finite 24 128 y = true ->
  Binary.Bsign 24 128 x = false ->
  Binary.Bsign 24 128 y = false ->
  msat_fp32_nonnegative (fp32_add x y).
Proof.
  intros x y Hx Hy Hfx Hfy Hsx Hsy.
  pose proof (Binary.Bplus_correct 24 128 eq_refl eq_refl
                fp32_binary_nan mode_NE x y Hfx Hfy) as HC.
  destruct (Rlt_bool
    (Rabs (round radix2 (SpecFloat.fexp 24 128)
             (round_mode mode_NE)
             (Binary.B2R 24 128 x + Binary.B2R 24 128 y)))
    (bpow radix2 128)) eqn:HR.
  - destruct HC as [_ [Hfin Hsign]].
    apply fp32_finite_sign_nonnegative; [exact Hfin|].
    unfold fp32_add. rewrite Hsign.
    pose proof (fp32_nonnegative_finite_B2R_nonnegative x Hx Hfx) as Hxr.
    pose proof (fp32_nonnegative_finite_B2R_nonnegative y Hy Hfy) as Hyr.
    case (Flocq.Core.Raux.Rcompare_spec
            (Binary.B2R 24 128 x + Binary.B2R 24 128 y) 0);
      intro Hcmp; simpl.
    + exfalso. lra.
    + rewrite Hsx, Hsy. reflexivity.
    + reflexivity.
  - destruct HC as [Hover Hsame].
    apply fp32_positive_overflow_nonnegative.
    rewrite Hsx in Hover. exact Hover.
Qed.

Lemma fp32_nonnegative_add : forall x y,
  msat_fp32_nonnegative x -> msat_fp32_nonnegative y ->
  msat_fp32_nonnegative (fp32_add x y).
Proof.
  intros x y Hx Hy.
  destruct x as [sx | sx | sx px Hpx | sx mx ex Hmx];
    destruct y as [sy | sy | sy py Hpy | sy my ey Hmy];
    destruct sx; destruct sy;
    simpl in Hx, Hy; try contradiction;
    try (eapply fp32_nonnegative_add_finite;
         [exact Hx | exact Hy | reflexivity | reflexivity |
          reflexivity | reflexivity]);
    unfold fp32_add; simpl; exact I.
Qed.

Lemma fp32_nonnegative_mul_finite : forall x y,
  msat_fp32_nonnegative x -> msat_fp32_positive_finite y ->
  Binary.is_finite 24 128 x = true ->
  Binary.Bsign 24 128 x = false ->
  msat_fp32_nonnegative (fp32_mul x y).
Proof.
  intros x y Hx Hy Hfx Hsx.
  destruct Hy as [Hfy [Hsy Hynz]].
  pose proof (Binary.Bmult_correct 24 128 eq_refl eq_refl
                fp32_binary_nan mode_NE x y) as HC.
  destruct (Rlt_bool
    (Rabs (round radix2 (SpecFloat.fexp 24 128)
             (round_mode mode_NE)
             (Binary.B2R 24 128 x * Binary.B2R 24 128 y)))
    (bpow radix2 128)) eqn:HR.
  - destruct HC as [_ [Hfin Hsign]].
    apply fp32_finite_sign_nonnegative.
    + unfold fp32_mul. now rewrite Hfin, Hfx, Hfy.
    + assert (Hnan : Binary.is_nan 24 128 (fp32_mul x y) = false).
      { apply fp32_finite_not_nan. unfold fp32_mul.
        now rewrite Hfin, Hfx, Hfy. }
      unfold fp32_mul in Hnan |- *.
      rewrite (Hsign Hnan), Hsx, Hsy. reflexivity.
  - apply fp32_positive_overflow_nonnegative.
    rewrite Hsx, Hsy in HC. exact HC.
Qed.

Lemma fp32_nonnegative_mul_positive_finite : forall x y,
  msat_fp32_nonnegative x -> msat_fp32_positive_finite y ->
  msat_fp32_nonnegative (fp32_mul x y).
Proof.
  intros x y Hx Hy.
  destruct x as [sx | sx | sx px Hpx | sx mx ex Hmx];
    destruct sx; simpl in Hx; try contradiction;
    try (eapply fp32_nonnegative_mul_finite;
         [exact Hx | exact Hy | reflexivity | reflexivity]).
  all: destruct y as [sy | sy | sy py Hpy | sy my ey Hmy];
    unfold msat_fp32_positive_finite in Hy;
    destruct Hy as [Hfy [Hsy Hynz]];
    simpl in Hfy, Hsy, Hynz; try discriminate; subst sy;
    try (contradiction Hynz; reflexivity);
    unfold fp32_mul; simpl; exact I.
Qed.

Lemma fp32_nonnegative_div_finite : forall x y,
  msat_fp32_nonnegative x -> msat_fp32_positive_finite y ->
  Binary.is_finite 24 128 x = true ->
  Binary.Bsign 24 128 x = false ->
  msat_fp32_nonnegative (fp32_div x y).
Proof.
  intros x y Hx Hy Hfx Hsx.
  pose proof (fp32_positive_finite_B2R_nonzero y Hy) as HyR.
  destruct Hy as [Hfy [Hsy Hynz]].
  pose proof (Binary.Bdiv_correct 24 128 eq_refl eq_refl
                fp32_binary_nan mode_NE x y HyR) as HC.
  destruct (Rlt_bool
    (Rabs (round radix2 (SpecFloat.fexp 24 128)
             (round_mode mode_NE)
             (Binary.B2R 24 128 x / Binary.B2R 24 128 y)))
    (bpow radix2 128)) eqn:HR.
  - destruct HC as [_ [Hfin Hsign]].
    apply fp32_finite_sign_nonnegative.
    + unfold fp32_div. now rewrite Hfin, Hfx.
    + assert (Hnan : Binary.is_nan 24 128 (fp32_div x y) = false).
      { apply fp32_finite_not_nan. unfold fp32_div. now rewrite Hfin, Hfx. }
      unfold fp32_div in Hnan |- *.
      rewrite (Hsign Hnan), Hsx, Hsy. reflexivity.
  - apply fp32_positive_overflow_nonnegative.
    rewrite Hsx, Hsy in HC. exact HC.
Qed.

Lemma fp32_nonnegative_div_positive_finite : forall x y,
  msat_fp32_nonnegative x -> msat_fp32_positive_finite y ->
  msat_fp32_nonnegative (fp32_div x y).
Proof.
  intros x y Hx Hy.
  destruct x as [sx | sx | sx px Hpx | sx mx ex Hmx];
    destruct sx; simpl in Hx; try contradiction;
    try (eapply fp32_nonnegative_div_finite;
         [exact Hx | exact Hy | reflexivity | reflexivity]).
  all: destruct y as [sy | sy | sy py Hpy | sy my ey Hmy];
    unfold msat_fp32_positive_finite in Hy;
    destruct Hy as [Hfy [Hsy Hynz]];
    simpl in Hfy, Hsy, Hynz; try discriminate; subst sy;
    try (contradiction Hynz; reflexivity);
    unfold fp32_div; simpl; exact I.
Qed.

Lemma fp32_finite_B2R_positive : forall x,
  Binary.is_finite 24 128 x = true ->
  (0 < Binary.B2R 24 128 x)%R ->
  msat_fp32_positive_finite x.
Proof.
  intros x Hfin Hpos.
  destruct x as [s | s | s p Hp | s m e Hm].
  - exfalso. simpl in Hpos. lra.
  - discriminate Hfin.
  - discriminate Hfin.
  - destruct s.
    + pose proof (F2R_gt_0 radix2 (Float radix2 (Z.pos m) e)
                    (Pos2Z.is_pos m)) as Hgt.
      assert (Hneg :
        (- F2R (Float radix2 (Z.pos m) e) < 0)%R).
      { apply Ropp_lt_gt_0_contravar. exact Hgt. }
      simpl in Hpos.
      change (0 < F2R (Float radix2 (Z.opp (Z.pos m)) e))%R in Hpos.
      rewrite F2R_Zopp in Hpos.
      exfalso. exact (Rlt_asym _ _ Hpos Hneg).
    + unfold msat_fp32_positive_finite. simpl.
      split; [reflexivity|]. split; [reflexivity|]. discriminate.
Qed.

Lemma fp32_of_real_correct : forall r,
  in_float32_range mode_NE r ->
  Binary.B2R 24 128 (fp32_of_real r) = rounded32 mode_NE r /\
  Binary.is_finite 24 128 (fp32_of_real r) = true.
Proof.
  intros r Hr. unfold in_float32_range in Hr.
  unfold fp32_of_real. cbv zeta.
  set (rr := rounded32 mode_NE r) in *.
  set (sz := Rlt_bool r 0).
  assert (Hg : generic_format radix2 fexp32 rr) by apply rounded32_generic.
  pose proof (binary_normalize_correct 24 128
                (eq_refl : Prec_gt_0 24) (eq_refl : Prec_lt_emax 24 128)
                mode_NE
                (Ztrunc (scaled_mantissa radix2 fexp32 rr))
                (cexp radix2 fexp32 rr) sz) as HC.
  change (SpecFloat.fexp 24 128) with fexp32 in HC.
  rewrite <- Hg in HC. cbv zeta in HC.
  rewrite (round_generic radix2 fexp32 (round_mode mode_NE) rr Hg) in HC.
  rewrite Rlt_bool_true in HC by exact Hr.
  destruct HC as [HR [Hfin _]]. split; assumption.
Qed.

Lemma fp32_of_real_positive_finite : forall r,
  in_float32_range mode_NE r ->
  (0 < rounded32 mode_NE r)%R ->
  msat_fp32_positive_finite (fp32_of_real r).
Proof.
  intros r Hr Hpos.
  pose proof (fp32_of_real_correct r Hr) as [Hread Hfin].
  apply fp32_finite_B2R_positive; [exact Hfin|]. now rewrite Hread.
Qed.

Lemma fp32_of_real_nonnegative : forall r,
  in_float32_range mode_NE r ->
  (0 <= r)%R -> (0 <= rounded32 mode_NE r)%R ->
  msat_fp32_nonnegative (fp32_of_real r).
Proof.
  intros r Hr Hrn Hrr. unfold in_float32_range in Hr.
  unfold fp32_of_real. cbv zeta.
  set (rr := rounded32 mode_NE r) in *.
  set (sz := Rlt_bool r 0).
  assert (Hg : generic_format radix2 fexp32 rr) by apply rounded32_generic.
  pose proof (binary_normalize_correct 24 128
                (eq_refl : Prec_gt_0 24) (eq_refl : Prec_lt_emax 24 128)
                mode_NE
                (Ztrunc (scaled_mantissa radix2 fexp32 rr))
                (cexp radix2 fexp32 rr) sz) as HC.
  change (SpecFloat.fexp 24 128) with fexp32 in HC.
  rewrite <- Hg in HC. cbv zeta in HC.
  rewrite (round_generic radix2 fexp32 (round_mode mode_NE) rr Hg) in HC.
  rewrite Rlt_bool_true in HC by exact Hr.
  destruct HC as [Hread [Hfin Hsign]].
  apply fp32_finite_sign_nonnegative; [exact Hfin|].
  rewrite Hsign. assert (Hsz : sz = false).
  { unfold sz. apply Rlt_bool_false. lra. }
  case (Flocq.Core.Raux.Rcompare_spec rr 0); intro Hcmp; simpl.
  - exfalso. lra.
  - exact Hsz.
  - reflexivity.
Qed.

Lemma fp32_of_real_zero_nonnegative :
  msat_fp32_nonnegative (fp32_of_real 0%R).
Proof.
  apply fp32_of_real_nonnegative.
  - unfold in_float32_range, rounded32.
    rewrite round_0 by apply valid_rnd_round_mode. rewrite Rabs_R0.
    exact (bpow_gt_0 radix2 128).
  - lra.
  - unfold rounded32. rewrite round_0 by apply valid_rnd_round_mode. lra.
Qed.

Lemma fp32_in_range_bpow : forall r e,
  (-149 <= e < 128)%Z ->
  (Rabs r <= bpow radix2 e)%R ->
  in_float32_range mode_NE r.
Proof.
  intros r e He Hr. unfold in_float32_range.
  apply Rle_lt_trans with (bpow radix2 e).
  - unfold rounded32, fexp32.
    apply abs_round_le_generic.
    + apply FLT_exp_valid. reflexivity.
    + apply valid_rnd_round_mode.
    + apply generic_format_bpow. unfold FLT_exp. simpl. lia.
    + exact Hr.
  - apply bpow_lt. lia.
Qed.

Lemma fp32_round_ge_bpow : forall r e,
  (-149 <= e)%Z ->
  (bpow radix2 e <= r)%R ->
  (bpow radix2 e <= rounded32 mode_NE r)%R.
Proof.
  intros r e He Hr. unfold rounded32, fexp32.
  apply round_ge_generic.
  - apply FLT_exp_valid. reflexivity.
  - apply valid_rnd_round_mode.
  - apply generic_format_bpow. unfold FLT_exp. simpl. lia.
  - exact Hr.
Qed.

Lemma fp32_of_real_positive_from_bpow : forall r lo hi,
  (-149 <= lo)%Z -> (-149 <= hi < 128)%Z ->
  (bpow radix2 lo <= r)%R -> (Rabs r <= bpow radix2 hi)%R ->
  msat_fp32_positive_finite (fp32_of_real r).
Proof.
  intros r lo hi Hlo Hhi Hlower Hupper.
  apply fp32_of_real_positive_finite.
  - now apply (fp32_in_range_bpow r hi).
  - pose proof (fp32_round_ge_bpow r lo Hlo Hlower).
    pose proof (bpow_gt_0 radix2 lo). lra.
Qed.

Lemma i32_in_float32_range : forall z,
  (-2147483648 <= z <= 2147483647)%Z ->
  in_float32_range mode_NE (IZR z).
Proof.
  intros z Hz. apply (fp32_in_range_bpow (IZR z) 31); [lia|].
  rewrite <- IZR_Zpower by lia. rewrite <- abs_IZR. apply IZR_le.
  change (radix_val radix2 ^ 31)%Z with 2147483648%Z. lia.
Qed.

Lemma Z_to_fp32_i32_positive_finite : forall z,
  (1 <= z <= 2147483647)%Z ->
  msat_fp32_positive_finite (Z_to_fp32 z).
Proof.
  intros z Hz. unfold Z_to_fp32, fp32_of_Z.
  apply fp32_of_real_positive_finite.
  - apply i32_in_float32_range. lia.
  - pose proof (fp32_round_ge_bpow (IZR z) 0 ltac:(lia)) as Hround.
    eapply Rlt_le_trans.
    + apply bpow_gt_0.
    + apply Hround. change (IZR 1 <= IZR z)%R.
      apply IZR_le. lia.
Qed.

Lemma fp32_to_fp64_nonnegative : forall x,
  msat_fp32_nonnegative x -> msat_fp64_nonnegative (fp32_to_fp64 x).
Proof.
  intros x Hx.
  destruct x as [s | s | s p Hp | s m e Hm]; destruct s; simpl in Hx;
    try contradiction; try exact I.
  destruct (fp32_to_fp64_exact (Binary.B754_finite 24 128 false m e Hm) eq_refl)
    as [Hfin HR].
  assert (Hpos : 0 < Binary.B2R 24 128 (Binary.B754_finite 24 128 false m e Hm)).
  { apply F2R_gt_0. simpl. lia. }
  rewrite <- HR in Hpos. revert Hfin Hpos.
  destruct (fp32_to_fp64 _) as [s' | s' | s' p' Hp' | s' m' e' Hm'];
    simpl; intros Hfin Hpos; try discriminate.
  - lra.
  - destruct s'; [|exact I].
    assert (Hneg : F2R (Float radix2 (Zneg m') e') < 0)
      by (apply F2R_lt_0; simpl; lia).
    simpl in Hpos. lra.
Qed.

Lemma fp64_count_limit_of_div : forall count inc,
  (0 <= count <= 2147483647)%Z ->
  msat_fp32_nonnegative inc ->
  msat_fp64_count_limit count (fp32_to_fp64 (fp32_div inc (Z_to_fp32 count))).
Proof.
  intros count inc Hcount Hinc.
  unfold msat_fp64_count_limit. intros Hpositive.
  apply fp32_to_fp64_nonnegative.
  apply fp32_nonnegative_div_positive_finite; [exact Hinc|].
  apply Z_to_fp32_i32_positive_finite. lia.
Qed.

Lemma fp64_of_real_correct : forall r,
  in_float64_range mode_NE r ->
  Binary.B2R 53 1024 (fp64_of_real r) = rounded64 mode_NE r /\
  fp64_isFinite (fp64_of_real r).
Proof.
  intros r Hr.
  unfold in_float64_range in Hr.
  unfold fp64_isFinite, fp64_of_real. cbv zeta.
  set (rr := rounded64 mode_NE r) in *.
  set (sz := Rlt_bool r 0).
  assert (Hg : generic_format radix2 fexp64 rr) by apply rounded64_generic.
  pose proof (binary_normalize_correct 53 1024
                (eq_refl : Prec_gt_0 53) (eq_refl : Prec_lt_emax 53 1024)
                mode_NE
                (Ztrunc (scaled_mantissa radix2 fexp64 rr))
                (cexp radix2 fexp64 rr) sz) as HC.
  change (SpecFloat.fexp 53 1024) with fexp64 in HC.
  rewrite <- Hg in HC. cbv zeta in HC.
  rewrite (round_generic radix2 fexp64 (round_mode mode_NE) rr Hg) in HC.
  rewrite Rlt_bool_true in HC by exact Hr.
  destruct HC as [HR [Hfin _]]. split; [exact HR | exact Hfin].
Qed.

Lemma i32_in_float64_range : forall z,
  (-2147483648 <= z <= 2147483647)%Z -> in_float64_range mode_NE (IZR z).
Proof.
  intros z Hz. unfold in_float64_range.
  apply Rle_lt_trans with (bpow radix2 31).
  - unfold rounded64, fexp64.
    apply abs_round_le_generic.
    + apply FLT_exp_valid. reflexivity.
    + apply valid_rnd_round_mode.
    + apply generic_format_bpow. unfold FLT_exp. simpl. lia.
    + rewrite <- IZR_Zpower by lia.
      rewrite <- abs_IZR. apply IZR_le.
      change (radix_val radix2 ^ 31)%Z with 2147483648%Z. lia.
  - apply bpow_lt. lia.
Qed.

Lemma Z_to_fp64_i32_finite : forall z,
  (-2147483648 <= z <= 2147483647)%Z -> fp64_isFinite (Z_to_fp64 z).
Proof.
  intros z Hz. unfold Z_to_fp64, fp64_of_Z.
  exact (proj2 (fp64_of_real_correct (IZR z) (i32_in_float64_range z Hz))).
Qed.

Lemma Z_to_fp64_ge_one : forall z,
  (1 <= z <= 2147483647)%Z ->
  bpow radix2 0 <= Binary.B2R 53 1024 (Z_to_fp64 z).
Proof.
  intros z Hz.
  unfold Z_to_fp64, fp64_of_Z.
  rewrite (proj1 (fp64_of_real_correct (IZR z)
                    (i32_in_float64_range z ltac:(lia)))).
  unfold rounded64, fexp64.
  apply round_ge_generic.
  - apply FLT_exp_valid. reflexivity.
  - apply valid_rnd_round_mode.
  - apply generic_format_bpow. unfold FLT_exp. simpl. lia.
  - rewrite <- IZR_Zpower by lia. apply IZR_le.
    change (radix_val radix2 ^ 0)%Z with 1%Z. lia.
Qed.

Lemma Z_to_fp64_seed_not_zero : forall z,
  seed_ok z -> Z_to_fp64 z <> msat_fp64_zero.
Proof.
  intros z Hz Heq. unfold seed_ok in Hz.
  pose proof (Z_to_fp64_ge_one z ltac:(lia)) as H1.
  rewrite Heq in H1. unfold msat_fp64_zero in H1. simpl in H1.
  pose proof (bpow_gt_0 radix2 0) as Hp. lra.
Qed.

Lemma fp32_search_decay_positive_finite :
  msat_fp32_positive_finite
    (fp64_to_fp32 (fp64_div (Z_to_fp64 1) (fp64_of_real 0.999))).
Proof.
  assert (Hvalid : Valid_exp fexp64) by (apply FLT_exp_valid; reflexivity).
  assert (Hg0 : generic_format radix2 fexp64 (bpow radix2 0))
    by (apply generic_format_bpow; unfold fexp64, fexp32, FLT_exp; simpl; lia).
  assert (Hg1 : generic_format radix2 fexp64 (bpow radix2 1))
    by (apply generic_format_bpow; unfold fexp64, fexp32, FLT_exp; simpl; lia).
  assert (Hgm1 : generic_format radix2 fexp64 (bpow radix2 (-1)))
    by (apply generic_format_bpow; unfold fexp64, fexp32, FLT_exp; simpl; lia).
  change (bpow radix2 0) with 1 in Hg0.
  change (bpow radix2 1) with 2 in Hg1.
  replace (bpow radix2 (-1)) with (/2) in Hgm1 by (simpl; lra).
  assert (Hy_range : in_float64_range mode_NE 0.999).
  { unfold in_float64_range. apply Rle_lt_trans with 1.
    - unfold rounded64. apply abs_round_le_generic;
        [exact Hvalid | apply valid_rnd_round_mode | exact Hg0 |].
      rewrite Rabs_right by lra. lra.
    - change 1 with (bpow radix2 0). apply bpow_lt. lia. }
  destruct (fp64_of_real_correct 0.999 Hy_range) as [HyR Hyfin].
  assert (Hylo : /2 <= rounded64 mode_NE 0.999).
  { unfold rounded64. apply round_ge_generic;
      [exact Hvalid | apply valid_rnd_round_mode | exact Hgm1 | lra]. }
  assert (Hyhi : rounded64 mode_NE 0.999 <= 1).
  { unfold rounded64. apply round_le_generic;
      [exact Hvalid | apply valid_rnd_round_mode | exact Hg0 | lra]. }
  assert (HxR : Binary.B2R 53 1024 (Z_to_fp64 1) = 1).
  { unfold Z_to_fp64, fp64_of_Z.
    rewrite (proj1 (fp64_of_real_correct (IZR 1)
                      (i32_in_float64_range 1 ltac:(lia)))).
    unfold rounded64. apply round_generic; [apply valid_rnd_round_mode | exact Hg0]. }
  pose proof (Z_to_fp64_i32_finite 1 ltac:(lia)) as Hxfin.
  set (q := 1 / rounded64 mode_NE 0.999).
  assert (Hq : 1 <= q <= 2).
  { unfold q. split.
    - apply (Rmult_le_reg_r (rounded64 mode_NE 0.999)); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
    - apply (Rmult_le_reg_r (rounded64 mode_NE 0.999)); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Hrq : 1 <= rounded64 mode_NE q <= 2).
  { unfold rounded64. split.
    - apply round_ge_generic; [exact Hvalid | apply valid_rnd_round_mode | exact Hg0 | lra].
    - apply round_le_generic; [exact Hvalid | apply valid_rnd_round_mode | exact Hg1 | lra]. }
  pose proof (Binary.Bdiv_correct 53 1024 eq_refl eq_refl fp64_binary_nan mode_NE
                (Z_to_fp64 1) (fp64_of_real 0.999)) as HD.
  rewrite HyR in HD. specialize (HD ltac:(lra)).
  change (SpecFloat.fexp 53 1024) with fexp64 in HD.
  rewrite HxR in HD. fold q in HD. fold (rounded64 mode_NE q) in HD.
  rewrite Rlt_bool_true in HD.
  2:{ rewrite Rabs_right by lra. apply Rle_lt_trans with 2; [lra|].
      change 2 with (bpow radix2 1). apply bpow_lt. lia. }
  destruct HD as [HzR [Hzfin _]].
  fold (fp64_div (Z_to_fp64 1) (fp64_of_real 0.999)) in HzR, Hzfin.
  unfold fp64_isFinite in Hxfin. rewrite Hxfin in Hzfin.
  assert (Hg0' : generic_format radix2 fexp32 1)
    by (change 1 with (bpow radix2 0); apply generic_format_bpow; unfold fexp64, fexp32, FLT_exp; simpl; lia).
  assert (Hg1' : generic_format radix2 fexp32 2)
    by (change 2 with (bpow radix2 1); apply generic_format_bpow; unfold fexp64, fexp32, FLT_exp; simpl; lia).
  assert (Hr32 : 1 <= rounded32 mode_NE (rounded64 mode_NE q) <= 2).
  { unfold rounded32. split.
    - apply round_ge_generic; [apply FLT_exp_valid; reflexivity | apply valid_rnd_round_mode | exact Hg0' | lra].
    - apply round_le_generic; [apply FLT_exp_valid; reflexivity | apply valid_rnd_round_mode | exact Hg1' | lra]. }
  destruct (fp64_to_fp32_round _ Hzfin) as [Hwfin HwR].
  { rewrite HzR, Rabs_right by lra. apply Rle_lt_trans with 2; [lra|].
    change 2 with (bpow radix2 1). apply bpow_lt. lia. }
  apply fp32_finite_B2R_positive; [exact Hwfin|].
  rewrite HwR, HzR. lra.
Qed.

End MSatFloatFacts.

Lemma root_satisfied_cancel__canceluntil_cap : forall n t c level,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  root_satisfied t c -> root_satisfied (mt_cancel t level) c.
Proof.
  intros n t c level Hwf Hlevel [lit [Hin [Htrue Hroot]]].
  exists lit. split; [exact Hin|]. split.
  - assert (Hassigned : exists b, mt_pv t (literal_var lit) = Some b).
    { assert (Hsome : mt_pv t (literal_var lit) <> None).
      { intro Hnone. unfold eval_partial_literal in Htrue.
        rewrite Hnone in Htrue. discriminate. }
      destruct (mt_pv t (literal_var lit)) as [b|] eqn:Hpv.
      - exists b. reflexivity.
      - contradiction. }
    destruct Hassigned as [b Hpv].
    assert (Hpos : trail_pos t (literal_var lit) <> None).
    { intro Hnone. apply (proj2 (view_unassigned_iff n t
        (literal_var lit) Hwf)) in Hnone. congruence. }
    destruct (trail_pos t (literal_var lit)) as [k|] eqn:Hk;
      [|contradiction].
    pose proof (trail_pos_bound t (literal_var lit) k Hk) as Hkb.
    pose proof (trail_pos_var t (literal_var lit) k Hk) as Hvar.
    pose proof (mtw_levels_agree Hwf (Z.of_nat k)
      ltac:(lia)) as Hlevel_index.
    rewrite Hvar in Hlevel_index.
    assert (Hcount : level_of_index t (Z.of_nat k) = 0) by congruence.
    assert (Hlt : Z.of_nat k < Znth level (mt_lim t) 0).
    { apply (strict_sorted_count_suffix
        (mt_lim t) (Z.of_nat k) level (mtw_lim_sorted Hwf)).
      - unfold level_of_index in Hcount. lia.
      - exact Hlevel. }
    assert (Hkeep : In (literal_var lit)
      (map lit_var_c (mt_trail (mt_cancel t level)))).
    { rewrite mt_cancel_trail.
      replace (literal_var lit) with
        (lit_var_c (Znth (Z.of_nat k) (mt_trail t) 0)) by
        (unfold trail_var in Hvar; exact Hvar).
      apply in_map.
      rewrite <- (Znth_ztake (Znth level (mt_lim t) 0)
        (mt_trail t) (Z.of_nat k) 0) by lia. apply Znth_In.
      rewrite Zlength_ztake by
        (pose proof (lim_lt_trail n t level Hwf Hlevel); lia).
      lia. }
    unfold eval_partial_literal in *.
    rewrite (mt_pv_cancel_keep n t level (literal_var lit)
      Hwf Hlevel Hkeep).
    exact Htrue.
  - rewrite mt_cancel_levels. exact Hroot.
Qed.

Lemma db_pair_lits_update_words__propagate :
  forall prob learnt p old_lits new_lits prob' learnt',
    db_pair_lits_update prob learnt p old_lits new_lits prob' learnt' ->
    map fst prob' = map fst prob /\ map fst learnt' = map fst learnt.
Proof.
  intros prob learnt p old_lits new_lits prob' learnt' H.
  destruct H as
    [[co [pre [post [Hprob [Hold [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hold [Hprob' Hlearnt']]]]]]].
  - subst. repeat rewrite map_app. cbn. split; reflexivity.
  - subst. repeat rewrite map_app. cbn. split; reflexivity.
Qed.

Lemma learnt_sort_rep_app_intro__clause_cmp : forall db1 db2 a1 a2,
  List.length db1 = List.length a1 ->
  learnt_sort_rep db1 a1 ** learnt_sort_rep db2 a2 |--
  learnt_sort_rep (db1 ++ db2) (a1 ++ a2).
Proof.
  intros db1. induction db1 as [|[p co] db1 IH];
    intros db2 a1 a2 Hlen.
  - destruct a1 as [|a a1].
    + simpl. (Intros; cancel).
    + simpl in Hlen. lia.
  - destruct a1 as [|a a1].
    + simpl in Hlen. lia.
    + simpl in Hlen.
      cbn [List.app learnt_sort_rep].
      Intros_p Hhead.
      sep_apply (IH db2 a1 a2 ltac:(lia)).
      (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma learnt_sort_rep_cons_intro__clause_cmp :
  forall p co db a activities,
  co_learnt co = true ->
  learnt_clause_snapshot_raw p (co_lits co) a **
  learnt_sort_rep db activities |--
  learnt_sort_rep ((p, co) :: db) (a :: activities).
Proof.
  intros p co db a activities Htag.
  unfold learnt_clause_snapshot_raw at 1.
  Intros_p Hsnapshot.
  cbn [learnt_sort_rep].
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma learnt_sort_rep_alias_refold__clause_cmp :
  forall db activities x xlits xa,
  learnt_clause_snapshot_raw x xlits xa **
  learnt_sort_alias_remainder db activities x xlits xa |--
  learnt_sort_rep db activities.
Proof.
  intros db activities x xlits xa.
  unfold learnt_sort_alias_remainder at 1.
  Intros co pre post apre apost.
  destruct H as
    [Hdb [Hactivities [Hprelen [Hlits [Htag Hnonneg]]]]].
  assert (Hlen : List.length pre = List.length apre).
  { rewrite !Zlength_correct in Hprelen. lia. }
  rewrite Hdb, Hactivities.
  rewrite <- Hlits.
  sep_apply
    (learnt_sort_rep_cons_intro__clause_cmp
       x co post xa apost Htag).
  sep_apply
    (learnt_sort_rep_app_intro__clause_cmp
       pre ((x, co) :: post) apre (xa :: apost) Hlen).
  cancel.
Qed.

(* Reattach one clause and the untouched segment preceding it. *)
Local Ltac msat_learnt_sort_refold_prefix p co tail activity activities Htag
    pre apre Hlen :=
  sep_apply (learnt_sort_rep_cons_intro__clause_cmp
    p co tail activity activities Htag);
  sep_apply (learnt_sort_rep_app_intro__clause_cmp
    pre ((p, co) :: tail) apre (activity :: activities) Hlen).

Lemma learnt_sort_rep_two_refold__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  learnt_clause_snapshot_raw x xlits xa **
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  learnt_sort_rep db activities.
Proof.
  intros db activities x xlits xa y ylits ya.
  unfold learnt_sort_two_remainder at 1.
  Split;
    Intros cox coy pre mid post apre amid apost;
    destruct H as
      [Hdb [Hactivities [Hprelen [Hmidlen
       [Hxlits [Hylits [Hxtag [Hytag [Hxnonneg Hynonneg]]]]]]]]];
    assert (Hpre : List.length pre = List.length apre)
      by (rewrite !Zlength_correct in Hprelen; lia);
    assert (Hmid : List.length mid = List.length amid)
      by (rewrite !Zlength_correct in Hmidlen; lia);
    rewrite Hdb, Hactivities;
    rewrite <- Hxlits; rewrite <- Hylits.
  - msat_learnt_sort_refold_prefix y coy post ya apost Hytag mid amid Hmid.
    msat_learnt_sort_refold_prefix x cox (mid ++ (y, coy) :: post)
      xa (amid ++ ya :: apost) Hxtag pre apre Hpre.
    cancel.
  - msat_learnt_sort_refold_prefix x cox post xa apost Hxtag mid amid Hmid.
    msat_learnt_sort_refold_prefix y coy (mid ++ (x, cox) :: post)
      ya (amid ++ xa :: apost) Hytag pre apre Hpre.
    cancel.
Qed.

Lemma learnt_sort_key_prefix__clause_cmp :
  forall pre db apre activities p co a,
  List.length pre = List.length apre ->
  learnt_sort_key db activities p co a ->
  learnt_sort_key (pre ++ db) (apre ++ activities) p co a.
Proof.
  intros pre.
  induction pre as [| [q cq] pre IH]; intros db apre activities p co a Hlen Hkey.
  - destruct apre as [| aq apre].
    + exact Hkey.
    + simpl in Hlen. discriminate.
  - destruct apre as [| aq apre].
    + simpl in Hlen. discriminate.
    + cbn [List.app learnt_sort_key].
      right. apply IH.
      * simpl in Hlen. lia.
      * exact Hkey.
Qed.

Lemma learnt_sort_two_keys__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  learnt_clause_snapshot_raw x xlits xa **
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ exists cox coy,
      learnt_sort_key db activities x cox xa /\
      learnt_sort_key db activities y coy ya /\
      co_lits cox = xlits /\ co_lits coy = ylits ”.
Proof.
  intros db activities x xlits xa y ylits ya.
  unfold learnt_sort_two_remainder at 1.
  Split.
  - Intros cox coy pre mid post apre amid apost.
    destruct H as
      [Hdb [Hactivities [Hprelen [Hmidlen
       [Hxlits [Hylits [Hxtag [Hytag [Hxnonneg Hynonneg]]]]]]]]].
    assert (Hpre : List.length pre = List.length apre).
    { rewrite !Zlength_correct in Hprelen. lia. }
    assert (Hmid : List.length mid = List.length amid).
    { rewrite !Zlength_correct in Hmidlen. lia. }
    assert (Hxkey : learnt_sort_key db activities x cox xa).
    { rewrite Hdb, Hactivities.
      apply learnt_sort_key_prefix__clause_cmp; [exact Hpre |].
      cbn [learnt_sort_key]. auto. }
    assert (Hykey : learnt_sort_key db activities y coy ya).
    { rewrite Hdb, Hactivities.
      apply learnt_sort_key_prefix__clause_cmp; [exact Hpre |].
      cbn [learnt_sort_key]. right.
      apply learnt_sort_key_prefix__clause_cmp; [exact Hmid |].
      cbn [learnt_sort_key]. auto. }
    Exists cox coy. apply derivable1s_coq_prop_r.
    repeat split; assumption.
  - Intros cox coy pre mid post apre amid apost.
    destruct H as
      [Hdb [Hactivities [Hprelen [Hmidlen
       [Hxlits [Hylits [Hxtag [Hytag [Hxnonneg Hynonneg]]]]]]]]].
    assert (Hpre : List.length pre = List.length apre).
    { rewrite !Zlength_correct in Hprelen. lia. }
    assert (Hmid : List.length mid = List.length amid).
    { rewrite !Zlength_correct in Hmidlen. lia. }
    assert (Hxkey : learnt_sort_key db activities x cox xa).
    { rewrite Hdb, Hactivities.
      apply learnt_sort_key_prefix__clause_cmp; [exact Hpre |].
      cbn [learnt_sort_key]. right.
      apply learnt_sort_key_prefix__clause_cmp; [exact Hmid |].
      cbn [learnt_sort_key]. auto. }
    assert (Hykey : learnt_sort_key db activities y coy ya).
    { rewrite Hdb, Hactivities.
      apply learnt_sort_key_prefix__clause_cmp; [exact Hpre |].
      cbn [learnt_sort_key]. auto. }
    Exists cox coy. apply derivable1s_coq_prop_r.
    repeat split; assumption.
Qed.

Lemma learnt_cmp_result_lt_two__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  2 < Zlength xlits ->
  (Zlength ylits = 2 \/ fp32_lt xa ya) ->
  learnt_clause_snapshot_raw x xlits xa **
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ learnt_cmp_result db activities x y (-1) ” &&
  learnt_sort_rep db activities.
Proof.
  intros db activities x xlits xa y ylits ya Hxlen Hycond.
  apply _derivable1_andp_intros.
  - sep_apply (learnt_sort_two_keys__clause_cmp
      db activities x xlits xa y ylits ya).
    apply coq_prop_imply.
    intros [cox [coy [Hxkey [Hykey [Hxlits Hylits]]]]].
    unfold learnt_cmp_result, learnt_cmp_lt.
    left. split; [reflexivity |].
    exists cox, coy, xa, ya.
    repeat split; try assumption.
    + rewrite Hxlits. exact Hxlen.
    + destruct Hycond as [Hylen | Hlt].
      * left. now rewrite Hylits.
      * right. exact Hlt.
  - apply learnt_sort_rep_two_refold__clause_cmp.
Qed.

Lemma learnt_clause_snapshot_raw_dup__clause_cmp :
  forall p l1 a1 l2 a2,
  learnt_clause_snapshot_raw p l1 a1 **
  learnt_clause_snapshot_raw p l2 a2 |--
  “ False ”.
Proof.
  intros p l1 a1 l2 a2.
  unfold learnt_clause_snapshot_raw at 1.
  Intros_p Hsnap1.
  unfold learnt_clause_snapshot_raw at 1.
  Intros_p Hsnap2.
  Intros.
  sep_apply (dup_store_int (clause_hdr_addr p)
    (clause_hdr_word true (Zlength l1))
    (clause_hdr_word true (Zlength l2))).
  (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
Qed.

Lemma learnt_sort_rep_key_focus__clause_cmp :
  forall db activities p co a,
  learnt_sort_key db activities p co a ->
  learnt_sort_rep db activities |--
  learnt_clause_snapshot_raw p (co_lits co) a ** TT.
Proof.
  intros db.
  induction db as [| [q cq] db IH]; intros activities p co a Hkey.
  - destruct activities; cbn [learnt_sort_key] in Hkey; contradiction.
  - destruct activities as [| aq activities].
    + cbn [learnt_sort_key] in Hkey. contradiction.
    + cbn [learnt_sort_key] in Hkey.
      destruct Hkey as [[Hp [Hco Ha]] | Htail].
      * subst p co a.
        cbn [learnt_sort_rep].
        unfold learnt_clause_snapshot_raw.
        (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (int_auto)] ..]).
        apply derivable1_truep_intros.
      * cbn [learnt_sort_rep].
        Intros_p Hhead.
        sep_apply (IH activities p co a Htail).
        cancel.
        apply derivable1_truep_intros.
Qed.

Lemma learnt_sort_key_prefix_elim__clause_cmp :
  forall pre db apre activities p co a,
  List.length pre = List.length apre ->
  learnt_sort_key (pre ++ db) (apre ++ activities) p co a ->
  learnt_sort_key pre apre p co a \/
  learnt_sort_key db activities p co a.
Proof.
  intros pre.
  induction pre as [| [q cq] pre IH]; intros db apre activities p co a Hlen Hkey.
  - destruct apre as [| aq apre].
    + right. exact Hkey.
    + simpl in Hlen. discriminate.
  - destruct apre as [| aq apre].
    + simpl in Hlen. discriminate.
    + cbn [List.app learnt_sort_key] in Hkey |- *.
      destruct Hkey as [Hhead | Htail].
      * left. exact (or_introl Hhead).
      * destruct (IH db apre activities p co a) as [Hpre | Hdb].
        -- simpl in Hlen. lia.
        -- exact Htail.
        -- left. exact (or_intror Hpre).
        -- right. exact Hdb.
Qed.

Lemma learnt_sort_alias_key_unique__clause_cmp :
  forall db activities x xlits xa co a,
  learnt_sort_key db activities x co a ->
  learnt_clause_snapshot_raw x xlits xa **
  learnt_sort_alias_remainder db activities x xlits xa |--
  “ co_lits co = xlits /\ a = xa ”.
Proof.
  intros db activities x xlits xa co a Hkey.
  unfold learnt_sort_alias_remainder at 1.
  Intros co0 pre post apre apost.
  destruct H as [Hdb [Hactivities [Hprelen [Hlits [Htag Hnonneg]]]]].
  assert (Hpre : List.length pre = List.length apre).
  { rewrite !Zlength_correct in Hprelen. lia. }
  rewrite Hdb, Hactivities in Hkey.
  destruct (learnt_sort_key_prefix_elim__clause_cmp
    pre ((x, co0) :: post) apre (xa :: apost) x co a Hpre Hkey)
    as [Hinpre | Hrest].
  - sep_apply (learnt_sort_rep_key_focus__clause_cmp
      pre apre x co a Hinpre).
    sep_apply (learnt_clause_snapshot_raw_dup__clause_cmp x (co_lits co) a xlits xa).
    (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - cbn [learnt_sort_key] in Hrest.
    destruct Hrest as [[Hx [Hco Ha]] | Hinpost].
    + subst co a. apply derivable1s_coq_prop_r.
      split; [exact Hlits | reflexivity].
    + sep_apply (learnt_sort_rep_key_focus__clause_cmp
        post apost x co a Hinpost).
      sep_apply (learnt_clause_snapshot_raw_dup__clause_cmp x (co_lits co) a xlits xa).
      (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
Qed.

Lemma learnt_cmp_stop_alias__clause_cmp :
  forall db activities x xlits xa,
  msat_fp32_nonnegative xa ->
  learnt_clause_snapshot_raw x xlits xa **
  learnt_sort_alias_remainder db activities x xlits xa |--
  “ learnt_cmp_stop db activities x x ”.
Proof.
  intros db activities x xlits xa Hnonnegative.
  unfold derivable1.
  intros m Hspatial.
  unfold coq_prop.
  unfold learnt_cmp_stop, learnt_cmp_lt.
  intros Hlt.
  destruct Hlt as
    [cox [coy [ax [ay [Hxkey [Hykey [Hxlen Hycond]]]]]]].
  pose proof (learnt_sort_alias_key_unique__clause_cmp
    db activities x xlits xa cox ax Hxkey m Hspatial) as Hxunique.
  pose proof (learnt_sort_alias_key_unique__clause_cmp
    db activities x xlits xa coy ay Hykey m Hspatial) as Hyunique.
  unfold coq_prop in Hxunique, Hyunique.
  destruct Hxunique as [Hxlits Hxa].
  destruct Hyunique as [Hylits Hya].
  destruct Hycond as [Hylen | Hactivity].
  - rewrite Hxlits in Hxlen.
    rewrite Hylits in Hylen.
    lia.
  - rewrite Hxa in Hactivity.
    rewrite Hya in Hactivity.
    pose proof (MSatFloatFacts.fp32_nonnegative_eq_refl
      xa Hnonnegative) as Heq.
    unfold fp32_lt, fp32_eq in Hactivity, Heq.
    congruence.
Qed.

Lemma learnt_cmp_result_stop_alias__clause_cmp :
  forall db activities x xlits xa,
  msat_fp32_nonnegative xa ->
  learnt_clause_snapshot_raw x xlits xa **
  learnt_sort_alias_remainder db activities x xlits xa |--
  “ learnt_cmp_result db activities x x 1 ” &&
  learnt_sort_rep db activities.
Proof.
  intros db activities x xlits xa Hnonnegative.
  apply _derivable1_andp_intros.
  - sep_apply (learnt_cmp_stop_alias__clause_cmp
      db activities x xlits xa Hnonnegative).
    apply coq_prop_imply.
    intros Hstop.
    unfold learnt_cmp_result.
    right. split; [reflexivity | exact Hstop].
  - apply learnt_sort_rep_alias_refold__clause_cmp.
Qed.

Lemma learnt_sort_two_to_alias_x__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  learnt_clause_snapshot_raw x xlits xa **
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  learnt_clause_snapshot_raw x xlits xa **
  learnt_sort_alias_remainder db activities x xlits xa.
Proof.
  intros db activities x xlits xa y ylits ya.
  unfold learnt_sort_two_remainder at 1.
  Split.
  - Intros cox coy pre mid post apre amid apost.
    destruct H as
      [Hdb [Hactivities [Hprelen [Hmidlen
       [Hxlits [Hylits [Hxtag [Hytag [Hxnonneg Hynonneg]]]]]]]]].
    assert (Hmid : List.length mid = List.length amid).
    { rewrite !Zlength_correct in Hmidlen. lia. }
    rewrite <- Hylits.
    sep_apply (learnt_sort_rep_cons_intro__clause_cmp
      y coy post ya apost Hytag).
    sep_apply (learnt_sort_rep_app_intro__clause_cmp
      mid ((y, coy) :: post) amid (ya :: apost) Hmid).
    unfold learnt_sort_alias_remainder.
    Exists cox pre (mid ++ (y, coy) :: post)
      apre (amid ++ ya :: apost).
    split_pure_spatial.
    + cancel (learnt_sort_rep pre apre).
      cancel.
    + dump_pre_spatial. tauto.
  - Intros cox coy pre mid post apre amid apost.
    destruct H as
      [Hdb [Hactivities [Hprelen [Hmidlen
       [Hxlits [Hylits [Hxtag [Hytag [Hxnonneg Hynonneg]]]]]]]]].
    assert (Hpre : List.length pre = List.length apre).
    { rewrite !Zlength_correct in Hprelen. lia. }
    assert (Hmid : List.length mid = List.length amid).
    { rewrite !Zlength_correct in Hmidlen. lia. }
    rewrite <- Hylits.
    sep_apply (learnt_sort_rep_cons_intro__clause_cmp
      y coy mid ya amid Hytag).
    sep_apply (learnt_sort_rep_app_intro__clause_cmp
      pre ((y, coy) :: mid) apre (ya :: amid) Hpre).
    unfold learnt_sort_alias_remainder.
    Exists cox (pre ++ (y, coy) :: mid) post
      (apre ++ ya :: amid) apost.
    split_pure_spatial.
    + cancel (learnt_sort_rep post apost).
      cancel.
    + dump_pre_spatial.
      repeat split; auto.
      * rewrite Hdb, <- app_assoc. reflexivity.
      * rewrite Hactivities, <- app_assoc. reflexivity.
      * rewrite !Zlength_app, !Zlength_cons. lia.
Qed.

Lemma learnt_sort_two_remainder_swap :
  forall db activities x xlits xa y ylits ya,
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  learnt_sort_two_remainder db activities y ylits ya x xlits xa.
Proof.
  intros db activities x xlits xa y ylits ya.
  unfold learnt_sort_two_remainder. Split.
  - Intros cox coy pre mid post apre amid apost.
    Right. Exists coy cox pre mid post apre amid apost.
    split_pure_spatial.
    + cancel (learnt_sort_rep pre apre). cancel.
    + dump_pre_spatial. tauto.
  - Intros cox coy pre mid post apre amid apost.
    Left. Exists coy cox pre mid post apre amid apost.
    split_pure_spatial.
    + cancel (learnt_sort_rep pre apre). cancel.
    + dump_pre_spatial. tauto.
Qed.

Lemma learnt_sort_two_to_alias_y__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  learnt_clause_snapshot_raw x xlits xa **
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_alias_remainder db activities y ylits ya.
Proof.
  intros db activities x xlits xa y ylits ya.
  sep_apply (learnt_sort_two_remainder_swap db activities x xlits xa y ylits ya).
  sep_apply (learnt_sort_two_to_alias_x__clause_cmp db activities y ylits ya x xlits xa).
  cancel.
Qed.

Lemma learnt_cmp_stop_two__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  (Zlength xlits <= 2 \/
   (Zlength ylits <> 2 /\ fp32_ge xa ya)) ->
  learnt_clause_snapshot_raw x xlits xa **
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ learnt_cmp_stop db activities x y ”.
Proof.
  intros db activities x xlits xa y ylits ya Hcondition.
  unfold derivable1.
  intros m Hspatial.
  unfold coq_prop.
  unfold learnt_cmp_stop, learnt_cmp_lt.
  intros Hlt.
  destruct Hlt as
    [cox [coy [ax [ay [Hxkey [Hykey [Hxlen Hycond]]]]]]].
  pose proof (learnt_sort_two_to_alias_x__clause_cmp
    db activities x xlits xa y ylits ya m Hspatial) as Hxalias.
  pose proof (learnt_sort_two_to_alias_y__clause_cmp
    db activities x xlits xa y ylits ya m Hspatial) as Hyalias.
  pose proof (learnt_sort_alias_key_unique__clause_cmp
    db activities x xlits xa cox ax Hxkey m Hxalias) as Hxunique.
  pose proof (learnt_sort_alias_key_unique__clause_cmp
    db activities y ylits ya coy ay Hykey m Hyalias) as Hyunique.
  unfold coq_prop in Hxunique, Hyunique.
  destruct Hxunique as [Hxlits Hxa].
  destruct Hyunique as [Hylits Hya].
  destruct Hcondition as [Hxshort | [Hynotbinary Hge]].
  - rewrite Hxlits in Hxlen. lia.
  - destruct Hycond as [Hybinary | Hactivity].
    + rewrite Hylits in Hybinary. contradiction.
    + rewrite Hxa in Hactivity.
      rewrite Hya in Hactivity.
      unfold fp32_lt in Hactivity.
      unfold fp32_ge in Hge.
      destruct (fp32_compare xa ya) as [cmp |];
        [destruct cmp |]; simpl in Hge; try contradiction; discriminate.
Qed.

Lemma learnt_cmp_result_stop_two__clause_cmp :
  forall db activities x xlits xa y ylits ya,
  (Zlength xlits <= 2 \/
   (Zlength ylits <> 2 /\ fp32_ge xa ya)) ->
  learnt_clause_snapshot_raw x xlits xa **
  learnt_clause_snapshot_raw y ylits ya **
  learnt_sort_two_remainder db activities x xlits xa y ylits ya |--
  “ learnt_cmp_result db activities x y 1 ” &&
  learnt_sort_rep db activities.
Proof.
  intros db activities x xlits xa y ylits ya Hcondition.
  apply _derivable1_andp_intros.
  - sep_apply (learnt_cmp_stop_two__clause_cmp
      db activities x xlits xa y ylits ya Hcondition).
    apply coq_prop_imply.
    intros Hstop.
    unfold learnt_cmp_result.
    right. split; [reflexivity | exact Hstop].
  - apply learnt_sort_rep_two_refold__clause_cmp.
Qed.

Lemma solver_shape_assume__search : forall M l,
  solver_shape M -> ms_qtail M < ms_cap M ->
  ms_capacity_root_propagation_pending M = 0 ->
  solver_shape (msolver_assume M l).
Proof.
  intros M l Hshape Hroom Hpending.
  destruct Hshape as
    [Hsize [Hcap [Htwice [Hassigns [Hlevels [Hreasons [Horderpos
    [Hactivity [Htags [Htrail [Hqhead [Hpendingrange [Hpending01
    [Hpendingcase [Hqtail [Hwm [Hbinarylits [Hstats
    [Hroot [Hbinarynz Hbinaryeven]]]]]]]]]]]]]]]]]]]].
  unfold solver_shape, msolver_assume, mt_decide, mt_push. cbn.
  repeat rewrite Zlength_replace_Znth.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  repeat split; try assumption; try lia.
Qed.

(** * Propagation updates. *)

Lemma obj_wf_clause_obj_with_lits_perm__propagate_dbu :
  forall n co new_lits,
    obj_wf n co ->
    Permutation new_lits (co_lits co) ->
    obj_wf n (clause_obj_with_lits co new_lits).
Proof.
  intros n co new_lits [Hlen [Hall Hnodup]] Hperm.
  unfold obj_wf, clause_obj_with_lits. cbn.
  split.
  - pose proof (Zlength_perm_eq Z new_lits (co_lits co) Hperm) as Hlenperm.
    lia.
  - split.
    + eapply Forall_of_perm; [apply Permutation_sym; exact Hperm | exact Hall].
    + eapply Permutation_NoDup; [| exact Hnodup].
      apply Permutation_map. apply Permutation_sym. exact Hperm.
Qed.

Lemma db_wf_replace_lits__propagate_dbu :
  forall n pre p co post new_lits,
    db_wf n (pre ++ (p, co) :: post) ->
    Permutation new_lits (co_lits co) ->
    db_wf n
      (pre ++ (p, clause_obj_with_lits co new_lits) :: post).
Proof.
  intros n pre p co post new_lits [Hkeys [Hptrs Hobjs]] Hperm.
  assert (Hkeyeq :
    map fst (pre ++ (p, clause_obj_with_lits co new_lits) :: post) =
    map fst (pre ++ (p, co) :: post)).
  { repeat rewrite map_app. cbn. reflexivity. }
  split; [rewrite Hkeyeq; exact Hkeys |]. split.
  - rewrite Forall_forall in Hptrs |- *. intros e He.
    assert (Hemap :
      In (fst e)
        (map fst (pre ++ (p, clause_obj_with_lits co new_lits) :: post))).
    { apply in_map. exact He. }
    rewrite Hkeyeq in Hemap.
    apply in_map_iff in Hemap as [eold [Hfst Heold]].
    specialize (Hptrs eold Heold). rewrite <- Hfst. exact Hptrs.
  - rewrite Forall_forall in Hobjs |- *. intros [q obj] He.
    destruct (in_app_or _ _ _ He) as [Hepre | Hecons].
    + apply Hobjs. apply in_or_app. left. exact Hepre.
    + destruct Hecons as [Heq | Hepost].
      * inversion Heq; subst q obj.
        assert (Holdobj : obj_wf n co).
        { apply (Hobjs (p, co)).
          apply in_or_app. right. simpl. auto. }
        exact
          (obj_wf_clause_obj_with_lits_perm__propagate_dbu
             n co new_lits Holdobj Hperm).
      * apply Hobjs. apply in_or_app. right. simpl. right. exact Hepost.
Qed.

Lemma prob_db_replace_lits__propagate_dbu :
  forall pre p co post new_lits,
    prob_db (pre ++ (p, co) :: post) ->
    prob_db (pre ++ (p, clause_obj_with_lits co new_lits) :: post).
Proof.
  intros pre p co post new_lits H.
  unfold prob_db in H |- *. rewrite Forall_forall in H |- *.
  intros [q obj] He.
  destruct (in_app_or _ _ _ He) as [Hepre | Hecons].
  - apply H. apply in_or_app. left. exact Hepre.
  - destruct Hecons as [Heq | Hepost].
    + inversion Heq; subst q obj.
      unfold clause_obj_with_lits; cbn.
      assert (Hold : co_learnt (snd (p, co)) = false).
      { apply H. apply in_or_app. right. simpl. auto. }
      cbn in Hold. exact Hold.
    + apply H. apply in_or_app. right. simpl. right. exact Hepost.
Qed.

Lemma learnt_db_replace_lits__propagate_dbu :
  forall pre p co post new_lits,
    learnt_db (pre ++ (p, co) :: post) ->
    learnt_db (pre ++ (p, clause_obj_with_lits co new_lits) :: post).
Proof.
  intros pre p co post new_lits H.
  unfold learnt_db in H |- *. rewrite Forall_forall in H |- *.
  intros [q obj] He.
  destruct (in_app_or _ _ _ He) as [Hepre | Hecons].
  - apply H. apply in_or_app. left. exact Hepre.
  - destruct Hecons as [Heq | Hepost].
    + inversion Heq; subst q obj.
      unfold clause_obj_with_lits; cbn.
      assert (Hold : co_learnt (snd (p, co)) = true).
      { apply H. apply in_or_app. right. simpl. auto. }
      cbn in Hold. exact Hold.
    + apply H. apply in_or_app. right. simpl. right. exact Hepost.
Qed.

Lemma db_pair_lits_update_db_wf__propagate_dbu :
  forall n prob learnt p old_lits new_lits prob' learnt',
    db_wf n (prob ++ learnt) ->
    Permutation new_lits old_lits ->
    db_pair_lits_update prob learnt p old_lits new_lits prob' learnt' ->
    db_wf n (prob' ++ learnt').
Proof.
  intros n prob learnt p old_lits new_lits prob' learnt'
    Hwf Hperm Hupdate.
  destruct Hupdate as
    [[co [pre [post [Hprob [Hold [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hold [Hprob' Hlearnt']]]]]]].
  - subst prob prob' learnt'. rewrite <- Hold in Hperm.
    rewrite <- app_assoc in Hwf |- *.
    eapply db_wf_replace_lits__propagate_dbu;
      eassumption.
  - subst learnt prob' learnt'. rewrite <- Hold in Hperm.
    rewrite app_assoc in Hwf |- *.
    eapply db_wf_replace_lits__propagate_dbu;
      eassumption.
Qed.

Lemma db_pair_lits_update_prob_learnt__propagate_dbu :
  forall prob learnt p old_lits new_lits prob' learnt',
    prob_db prob -> learnt_db learnt ->
    db_pair_lits_update prob learnt p old_lits new_lits prob' learnt' ->
    prob_db prob' /\ learnt_db learnt'.
Proof.
  intros prob learnt p old_lits new_lits prob' learnt'
    Hprobdb Hlearntdb Hupdate.
  destruct Hupdate as
    [[co [pre [post [Hprob [Hold [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hold [Hprob' Hlearnt']]]]]]].
  - subst prob prob' learnt'. split.
    + eapply prob_db_replace_lits__propagate_dbu;
        eassumption.
    + exact Hlearntdb.
  - subst learnt prob' learnt'. split.
    + exact Hprobdb.
    + eapply learnt_db_replace_lits__propagate_dbu;
        eassumption.
Qed.

Lemma denote_obj_clause_obj_with_lits_perm__propagate_dbu :
  forall co new_lits,
    Permutation new_lits (co_lits co) ->
    Permutation (denote_obj (clause_obj_with_lits co new_lits))
                (denote_obj co).
Proof.
  intros co new_lits Hperm.
  unfold denote_obj, clause_obj_with_lits; cbn.
  apply lits_denote_perm. exact Hperm.
Qed.

(* A lookup at a different pointer passes through the replaced entry.
   Prefix and suffix membership are retained; the replaced-head case is
   impossible by the caller's distinct-pointer hypothesis. *)
Local Ltac msat_db_other_entry_membership Hin :=
  apply in_app_or in Hin; apply in_or_app;
  destruct Hin as [Hin | [Heq | Hin]];
    [ left; exact Hin
    | inversion Heq; subst; contradiction
    | right; simpl; right; exact Hin ].

Lemma db_pair_lits_update_other_iff__propagate_dbu :
  forall prob learnt p old_lits new_lits prob' learnt' q obj,
    db_pair_lits_update prob learnt p old_lits new_lits prob' learnt' ->
    q <> p ->
    (In (q, obj) (prob ++ learnt) <-> In (q, obj) (prob' ++ learnt')).
Proof.
  intros prob learnt p old_lits new_lits prob' learnt' q obj Hupdate Hneq.
  destruct Hupdate as
    [[co [pre [post [Hprob [Hold [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hold [Hprob' Hlearnt']]]]]]].
  - subst prob prob' learnt'.
    split; (intro Hin; apply in_app_or in Hin; apply in_or_app;
      destruct Hin as [Hin | Hin];
        [ left; msat_db_other_entry_membership Hin
        | right; exact Hin ]).
  - subst learnt prob' learnt'.
    split; (intro Hin; apply in_app_or in Hin; apply in_or_app;
      destruct Hin as [Hin | Hin];
        [ left; exact Hin
        | right; msat_db_other_entry_membership Hin ]).
Qed.

Lemma db_replace_lits_entry_bi__propagate_dbu :
  forall pre p co post new_lits,
    Permutation new_lits (co_lits co) ->
    (forall (q : Z) (obj' : clause_obj),
      In (q, obj') (pre ++ (p, clause_obj_with_lits co new_lits) :: post) ->
      exists obj : clause_obj,
        In (q, obj) (pre ++ (p, co) :: post) /\
        Permutation (denote_obj obj') (denote_obj obj)) /\
    (forall (q : Z) (obj : clause_obj),
      In (q, obj) (pre ++ (p, co) :: post) ->
      exists obj' : clause_obj,
        In (q, obj')
          (pre ++ (p, clause_obj_with_lits co new_lits) :: post) /\
        Permutation (denote_obj obj') (denote_obj obj)).
Proof.
  intros pre p co post new_lits Hperm. split.
  - intros q obj' Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | [Heq | Hin]].
    + exists obj'. split; [apply in_or_app; left; exact Hin|reflexivity].
    + inversion Heq; subst q obj'. exists co. split.
      * apply in_or_app. right. simpl. auto.
      * apply denote_obj_clause_obj_with_lits_perm__propagate_dbu.
        exact Hperm.
    + exists obj'. split.
      * apply in_or_app. right. simpl. right. exact Hin.
      * reflexivity.
  - intros q obj Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | [Heq | Hin]].
    + exists obj. split; [apply in_or_app; left; exact Hin|reflexivity].
    + inversion Heq; subst q obj.
      exists (clause_obj_with_lits co new_lits). split.
      * apply in_or_app. right. simpl. auto.
      * apply denote_obj_clause_obj_with_lits_perm__propagate_dbu.
        exact Hperm.
    + exists obj. split.
      * apply in_or_app. right. simpl. right. exact Hin.
      * reflexivity.
Qed.

Lemma db_matches_entries_transport__propagate_dbu :
  forall F old new,
    (forall q obj', In (q, obj') new ->
      exists obj, In (q, obj) old /\
        Permutation (denote_obj obj') (denote_obj obj)) ->
    Forall (fun c => exists c0, In c0 F /\ Permutation c c0)
      (db_clauses old) ->
    Forall (fun c => exists c0, In c0 F /\ Permutation c c0)
      (db_clauses new).
Proof.
  intros F old new Hforward Hold.
  rewrite Forall_forall in Hold |- *. intros C HC.
  apply db_clauses_in_inv in HC as [q [obj' [Hin Heq]]]. subst C.
  destruct (Hforward q obj' Hin) as [obj [Hinold Hperm]].
  specialize (Hold (denote_obj obj) (db_clauses_in old q obj Hinold)).
  destruct Hold as [C0 [HC0 Hold]]. exists C0. split; [exact HC0|].
  eapply Permutation_trans; eassumption.
Qed.

Lemma db_implied_entries_transport__propagate_dbu :
  forall F old new,
    (forall q obj', In (q, obj') new ->
      exists obj, In (q, obj) old /\
        Permutation (denote_obj obj') (denote_obj obj)) ->
    Forall (entails_clause F) (db_clauses old) ->
    Forall (entails_clause F) (db_clauses new).
Proof.
  intros F old new Hforward Hold.
  rewrite Forall_forall in Hold |- *. intros C HC.
  apply db_clauses_in_inv in HC as [q [obj' [Hin Heq]]]. subst C.
  destruct (Hforward q obj' Hin) as [obj [Hinold Hperm]].
  apply (entails_clause_perm F (denote_obj obj) (denote_obj obj')).
  - apply Permutation_sym. exact Hperm.
  - apply Hold. apply db_clauses_in with (p := q). exact Hinold.
Qed.

Lemma db_complete_entries_transport__propagate_dbu :
  forall F t old new,
    (forall q obj, In (q, obj) old ->
      exists obj', In (q, obj') new /\
        Permutation (denote_obj obj') (denote_obj obj)) ->
    (forall c, In c F ->
      (exists c', In c' (db_clauses old) /\ Permutation c' c) \/
      root_satisfied t c) ->
    forall c, In c F ->
      (exists c', In c' (db_clauses new) /\ Permutation c' c) \/
      root_satisfied t c.
Proof.
  intros F t old new Hreverse Hold c HC.
  destruct (Hold c HC) as [[Cold [Hinold Hpermold]] | Hroot].
  - left. apply db_clauses_in_inv in Hinold as [q [obj [Hin Heq]]].
    subst Cold.
    destruct (Hreverse q obj Hin) as [obj' [Hinnew Hpermnew]].
    exists (denote_obj obj'). split.
    + apply db_clauses_in with (p := q). exact Hinnew.
    + eapply Permutation_trans; eassumption.
  - right. exact Hroot.
Qed.

Lemma db_pair_lits_update_prob_entry_bi__propagate_dbu :
  forall prob learnt p old_lits new_lits prob' learnt',
    Permutation new_lits old_lits ->
    db_pair_lits_update prob learnt p old_lits new_lits prob' learnt' ->
    (forall q obj', In (q, obj') prob' ->
      exists obj, In (q, obj) prob /\
        Permutation (denote_obj obj') (denote_obj obj)) /\
    (forall q obj, In (q, obj) prob ->
      exists obj', In (q, obj') prob' /\
        Permutation (denote_obj obj') (denote_obj obj)).
Proof.
  intros prob learnt p old_lits new_lits prob' learnt' Hperm Hupdate.
  destruct Hupdate as
    [[co [pre [post [Hprob [Hold [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hold [Hprob' Hlearnt']]]]]]].
  - subst prob prob'. rewrite <- Hold in Hperm.
    apply db_replace_lits_entry_bi__propagate_dbu.
    exact Hperm.
  - subst prob'. split.
    + intros q obj Hin. exists obj. split; [exact Hin|reflexivity].
    + intros q obj Hin. exists obj. split; [exact Hin|reflexivity].
Qed.

Lemma db_pair_lits_update_learnt_entry_bi__propagate_dbu :
  forall prob learnt p old_lits new_lits prob' learnt',
    Permutation new_lits old_lits ->
    db_pair_lits_update prob learnt p old_lits new_lits prob' learnt' ->
    (forall q obj', In (q, obj') learnt' ->
      exists obj, In (q, obj) learnt /\
        Permutation (denote_obj obj') (denote_obj obj)) /\
    (forall q obj, In (q, obj) learnt ->
      exists obj', In (q, obj') learnt' /\
        Permutation (denote_obj obj') (denote_obj obj)).
Proof.
  intros prob learnt p old_lits new_lits prob' learnt' Hperm Hupdate.
  destruct Hupdate as
    [[co [pre [post [Hprob [Hold [Hprob' Hlearnt']]]]]]
    |[co [pre [post [Hlearnt [Hold [Hprob' Hlearnt']]]]]]].
  - subst learnt'. split.
    + intros q obj Hin. exists obj. split; [exact Hin|reflexivity].
    + intros q obj Hin. exists obj. split; [exact Hin|reflexivity].
  - subst learnt learnt'. rewrite <- Hold in Hperm.
    apply db_replace_lits_entry_bi__propagate_dbu.
    exact Hperm.
Qed.

(** * Installation contracts indexed by the native learned flag.
    The selector controls the parent vector, its capacity, the preserved
    opposite database, and the installed header tag. *)

(* Accessors retain each predicate's database spelling: [db_words] and
   [map fst] are convertible but symbolic matching distinguishes them. *)

(* Selectors use the native learned flag: zero selects problems, nonzero
   selects learned clauses. *)

Lemma sel_db_learnt   : forall M, solver_selected_db 1 M = ms_learnt M.      Proof. reflexivity. Qed.

Lemma sel_db_prob   : forall M, solver_selected_db 0 M = ms_prob M.        Proof. reflexivity. Qed.

Lemma sel_vec_learnt  : forall s, solver_selected_vec s 1 = &( s # "solver_t" ->ₛ "learnts").
Proof. reflexivity. Qed.

Lemma sel_vec_prob  : forall s, solver_selected_vec s 0 = &( s # "solver_t" ->ₛ "clauses").
Proof. reflexivity. Qed.

Lemma sel_learnt_learnt : solver_selected_is_learnt 1 = true.  Proof. reflexivity. Qed.

Lemma sel_learnt_prob : solver_selected_is_learnt 0 = false. Proof. reflexivity. Qed.

(* The complement -- what the FRAME keeps while clause_new works on the
   selected database.  `1 - sel` needs no new definition and reduces at both
   ends: 1-1 = 0 and 1-0 = 1. *)
Lemma sel_other_learnt : forall M, solver_selected_db (1 - 1) M = ms_prob M.   Proof. reflexivity. Qed.

Lemma sel_other_prob : forall M, solver_selected_db (1 - 0) M = ms_learnt M. Proof. reflexivity. Qed.

Lemma sel_other_vec_learnt : forall s, solver_selected_vec s (1 - 1) = &( s # "solver_t" ->ₛ "clauses").
Proof. reflexivity. Qed.

Lemma sel_other_vec_prob : forall s, solver_selected_vec s (1 - 0) = &( s # "solver_t" ->ₛ "learnts").
Proof. reflexivity. Qed.

(* The formula after installation: a learnt clause is entailed by F and does
   not extend it; a problem clause does. *)
Definition cn_F (F : cnf) (words : list Z) (sel : Z) : cnf :=
  if Z.eqb sel 0 then F ++ (lits_denote words :: nil) else F.

Lemma cn_F_learnt : forall F w, cn_F F w 1 = F.
Proof. reflexivity. Qed.

Lemma cn_F_prob : forall F w, cn_F F w 0 = F ++ (lits_denote w :: nil).
Proof. reflexivity. Qed.

Definition clause_new_vecs_frame_gen
    (s : Z) (M : msolver) (sel : Z) : Assertion :=
  Vecp.rep (solver_selected_vec s (1 - sel))
           (map fst (solver_selected_db (1 - sel) M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
           (ms_model M).

Definition clause_new_frame_at_gen
    (s : Z) (M : msolver) (lvl : Z) (sel : Z) : Assertion :=
  EX act asg opos rsn trl tgs : Z,
    clause_new_scalars_frame s M ** solver_fp_rep s M **
    clause_new_vecs_frame_gen s M sel **
    clause_new_ptrs_frame s M act asg opos rsn lvl trl tgs **
    solver_var_arrays_rep M act asg opos rsn lvl tgs **
    solver_trail_array_rep M trl **
    clause_db_rep (solver_selected_db (1 - sel) M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

Lemma clause_new_frame_at_gen_learnt :
  forall s M lvl, clause_new_frame_at_gen s M lvl 1 = clause_new_frame_at s M lvl.
Proof. reflexivity. Qed.

(* Layer 3.  Transaction remainder.                                        *)

Definition clause_new_transaction_rest_at_gen
    (s wl i0 i1 : Z) (M : msolver) (lvl : Z) (sel : Z) : Assertion :=
  solver_wlists_handle s wl **
  VecpArray.missing2 wl i0 i1 (2 * ms_size M) (ms_wm M) **
  clause_new_frame_at_gen s M lvl sel.

(* Layer 4.  Staging.                                                      *)

(* Entry uses a pending certificate: the problem clause need not yet be
   in [F]. The postcondition adds it to [F] and supplies membership. *)

Definition problem_clause_pending_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) : Prop :=
  2 <= Zlength words /\ Forall (lit_wf_c n) words /\
  NoDup (map lit_var_c words) /\
  Forall (fun l => Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0) words.

Definition clause_install_pending_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) (learnt : bool) : Prop :=
  if learnt then record_clause_cert n F M words
            else problem_clause_pending_cert n F M words.

(** The named watch-list address connects the live table to its unused growth
    tail. *)

Definition solver_rep_levels_wl_at (s : Z) (M : msolver) (wl lvl : Z) : Assertion :=
  “ solver_shape M ” &&
  ((EX act asg opos rsn trl tgs : Z,
      solver_nonlevel_rep_at s M wl act asg opos rsn trl tgs) **
   solver_levels_slice_at s M lvl).
