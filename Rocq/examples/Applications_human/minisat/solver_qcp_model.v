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
(* Load the reals and Flocq modules; [Binary] is imported below.
   The additional local imports used by [MSatFloatFacts] are in
   [solver_qcp_model.v], inside that module. *)
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

(* Solver representations, state operations, and facts required by the proof tactics. *)

Notation "'UINT64_MAX'" := (18446744073709551615).

(** The operation-closed activity domain.  Both IEEE zero constructors are
    admitted: [-0] compares equal to zero and remains a safe zero under the
    positive multiplications and divisions used by the activity code.  Apart
    from signed zero, only positive finite values and +infinity are admitted;
    NaNs and negative nonzero values are excluded. *)
Definition msat_fp32_nonnegative (x : fp32) : Prop :=
  match x with
  | Binary.B754_zero _ _ _ => True
  | Binary.B754_infinity _ _ false => True
  | Binary.B754_finite _ _ false _ _ _ => True
  | _ => False
  end.

(** Positive finite factors are used only as multipliers/divisors. *)
Definition msat_fp32_positive_finite (x : fp32) : Prop :=
  Binary.is_finite 24 128 x = true /\
  Binary.Bsign 24 128 x = false /\
  x <> Binary.B754_zero 24 128 false.

(** [solver_reducedb] computes its limit even for an empty learned database.
    That 0/0 result is never compared; orderedness is required only when a
    learned clause can actually reach the comparison. *)
Definition msat_fp32_count_limit (count : Z) (x : fp32) : Prop :=
  0 < count -> msat_fp32_nonnegative x.

(** A fixed default makes floating-array reads stable under symbolic
    matching.  In-range [Znth] values are independent of this default. *)
Definition msat_fp64_zero : fp64 := Binary.B754_zero 53 1024 false.

(* ================= SECTION msat_s1_semantics ================= *)

(** Representation-independent SAT and CDCL mathematics is re-exported from
    the two shared libraries.  This case library starts with MiniSat's packed
    encoding and concrete solver representation. *)
(* ================= SECTION msat_s2_bridge ================= *)

(** * S2 -- packed-encoding bridges.

    MiniSat stores a literal as a packed integer [l = 2*var + sign], an
    lbool as one of [-1,0,1], and a watcher word either as a clause
    pointer (even) or as a tagged literal [2*lit+1] (odd).  This section
    is the dictionary between those machine words and the S1 pure layer. *)

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

(* Representation-independent live CDCL carriers are owned by [cdcl_shared_lib].
   What MiniSat adds on top of them is below: the local trail, the mutable
   database, and the watched-frontier bridges. *)

(* ================= SECTION msat_s4_trail ================= *)

(** * S4 -- the concrete MiniSat trail, its projection to the S3 view, and
      TRAIL-IMPLIED.

    Everything here is a ghost mirror of the five pieces of solver state that
    together make up the assignment: [s->assigns], [s->levels], [s->trail],
    [s->trail_lim] and [s->qhead].  The section
    provides

      - [mtrail] + [mtrail_wf]        : the concrete state and its shape,
      - [view_of]                     : the projection to S3's [cdcl_view],
      - [mt_enqueue]/[mt_decide]/[mt_cancel]
                                      : the three state transitions that
                                        [enqueue], [assume], and
                                        [solver_canceluntil] perform, with [mtrail_wf]
                                        preservation and the memory-to-view
                                        bridges,
      - [trail_implied]               : the TRAIL-IMPLIED property,
                                        with its four maintenance lemmas and
                                        the UNSAT endgame that reads it off.

    Ranks.  [assignment_rank] is realised by concrete trail position.  The
    relational [assigns_one] bridge is the contract-level abstraction of an
    enqueue or decision step. *)

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

(** ----- first occurrence of a variable on a list of packed literals ----- *)

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

(** [mtrail_wf n t] is the memory-shape invariant of the trail:
    lbool cells, trail literals in range / variable-distinct / true, a
    strictly increasing [trail_lim] pointing inside the trail, [levels]
    agreeing with the boundary count on assigned variables, and "assigned
    exactly when on the trail". *)
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

(** Every decision boundary sits at or below the propagation frontier.
    Therefore the unpropagated trail suffix belongs to the current level;
    this supplies the level facts used by binary reasons and cancellation. *)
Definition prop_level (t : mtrail) : Prop :=
  Forall (fun b => b <= mt_qhead t) (mt_lim t).

Lemma trail_var_range : forall n t v,
  mtrail_wf n t -> In v (map lit_var_c (mt_trail t)) -> 0 <= v < n.
Proof.
  intros n t v Hwf Hin. apply in_map_iff in Hin. destruct Hin as [x [<- Hx]].
  apply (lit_var_c_in_range n).
  pose proof (mtw_trail_lits Hwf) as HF. rewrite Forall_forall in HF. auto.
Qed.

Lemma lim_lt_trail : forall n t k,
  mtrail_wf n t -> 0 <= k < Zlength (mt_lim t) ->
  0 <= Znth k (mt_lim t) 0 < Zlength (mt_trail t).
Proof.
  intros n t k Hwf Hk.
  exact (Forall_Znth_elim _ _ _ 0 k (mtw_lim_range Hwf) Hk).
Qed.

(** ===== C. the projection to S3's [cdcl_view] ===== *)

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

(** The single fact that ties the memory picture to the view: a variable is
    assigned exactly when it sits on the trail. *)
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

(** The decision literals of the levels below [d]: [trail[trail_lim[k]]]. *)
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

(** The arithmetic shard of [solver_analyze]'s tagged-reason step
    The C branches on

        if (levels[lit_var(q)] == solver_dlevel(s)) cnt++;
        else                                        veci_push(learnt,q);

    inside a guard [levels[lit_var(q)] > 0], so the [else] arm's
    real condition is [0 < lev /\ lev <> cur] -- which admits [lev > cur] as
    well as [0 < lev < cur].  Given the [binary_reason_same_level]-shaped
    premise (the tag literal's variable has the same level as the variable it
    justifies) and [level v = cur], the tag variable's level is [cur] on the
    nose, so the whole [else] arm is unreachable.  Stated as one lemma the
    annotation can cite for the dead push. *)

(** Projected assignment steps use the shared relation [assigns_one].
    [mtrail_wf_pushed] represents the short interval between extending
    [trail_lim] and enqueueing the decision.  No record equality with an
    abstract enqueue constructor is claimed because this projection defines
    assignment rank by concrete trail position. *)

(* ================= SECTION msat_s5_watch ================= *)

(** * S5 -- the watched-literal layer.

    [wmap_exact] records every watcher occurrence with multiplicity.
    [minisat_watch_frontier] records the processed/unprocessed frontier for
    each clause occurrence, while its focused scan carrier accounts for the
    one list currently being rewritten.  At [qhead = qtail], these facts and
    a total assignment imply that every live database clause is satisfied.
    The definitions use concrete packed literals and ghost lists so they can
    be tied directly to the separation-logic representation. *)

(** ** Generic list plumbing used below. *)

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

(** Change only a clause object's physical literal order.  Propagation uses
    this operation when it normalizes the false watch into slot 1; learntness,
    pointer identity, and every other database entry remain unchanged. *)
Definition clause_obj_with_lits (co : clause_obj) (lits : list Z) : clause_obj :=
  {| co_lits := lits; co_learnt := co_learnt co |}.

Definition denote_obj (co : clause_obj) : clause := lits_denote (co_lits co).

(** [dbmap] is [s->clauses ++ s->learnts]: an association list from clause
    pointer to the object it points at. *)
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

(** ** INV-W1: watcher-map exactness.

    The words that clause entry [e] is expected to contribute to watch
    list [l].  A clause of size >= 3 contributes its own pointer to the
    lists indexed by the negations of its two watched slots; a binary
    clause contributes the *tag of the other literal* instead (the real
    object is never reachable from a watch list). *)

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

(** A focused scan must retain the identity and multiplicity of the database
    occurrence that emitted each physical watcher word.  Pairing the exact
    occurrence with its word distinguishes equal binary tags contributed by
    different clauses without introducing a second owner model. *)
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

(** Agreement between the partial view used by S1/S2 and the total one. *)

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

(** ** The [solver_propagate] inner-scan carrier.

    While scanning [wlists[p]] the loop maintains three multisets: the
    entries already written back at [j] ([kept]), the entries that have
    been re-attached to another watch list ([moved], the ones upstream's
    [vecp_push]/[goto next] step moves), and the entries not yet inspected
    ([rest], the range [i, end)).  On exit the list is resized to [kept]
    (upstream's [vecp_resize(ws, j - vecp_begin(ws))]), and the [moved]
    words have been
    pushed elsewhere -- so [wmap_move] closes the INV-W1 obligation with
    [kept ++ moved] as the difference witness. *)
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

(** [order_select] sets [orderpos[next] := -1]; this is legal exactly
    because it runs at a propagation fixpoint, so [next], if assigned at all,
    is assigned below [qhead]. *)

(** ----- the pop/assume transient ----- *)

(** Between [order_select]'s pop ([orderpos[next] = -1] is set
    BEFORE the assignment test, and the returned variable is UNASSIGNED)
    and [solver_propagate]'s first [qhead++], plain [heap_covers]
    is false for exactly one variable.  This is the transient: coverage
    for every variable EXCEPT the distinguished [v0], which may sit
    popped-but-unassigned (after [order_select]) or assigned with its
    trail index at [qhead] (after [assume], before the first dequeue). *)
Definition heap_covers_except (n : Z) (h : mheap)
    (assigns trail : list Z) (qhead : Z) (v0 : Z) : Prop :=
  forall v, 0 <= v < n -> v <> v0 ->
    Znth v (mh_orderpos h) (-1) = -1 ->
    Znth v assigns 0 <> 0 /\
    (exists i, 0 <= i < qhead /\ lit_var_c (Znth i trail 0) = v).

(** ----- [list_without_Znth] toolbox ----- *)

(** hoisted from the propagation section: needed here by
    [list_without_Znth_perm] / [replace_Znth_split] *)
Lemma list_Znth_split : forall {A : Type} (default : A) (xs : list A) i,
  0 <= i < Zlength xs ->
  xs = sublist 0 i xs ++ Znth i xs default ::
       sublist (i + 1) (Zlength xs) xs.
Proof.
  intros A default xs i Hi.
  rewrite <- (sublist_self xs (Zlength xs) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength xs) i xs) by lia.
  rewrite (sublist_split i (Zlength xs) (i + 1) xs) by lia.
  rewrite (sublist_single default i xs) by lia. simpl. reflexivity.
Qed.

Definition heap_of_lists (order orderpos : list Z) : mheap :=
  {| mh_heap := order; mh_orderpos := orderpos |}.

(** ----- the random seed ----- *)

Definition seed_ok (s : Z) : Prop := 1 <= s <= 2147483646.

(** [heap_covers_except] is the transient after popping one decision candidate;
    enqueue and the first propagation dequeue restore full coverage. *)

(* ================= SECTION msat_s8_rep ================= *)

(** * S8 -- the separation-logic layer.

    This section owns every spatial predicate the MiniSat annotations name:
    the clause-object family frozen by [minisat_qcp_compat.h], the two vector
    families of [vec_qcp.h], the watcher-list table, the clause database, and
    the one whole-solver bundle.

    ** How [A::B] names resolve

    The QCP annotation surface writes namespaced predicates as [A::B]; the
    frontend resolves that to the Coq qualified name [A.B], i.e. member [B] of
    Coq module [A].  Evidence: [QCP_demos_LLM/int_array_def.h] declares
    [(IntArray::full : Z -> Z -> list Z -> Assertion)] and the Coq side has
    [Module IntArray := ArrayLib (StoreIntAsElement)] in
    [SeparationLogic/ArrayLib.v], whose functor body (ArrayLibCore.v) defines
    [full], [seg], [undef_seg], [undef_full], [missing_i], [seg_shape], ... ;
    [Applications_human/CDCL/CDCL_qcp_def.h] binds [PtrArray::undef_seg] the same way
    against [Module PtrArray := ArrayLib (StorePtrAsElement)].

    Consequence for this section:

    - [IntArray::seg / undef_seg / undef_full] and
      [PtrArray::seg / undef_seg / undef_full] -- REUSED verbatim from the
      framework ([SimpleC.SL.SeparationLogic] re-exports [ArrayLib]).  Nothing
      is defined here for them; [minisat_qcp_compat.h] can name them directly,
      exactly as qcpsat does.  The same holds for [CharArray] (the [lbool]
      arrays [assigns] and [tags]) and [DoubleArray] (the [activity] array).
    - [MiniSatClause::undef / rep / owned] are new, so this file opens
      [Module MiniSatClause] and defines [undef], [rep], [owned] inside it.

    ** Addressing idiom

    Struct fields go through the [&( p # "tag" ->ₛ "field")] notation, whose
    denotation is an opaque address function -- the same idiom qcpsat uses for
    [var_data] / [clause_data] / [sat_data].  Struct tags are the C tag names:
    [clause_t], [veci_t], [vecp_t], [solver_t], [stats_t].  The flexible array
    member [lit lits[0]] is addressed as the *field address* of ["lits"], which
    is precisely the post-header address, and the cells are then an ordinary
    [IntArray] segment there -- no byte offset is hardcoded anywhere in this
    file.  Array-of-struct stride likewise uses the exact alias-size term
    emitted for native [vecp] indexing, [sizeof("vecp_t")], rather than a
    literal 16. *)

(** ** The clause object.

    C layout:

    << struct clause_t { int size_learnt; float activity; lit lits[0]; }; >>

    with [clause_size c = c->size_learnt >> 1] and
    [clause_learnt c = c->size_learnt & 1], i.e. the header word packs
    [2 * size + learnt].

    [activity] carries no SAT-semantic content (it only drives heuristic
    ordering), but learned activities do carry the operation-closed IEEE fact
    [msat_fp32_nonnegative].  This excludes NaNs and negative values while
    admitting +0 and +infinity, exactly the domain preserved by MiniSat's
    add/multiply/divide update paths.  Problem-clause activity remains
    undefined, and [rep |-- owned] still forgets the initialized value.

    [clause_new] writes [c->activity = 0.0f] only in the learnt branch, and
    [s->binary] is built with only [size_learnt] written.  A problem clause's
    activity cell is therefore uninitialised.  [activity_state] follows that
    learnt-dependent behavior, using the
    framework's single-cell undefined-float idiom [x # Float |->_]
    ([undef_store_float] in [SeparationLogic/CommonAssertion.v]) -- the
    same atom [ArrayLib]'s [undef_seg] is built from, so no new mechanism is
    invented here. *)

Definition clause_hdr_addr (c : Z) : Z := &( c # "clause_t" ->ₛ "size_learnt").

Definition clause_act_addr (c : Z) : Z := &( c # "clause_t" ->ₛ "activity").

Definition clause_lits_addr (c : Z) : Z := &( c # "clause_t" ->ₛ "lits").

(** A stable carrier for the address returned by [clause_begin].  The C
    symbolic executor deliberately keeps this relation opaque so successive
    calls can share the same array base without rewriting spatial addresses
    through a pure pointer equality. *)
Definition clause_lits_pointer (c p : Z) : Prop :=
  p = clause_lits_addr c.

(** The packed header word. *)
Definition clause_hdr_word (learnt : bool) (size : Z) : Z :=
  2 * size + (if learnt then 1 else 0).

(** The activity cell: written iff the clause is learnt. *)
Definition activity_state (c : Z) (learnt : bool) : Assertion :=
  if learnt
  then EX a : fp32,
         “ msat_fp32_nonnegative a ” &&
         clause_act_addr c # Float |-> a
  else clause_act_addr c # Float |->_.

Module MiniSatClause.

  (** Freshly allocated, nothing written yet: all three regions undefined.
      This is the postcondition of [minisat_clause_alloc]. *)
  Definition undef (c size : Z) : Assertion :=
    “ 0 <= size /\ 0 < c /\ c mod 2 = 0 ” &&
    (clause_hdr_addr c # Int |->_ **
     clause_act_addr c # Float |->_ **
     IntArray.undef_seg (clause_lits_addr c) 0 size).

  (** A fully initialised clause object. *)
  Definition rep (c : Z) (learnt : bool) (lits : list Z) : Assertion :=
    “ 0 <= Zlength lits /\ 0 < c /\ c mod 2 = 0 ” &&
    (clause_hdr_addr c # Int |-> clause_hdr_word learnt (Zlength lits) **
     activity_state c learnt **
     IntArray.seg (clause_lits_addr c) 0 (Zlength lits) lits).

  (** What [minisat_clause_free] consumes: the three regions, contents
      forgotten.  Both [undef] and [rep] entail it. *)
  Definition owned (c size : Z) : Assertion :=
    “ 0 <= size /\ 0 < c /\ c mod 2 = 0 ” &&
    (clause_hdr_addr c # Int |->_ **
     clause_act_addr c # Float |->_ **
     IntArray.undef_seg (clause_lits_addr c) 0 size).

End MiniSatClause.

(** ** The two vector families ([vec_qcp.h]).

    << struct veci_t { int size; int cap; int*   ptr; }; >>
    << struct vecp_t { int size; int cap; void** ptr; }; >>

    Both are three header fields plus a heap block of [cap] cells of which the
    first [size] are live.  The [_at] variants expose the data pointer (the
    [veci_begin] / [vecp_begin] result); the plain ones hide it.  [cap > 0] is
    an invariant of the C code: [veci_new] starts at 4 and [veci_push] only
    grows. *)

Definition veci_size_addr (v : Z) : Z := &( v # "veci_t" ->ₛ "size").

Definition veci_cap_addr  (v : Z) : Z := &( v # "veci_t" ->ₛ "cap").

Definition veci_ptr_addr  (v : Z) : Z := &( v # "veci_t" ->ₛ "ptr").

Definition vecp_size_addr (v : Z) : Z := &( v # "vecp_t" ->ₛ "size").

Definition vecp_cap_addr  (v : Z) : Z := &( v # "vecp_t" ->ₛ "cap").

Definition vecp_ptr_addr  (v : Z) : Z := &( v # "vecp_t" ->ₛ "ptr").

Definition veci_rep_at (v p : Z) (l : list Z) (cap : Z) : Assertion :=
  “ 0 <= Zlength l <= cap /\ 0 < cap <= INT_MAX ” &&
  (veci_size_addr v # Int |-> Zlength l **
   veci_cap_addr v # Int |-> cap **
   veci_ptr_addr v # Ptr |-> p **
   IntArray.seg p 0 (Zlength l) l **
   IntArray.undef_seg p (Zlength l) cap).

Definition veci_rep (v : Z) (l : list Z) (cap : Z) : Assertion :=
  EX p : Z, veci_rep_at v p l cap.

Definition vecp_rep_at (v p : Z) (l : list Z) (cap : Z) : Assertion :=
  “ 0 <= Zlength l <= cap /\ 0 < cap <= INT_MAX ” &&
  (vecp_size_addr v # Int |-> Zlength l **
   vecp_cap_addr v # Int |-> cap **
   vecp_ptr_addr v # Ptr |-> p **
   PtrArray.seg p 0 (Zlength l) l **
   PtrArray.undef_seg p (Zlength l) cap).

Definition vecp_rep (v : Z) (l : list Z) (cap : Z) : Assertion :=
  EX p : Z, vecp_rep_at v p l cap.

Lemma veci_rep_at_rep : forall v p l cap,
  veci_rep_at v p l cap |-- veci_rep v l cap.
Proof. intros. unfold veci_rep. Exists p. entailer_with lia. Qed.

Definition clause_watch_word
    (c : Z) (lits : list Z) (other : Z) : Z :=
  if Z.ltb 2 (Zlength lits) then c else tag_of_lit other.

(** ** The watcher table [s->wlists].

    [s->wlists] is an array of [2n] in-place [vecp] structs (it is
    [realloc]'d as [sizeof(vecp) * cap * 2] and read as [&s->wlists[l]]).
    QCP translates both expressions with the alias-size term
    [sizeof("vecp_t")]; using that exact term keeps the accessor contract and
    every representation/focus carrier definitionally aligned. *)

Definition vecp_slot (base i : Z) : Z := base + i * sizeof("vecp_t").

Fixpoint wlists_rep_from (base i : Z) (wm : list (list Z)) (caps : list Z)
  : Assertion :=
  match wm with
  | nil => emp
  | w :: wm' =>
      vecp_rep (vecp_slot base i) w (hd 1 caps) **
      wlists_rep_from base (i + 1) wm' (tl caps)
  end.

Definition wlists_rep (base n : Z) (wm : wmap) (caps : list Z) : Assertion :=
  “ Zlength wm = 2 * n /\ Zlength caps = 2 * n ” &&
  wlists_rep_from base 0 wm caps.

(** ** The clause database.

    [dbmap] (S5) is [s->clauses ++ s->learnts] as an association list from the
    clause pointer to its ghost object; [clause_db_rep] is the iterated
    separating conjunction of [MiniSatClause::rep] over it.  Ownership of the
    objects is therefore separate from ownership of the two [vecp]s that hold
    the pointers -- which is exactly what [reduceDB] needs (it drops pointers
    from [learnts] and frees the objects in two independent steps). *)

Fixpoint clause_db_rep (entries : dbmap) : Assertion :=
  match entries with
  | nil => emp
  | e :: rest =>
      MiniSatClause.rep (fst e) (co_learnt (snd e)) (co_lits (snd e)) **
      clause_db_rep rest
  end.

(** Every entry in [s->learnts] carries an initialized activity cell.  This
    pure tag is the bridge from membership in the pointer vector to the
    learned-clause accessor contracts. *)
Definition learnt_db (entries : dbmap) : Prop :=
  Forall (fun e => co_learnt (snd e) = true) entries.

(** The dual tag fact for [s->clauses].  Without it nothing separates the
    two halves of [msolver_db] by tag, and a goal that knows only
    "[c] is in [prob ++ learnt]" plus "[c]'s header word says learnt" can
    never conclude "[c] is in [learnt]" -- exactly the gap recorded as
    [solver_analyze_safety_wit_37_learnt].  It is also what a problem-clause installation must
    preserve, since the object it appends carries [co_learnt = false]. *)
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
       clause_act_addr p # Float |-> a **
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
   clause_act_addr p # Float |-> activity **
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
    activity_state p is_learnt **
    clause_db_pair_remainder prob learnt p is_learnt lits.

Lemma clause_db_rep_app_intro : forall db1 db2,
  clause_db_rep db1 ** clause_db_rep db2 |-- clause_db_rep (db1 ++ db2).
Proof.
  induction db1 as [| e db1 IH]; intros db2; simpl.
  - entailer_with lia.
  - sep_apply (IH db2). entailer_with lia.
Qed.

(** ** The [stats] block.

    [struct stats_t] is eleven [uint64] counters.  Nothing in the development
    depends on their values, but the memory has to be owned; they are carried
    as an eleven-element list read positionally. *)

(** The eleven [stats] counters, named.  [ms_stats M] and the bare [stats]
    ghosts that cross [clause_remove]'s contract are both [list Z], so the
    accessors are list-level: one spelling serves the annotations, the
    strategy rules and every predicate body below.  Index order is
    the declaration order of [struct stats_t] in solver_qcp.h. *)
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

(** ** The whole-solver ghost record.

    One record holding every ghost list the solver bundle needs, in four
    layers: core / db / watch / heur.  The trail core is S4's [mtrail], so
    [mtrail_wf] and [view_of] apply to [ms_core] directly; the reason array is
    kept as raw machine WORDS ([ms_reason_words]) with the ghost clause map
    ([ms_reason_of]) alongside, because MiniSat stores [clause_from_lit l =
    2*l+1] -- an odd integer, not an address -- in [reasons[v]] for binary
    reasons.  Relating the two is a pure obligation and belongs to S9's
    invariant, not to the spatial layer. *)

Record msolver := {
  (* --- sizes ------------------------------------------------------------ *)
  ms_size        : Z;                  (* s->size : number of variables      *)
  ms_cap         : Z;                  (* s->cap  : varmap capacity          *)
  ms_qtail       : Z;                  (* s->qtail                           *)
  ms_capacity_pending_qhead : Z;       (* saved root propagation cursor      *)
  ms_capacity_root_propagation_pending : Z; (* public retry flag, 0 or 1     *)
  (* --- assignment core (S4) --------------------------------------------- *)
  ms_core        : mtrail;             (* assigns/levels/trail/trail_lim/qhead *)
  ms_root_level  : Z;                  (* s->root_level                      *)
  (* --- reasons ----------------------------------------------------------- *)
  ms_reason_words : list Z;            (* s->reasons, raw words              *)
  ms_reason_of   : Z -> option clause; (* ghost reason clauses (S3 view)     *)
  (* --- clause database ---------------------------------------------------- *)
  ms_prob        : dbmap;              (* s->clauses                         *)
  ms_learnt      : dbmap;              (* s->learnts                         *)
  ms_prob_cap    : Z;
  ms_learnt_cap  : Z;
  ms_binary      : Z;                  (* s->binary, the temp binary clause  *)
  ms_binary_lits : list Z;
  (* --- watcher table ------------------------------------------------------ *)
  ms_wm          : wmap;               (* s->wlists contents                 *)
  ms_wcaps       : list Z;             (* per-list capacities                *)
  (* --- heuristics --------------------------------------------------------- *)
  ms_activity    : list fp64;          (* s->activity                        *)
  ms_orderpos    : list Z;             (* s->orderpos                        *)
  ms_order       : list Z;             (* s->order (the heap array)          *)
  ms_order_cap   : Z;
  ms_lim_cap     : Z;                  (* capacity of s->trail_lim           *)
  ms_model       : list Z;
  ms_model_cap   : Z;
  ms_tags        : list Z;             (* s->tags                            *)
  ms_tagged      : list Z;
  ms_tagged_cap  : Z;
  ms_stack       : list Z;
  ms_stack_cap   : Z;
  (* --- floating-point knobs (shape only) ---------------------------------- *)
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

(** The ghost state seen after restoring a suspended public retry.  The C
    object publishes [qhead = qtail] while it is outside [solver_solve]; on
    re-entry it copies [capacity_pending_qhead] back to [qhead] and clears the
    flag before calling propagation.  This projection changes exactly those
    two logical fields and is therefore usable for reasoning about the
    pending work without claiming pointer identity for any vector. *)
(* Propagation updates share the unchanged solver fields. The arguments name every component this lane may replace. *)
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
    (wcaps : list Z)
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
  ms_prob_cap := ms_prob_cap M;
  ms_learnt_cap := ms_learnt_cap M;
  ms_binary := ms_binary M;
  ms_binary_lits := binary_lits;
  ms_wm := wm;
  ms_wcaps := wcaps;
  ms_activity := ms_activity M;
  ms_orderpos := ms_orderpos M;
  ms_order := ms_order M;
  ms_order_cap := ms_order_cap M;
  ms_lim_cap := ms_lim_cap M;
  ms_model := ms_model M;
  ms_model_cap := ms_model_cap M;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M;
  ms_tagged_cap := ms_tagged_cap M;
  ms_stack := ms_stack M;
  ms_stack_cap := ms_stack_cap M;
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
    propagation watcher vector is open.  It is used only by the six scan
    transitions below; all solver fields outside that source footprint are
    inherited from [M]. *)
Definition msolver_propagation_overlay
    (M : msolver) (core : mtrail) (qtail : Z)
    (reason_words : list Z) (reason_of : Z -> option clause)
    (prob learnt : dbmap) (binary_lits : list Z)
    (wm : wmap) (wcaps stats : list Z) : msolver :=
  msolver_propagation_update M (ms_cap M) (qtail) (ms_capacity_root_propagation_pending M) (core) (reason_words)
    (reason_of) (prob) (learnt) (binary_lits) (wm) (wcaps) (ms_simpdb_props M) (stats).

(** Recording has one additional enqueue shape that propagation never uses:
    a unary learned consequence is installed with the raw null reason and the
    ghost reason map entry [None].  The caller proves the head is fresh, so
    this projection deliberately contains only the fresh arm. *)
Definition msolver_enqueue_fresh
    (M : msolver) (l reason_word : Z) (reason_opt : option clause) : msolver :=
  let v := lit_var_c l in
  msolver_propagation_overlay M
    (mt_enqueue (ms_core M) l) (ms_qtail M + 1)
    (replace_Znth v reason_word (ms_reason_words M))
    (sat_function_update (ms_reason_of M) v reason_opt)
    (ms_prob M) (ms_learnt M) (ms_binary_lits M)
    (ms_wm M) (ms_wcaps M) (ms_stats M).

(** Exact solver state after [assume]: one decision boundary and literal are
    appended, the fresh variable receives a null reason, and only the
    trail-limit vector capacity may change. *)
Definition msolver_assume
    (M : msolver) (l lim_cap : Z) : msolver := {|
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
  ms_prob_cap := ms_prob_cap M; ms_learnt_cap := ms_learnt_cap M;
  ms_binary := ms_binary M; ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M; ms_wcaps := ms_wcaps M;
  ms_activity := ms_activity M; ms_orderpos := ms_orderpos M;
  ms_order := ms_order M; ms_order_cap := ms_order_cap M;
  ms_lim_cap := lim_cap; ms_model := ms_model M;
  ms_model_cap := ms_model_cap M; ms_tags := ms_tags M;
  ms_tagged := ms_tagged M; ms_tagged_cap := ms_tagged_cap M;
  ms_stack := ms_stack M; ms_stack_cap := ms_stack_cap M;
  ms_var_inc := ms_var_inc M; ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M; ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M; ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M; ms_stats := ms_stats M
|}.

Definition msolver_propagation_db_wmap_update
    (M : msolver) (prob learnt : dbmap) (wm : wmap) (wcaps : list Z)
    : msolver :=
  msolver_propagation_overlay M
    (ms_core M) (ms_qtail M) (ms_reason_words M) (ms_reason_of M)
    prob learnt (ms_binary_lits M) wm wcaps (ms_stats M).

(** Remove exactly one database pointer while retaining every component that
    clause deletion does not mutate.  The caller supplies the watcher table
    and statistics produced by [clause_remove].  This projection is shared by
    learned-database reduction and level-zero simplification. *)
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
    (ms_binary_lits M) wm (ms_wcaps M) stats.

(** Common exact projection for cancellation and its caller's subsequent
    [root_level] reset.  Everything outside the trail/reason/heap/root
    footprint is inherited definitionally. *)
Definition msolver_core_heap_update
    (M : msolver) (core : mtrail) (qtail : Z)
    (reason_words : list Z) (reason_of : Z -> option clause)
    (orderpos order : list Z) (order_cap root : Z) : msolver := {|
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
  ms_prob_cap       := ms_prob_cap M;
  ms_learnt_cap     := ms_learnt_cap M;
  ms_binary         := ms_binary M;
  ms_binary_lits    := ms_binary_lits M;
  ms_wm             := ms_wm M;
  ms_wcaps          := ms_wcaps M;
  ms_activity       := ms_activity M;
  ms_orderpos       := orderpos;
  ms_order          := order;
  ms_order_cap      := order_cap;
  ms_lim_cap        := ms_lim_cap M;
  ms_model          := ms_model M;
  ms_model_cap      := ms_model_cap M;
  ms_tags           := ms_tags M;
  ms_tagged         := ms_tagged M;
  ms_tagged_cap     := ms_tagged_cap M;
  ms_stack          := ms_stack M;
  ms_stack_cap      := ms_stack_cap M;
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
    (order_cap root : Z)
    : msolver :=
  let bound := Znth level (mt_lim (ms_core M)) 0 in
  msolver_core_heap_update M (mt_cancel (ms_core M) level) bound
    (clear_vars (zdrop bound (mt_trail (ms_core M))) (ms_reason_words M))
    (clear_reason_fun (zdrop bound (mt_trail (ms_core M))) (ms_reason_of M))
    orderpos order order_cap root.

(** Clause allocation can grow only the learnt parent vector and the two
    selected watcher vectors before it installs any logical object. *)
(* Clause capacity updates preserve every logical component of the solver. *)
Definition msolver_capacity_update (M : msolver)
    (prob_cap : Z)
    (learnt_cap : Z)
    (wcaps : list Z) : msolver := {|
  ms_size := ms_size M;
  ms_cap := ms_cap M;
  ms_qtail := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending := ms_capacity_root_propagation_pending M;
  ms_core := ms_core M;
  ms_root_level := ms_root_level M;
  ms_reason_words := ms_reason_words M;
  ms_reason_of := ms_reason_of M;
  ms_prob := ms_prob M;
  ms_learnt := ms_learnt M;
  ms_prob_cap := prob_cap;
  ms_learnt_cap := learnt_cap;
  ms_binary := ms_binary M;
  ms_binary_lits := ms_binary_lits M;
  ms_wm := ms_wm M;
  ms_wcaps := wcaps;
  ms_activity := ms_activity M;
  ms_orderpos := ms_orderpos M;
  ms_order := ms_order M;
  ms_order_cap := ms_order_cap M;
  ms_lim_cap := ms_lim_cap M;
  ms_model := ms_model M;
  ms_model_cap := ms_model_cap M;
  ms_tags := ms_tags M;
  ms_tagged := ms_tagged M;
  ms_tagged_cap := ms_tagged_cap M;
  ms_stack := ms_stack M;
  ms_stack_cap := ms_stack_cap M;
  ms_var_inc := ms_var_inc M;
  ms_var_decay := ms_var_decay M;
  ms_cla_inc := ms_cla_inc M;
  ms_cla_decay := ms_cla_decay M;
  ms_random_seed := ms_random_seed M;
  ms_progress := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props := ms_simpdb_props M;
  ms_verbosity := ms_verbosity M;
  ms_stats := ms_stats M
|}.

Definition msolver_with_clause_caps
    (M : msolver) (learnt_cap : Z) (wcaps : list Z) : msolver :=
  msolver_capacity_update M (ms_prob_cap M) (learnt_cap) (wcaps).

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
    (ms_binary_lits M) (clause_new_watch_map M c words)
    (ms_wcaps M) (ms_stats M).

(** The purely dimensional facts the spatial bundle itself guarantees.  The
    semantic invariant ([mtrail_wf], TRAIL-IMPLIED, watch soundness, heap
    coverage, ...) lives in S9's [msolver_inv]; keeping it out of [solver_rep]
    is what lets a hand-off be a cancellation rather than an entailment. *)
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
  Zlength (ms_wcaps M) = 2 * ms_size M /\
  Zlength (ms_binary_lits M) = 2 /\
  Zlength (ms_stats M) = 11 /\
  0 <= ms_root_level M /\
  (* [s->binary] is a genuine, even, non-null clause address.
     [solver_propagate] assigns [confl = s->binary]; [solver_search]'s
     conflict test needs [<> 0] and [solver_analyze]'s [clause_is_lit(c)]
     branch needs [is_tag = false], i.e. evenness. *)
  ms_binary M <> 0 /\
  Z.even (ms_binary M) = true.

(** The converse three equations, read back out of a tagged shape. *)

(** *** The [solver_t] fields, in four groups. *)

Definition solver_scalars_rep (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size")           # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap")            # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qhead")          # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "qtail")          # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "capacity_pending_qhead")
                                             # Int |-> ms_capacity_pending_qhead M **
  &( s # "solver_t" ->ₛ "capacity_root_propagation_pending")
                            # Int |-> ms_capacity_root_propagation_pending M **
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
  vecp_rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) (ms_prob_cap M) **
  vecp_rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) (ms_learnt_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "tagged")    (ms_tagged M) (ms_tagged_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "stack")     (ms_stack M)  (ms_stack_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "order")     (ms_order M)  (ms_order_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) (ms_lim_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")     (ms_model M)  (ms_model_cap M).

(** The six variable-indexed heap arrays: [size] live cells, [cap - size]
    undefined tail (that is exactly what [solver_setnvars] leaves behind). *)
Definition solver_var_arrays_rep
    (M : msolver) (act asg opos rsn lvl tgs : Z) : Assertion :=
  DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
  DoubleArray.undef_seg act (ms_size M) (ms_cap M) **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  CharArray.undef_seg asg (ms_size M) (ms_cap M) **
  IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
  IntArray.undef_seg opos (ms_size M) (ms_cap M) **
  PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
  PtrArray.undef_seg rsn (ms_size M) (ms_cap M) **
  IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
  IntArray.undef_seg lvl (ms_size M) (ms_cap M) **
  CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
  CharArray.undef_seg tgs (ms_size M) (ms_cap M).

Definition solver_trail_array_rep (M : msolver) (trl : Z) : Assertion :=
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  IntArray.undef_seg trl (ms_qtail M) (ms_cap M).

(** The level array is the only full-solver component cancellation never
    touches.  Factoring it once keeps pointer-sensitive callers narrow. *)
Definition solver_levels_slice_at
    (s : Z) (M : msolver) (lvl : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
  IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
  IntArray.undef_seg lvl (ms_size M) (ms_cap M).

(* The nonlevel footprint excludes the independently updated statistics table. *)
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
   DoubleArray.undef_seg act (ms_size M) (ms_cap M) **
   CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
   CharArray.undef_seg asg (ms_size M) (ms_cap M) **
   IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
   IntArray.undef_seg opos (ms_size M) (ms_cap M) **
   PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
   PtrArray.undef_seg rsn (ms_size M) (ms_cap M) **
   CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
   CharArray.undef_seg tgs (ms_size M) (ms_cap M)) **
  solver_trail_array_rep M trl **
  wlists_rep wl (ms_size M) (ms_wm M) (ms_wcaps M) **
  clause_db_rep (ms_prob M) **
  clause_db_rep (ms_learnt M) **
  MiniSatClause.rep (ms_binary M) false (ms_binary_lits M).

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
  &( s # "solver_t" ->ₛ "capacity_pending_qhead")
                                             # Int |-> ms_capacity_pending_qhead M **
  &( s # "solver_t" ->ₛ "capacity_root_propagation_pending")
                            # Int |-> ms_capacity_root_propagation_pending M **
  &( s # "solver_t" ->ₛ "root_level")     # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props")   # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity")      # Int |-> ms_verbosity M.

Definition clause_new_vecs_frame (s : Z) (M : msolver) : Assertion :=
  vecp_rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) (ms_prob_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) (ms_tagged_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) (ms_stack_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) (ms_order_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) (ms_lim_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) (ms_model_cap M).

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

Definition clause_new_frame (s : Z) (M : msolver) : Assertion :=
  EX act asg opos rsn lvl trl tgs : Z,
    clause_new_scalars_frame s M ** solver_fp_rep s M **
    clause_new_vecs_frame s M **
    clause_new_ptrs_frame s M act asg opos rsn lvl trl tgs **
    solver_var_arrays_rep M act asg opos rsn lvl tgs **
    solver_trail_array_rep M trl **
    clause_db_rep (ms_prob M) **
    MiniSatClause.rep (ms_binary M) false (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** Pointer-pinned clause-allocation frame.  [clause_new] cannot reallocate
    or rewrite the level array, so callers that cache [s->levels] retain the
    exact backing address through every reserve and installation arm. *)
Definition clause_new_frame_at (s : Z) (M : msolver) (lvl : Z) : Assertion :=
  EX act asg opos rsn trl tgs : Z,
    clause_new_scalars_frame s M ** solver_fp_rep s M **
    clause_new_vecs_frame s M **
    clause_new_ptrs_frame s M act asg opos rsn lvl trl tgs **
    solver_var_arrays_rep M act asg opos rsn lvl tgs **
    solver_trail_array_rep M trl **
    clause_db_rep (ms_prob M) **
    MiniSatClause.rep (ms_binary M) false (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** Complement of the exact [enqueue_state_at] footprint. *)
Definition solver_enqueue_scalars_frame
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
  &( s # "solver_t" ->ₛ "capacity_pending_qhead")
    # Int |-> ms_capacity_pending_qhead M **
  &( s # "solver_t" ->ₛ "capacity_root_propagation_pending")
    # Int |-> ms_capacity_root_propagation_pending M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns")
    # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M.

Definition solver_enqueue_vecs_frame (s : Z) (M : msolver) : Assertion :=
  vecp_rep &( s # "solver_t" ->ₛ "clauses")
    (map fst (ms_prob M)) (ms_prob_cap M) **
  vecp_rep &( s # "solver_t" ->ₛ "learnts")
    (map fst (ms_learnt M)) (ms_learnt_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "tagged")
    (ms_tagged M) (ms_tagged_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "stack")
    (ms_stack M) (ms_stack_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "order")
    (ms_order M) (ms_order_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")
    (ms_model M) (ms_model_cap M).

(* The shared cells retain the same association under either watch-address binder policy. *)
Definition solver_enqueue_cells_at
    (s : Z) (M : msolver) (wl act opos tgs : Z) (scalars : Assertion) : Assertion :=
    scalars ** solver_fp_rep s M **
    solver_enqueue_vecs_frame s M **
    (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
     &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
     &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
     &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
     &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
    (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
     DoubleArray.undef_seg act (ms_size M) (ms_cap M) **
     IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
     IntArray.undef_seg opos (ms_size M) (ms_cap M) **
     CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
     CharArray.undef_seg tgs (ms_size M) (ms_cap M)) **
    wlists_rep wl (ms_size M) (ms_wm M) (ms_wcaps M) **
    clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
    MiniSatClause.rep (ms_binary M) false (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

Definition solver_enqueue_frame_with_scalars
    (s : Z) (M : msolver) (scalars : Assertion) : Assertion :=
  EX wl act opos tgs : Z,
    solver_enqueue_cells_at s M wl act opos tgs scalars.

(** [assume] consumes [qhead] in addition to [enqueue_state_at]; every other
    solver cell is the exact frame below. *)
Definition solver_assume_scalars_frame
    (s : Z) (M : msolver) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap") # Int |-> ms_cap M **
  &( s # "solver_t" ->ₛ "capacity_pending_qhead")
    # Int |-> ms_capacity_pending_qhead M **
  &( s # "solver_t" ->ₛ "capacity_root_propagation_pending")
    # Int |-> ms_capacity_root_propagation_pending M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns")
    # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M.

Definition solver_assume_frame (s : Z) (M : msolver) : Assertion :=
  solver_enqueue_frame_with_scalars s M (solver_assume_scalars_frame s M).

(** Exactly the resources cancellation reads or mutates.  The level slice is
    not owned here and is therefore preserved by ordinary separation framing. *)
Definition solver_cancel_owned (s : Z) (M : msolver) (wl : Z) : Assertion :=
  “ solver_shape M ” && (EX act asg opos rsn trl tgs : Z,
    solver_nonlevel_rep_at s M wl act asg opos rsn trl tgs).

(** Stable remainder for [solver_lit_removable].  The six resources it opens
    (size, reasons, levels, tags, tagged, stack) and the three clause-object
    regions are deliberately absent. *)
Definition solver_removable_frame_at
    (s : Z) (M : msolver) (trl : Z) (wl : Z) : Assertion :=
  clause_new_scalars_frame s M ** solver_fp_rep s M **
  vecp_rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) (ms_prob_cap M) **
  vecp_rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) (ms_learnt_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) (ms_order_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) (ms_lim_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) (ms_model_cap M) **
  &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
  (EX act asg opos : Z,
    &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
    &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
    DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
    DoubleArray.undef_seg act (ms_size M) (ms_cap M) **
    CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
    CharArray.undef_seg asg (ms_size M) (ms_cap M) **
    IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
    IntArray.undef_seg opos (ms_size M) (ms_cap M) **
    solver_trail_array_rep M trl **
    wlists_rep wl (ms_size M) (ms_wm M) (ms_wcaps M)) **
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
  &( s # "solver_t" ->ₛ "capacity_pending_qhead")
    # Int |-> ms_capacity_pending_qhead M **
  &( s # "solver_t" ->ₛ "capacity_root_propagation_pending")
    # Int |-> ms_capacity_root_propagation_pending M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M **
  &( s # "solver_t" ->ₛ "var_decay") # Double |-> ms_var_decay M **
  &( s # "solver_t" ->ₛ "cla_decay") # Float |-> ms_cla_decay M **
  &( s # "solver_t" ->ₛ "random_seed") # Double |-> ms_random_seed M **
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M **
  vecp_rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) (ms_prob_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) (ms_model_cap M) **
  &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M.

Definition solver_analyze_frame (s : Z) (M : msolver) (wl : Z) : Assertion :=
  solver_analyze_frame_cells s M **
  (EX asg : Z,
    &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
    &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
    CharArray.undef_seg asg (ms_size M) (ms_cap M) **
    wlists_rep wl (ms_size M) (ms_wm M) (ms_wcaps M)) **
  stats_analyze_frame &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** Two compact recombination frames used after resolution.  Both are exact
    views of [solver_rep], obtained by extending [solver_removable_frame_at]
    with all resources except the named focus. *)
Definition solver_reason_levels_frame_at
    (s : Z) (M : msolver) (trl tags_ptr : Z) (wl : Z) : Assertion :=
    &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tags_ptr **
    CharArray.seg tags_ptr 0 (ms_size M) (ms_tags M) **
    CharArray.undef_seg tags_ptr (ms_size M) (ms_cap M) **
    veci_rep &( s # "solver_t" ->ₛ "tagged")
             (ms_tagged M) (ms_tagged_cap M) **
    veci_rep &( s # "solver_t" ->ₛ "stack")
             (ms_stack M) (ms_stack_cap M) **
    clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
    MiniSatClause.rep (ms_binary M) false (ms_binary_lits M) **
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
  &( s # "solver_t" ->ₛ "capacity_pending_qhead")
      # Int |-> ms_capacity_pending_qhead M **
  &( s # "solver_t" ->ₛ "capacity_root_propagation_pending")
      # Int |-> ms_capacity_root_propagation_pending M **
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
  &( s # "solver_t" ->ₛ "verbosity") # Int |-> ms_verbosity M **
  solver_fp_rep s M **
  vecp_rep &( s # "solver_t" ->ₛ "clauses")
           (map fst (ms_prob M)) (ms_prob_cap M) **
  vecp_rep &( s # "solver_t" ->ₛ "learnts")
           (map fst (ms_learnt M)) (ms_learnt_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) (ms_tagged_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) (ms_stack_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) (ms_order_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) (ms_model_cap M) **
  (EX act opos tgs : Z,
    &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
    DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
    DoubleArray.undef_seg act (ms_size M) (ms_cap M) **
    IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
    IntArray.undef_seg opos (ms_size M) (ms_cap M) **
    CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
    CharArray.undef_seg tgs (ms_size M) (ms_cap M)) **
  stats_propagate_frame &( s # "solver_t" ->ₛ "stats") (ms_stats M).

(** The binary scratch object is kept separate in propagation annotations:
    unlike a real database clause it is never a member of either DB vector,
    but the binary-conflict arm mutates its two literal cells in place. *)
Definition solver_binary_rep (M : msolver) : Assertion :=
  MiniSatClause.rep (ms_binary M) false (ms_binary_lits M).

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

(** The exact spatial footprint of [enqueue].  Keeping this focus separate
    from [solver_rep] lets propagation, record, and the public assumption
    path frame their distinct transient resources while sharing one checked
    definition contract. *)
Definition enqueue_state_at
    (s asg lvl n cap qtail : Z)
    (assigns levels reasons trail lim : list Z) (lim_cap : Z) : Assertion :=
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
     CharArray.undef_seg asg n cap **
     IntArray.seg lvl 0 n levels **
     IntArray.undef_seg lvl n cap **
     PtrArray.seg rsn 0 n reasons **
     PtrArray.undef_seg rsn n cap **
     IntArray.seg trl 0 qtail trail **
     IntArray.undef_seg trl qtail cap **
     veci_rep &( s # "solver_t" ->ₛ "trail_lim") lim lim_cap).

Definition enqueue_post_at
    (s asg lvl l reason n cap qtail ret : Z)
    (assigns levels reasons trail lim : list Z) (lim_cap : Z) : Assertion :=
  EX qtail' : Z, EX assigns' : list Z, EX levels' : list Z,
  EX reasons' : list Z, EX trail' : list Z,
    “ enqueue_transition l reason qtail ret qtail'
        assigns levels reasons trail lim
        assigns' levels' reasons' trail' ” &&
    enqueue_state_at s asg lvl n cap qtail'
      assigns' levels' reasons' trail' lim lim_cap.

Definition assume_post_at
    (s asg lvl l n cap qtail : Z)
    (assigns levels reasons trail lim : list Z) (lim_cap : Z) : Assertion :=
  EX lim_cap' : Z,
    “ lim_cap <= lim_cap' <= INT_MAX ” &&
    (&( s # "solver_t" ->ₛ "qhead") # Int |-> qtail **
     enqueue_post_at s asg lvl l 0 n cap qtail 1
       assigns levels reasons trail (lim ++ [qtail]) lim_cap').

(** The pointer-exposed variant: the shape a body that has just loaded the
    eight cached pointers works against.  [solver_rep] is its existential
    closure, so the two convert without any spatial reasoning. *)
Definition solver_rep_at
    (s : Z) (M : msolver) (wl act asg opos rsn lvl trl tgs : Z) : Assertion :=
  “ solver_shape M ” &&
  (solver_nonlevel_rep_at s M wl act asg opos rsn trl tgs **
   solver_levels_slice_at s M lvl).

(** Narrow existential closures used when a native local caches one solver
    backing address across calls that otherwise return an existential whole
    state.  They pin only the address actually dereferenced by that caller. *)


Definition solver_rep_reasons_levels_at
    (s : Z) (M : msolver) (rsn lvl : Z) : Assertion :=
  EX wl act asg opos trl tgs : Z,
    solver_rep_at s M wl act asg opos rsn lvl trl tgs.

Definition solver_rep_levels_at
    (s : Z) (M : msolver) (lvl : Z) : Assertion :=
  “ solver_shape M ” &&
  (solver_nonlevel_rep s M ** solver_levels_slice_at s M lvl).

Definition solver_rep_analyze_at
    (s : Z) (M : msolver) (rsn lvl trl tgs : Z) (wl : Z) : Assertion :=
  EX act asg opos : Z,
    solver_rep_at s M wl act asg opos rsn lvl trl tgs.

Lemma solver_shape_wm_len : forall M,
  solver_shape M -> Zlength (ms_wm M) = 2 * ms_size M.
Proof. intros M H. unfold solver_shape in H. tauto. Qed.

(** ** Relating the raw reason words to the ghost reason map.

    MiniSat packs a binary reason as the ODD integer [2*l+1]
    ([clause_from_lit]) and a real reason as the (even) clause pointer.  The
    spatial layer stores only the word; this predicate is the pure bridge, and
    it is the S9 invariant that asserts it.  Note it is stated over the S5
    [dbmap] so that deletion of a clause object is visible here. *)

Definition db_lookup (db : dbmap) (p : Z) (co : clause_obj) : Prop :=
  In (p, co) db.

(** *** The literal a variable carries on the trail.

    [2*v] when the [assigns] cell says TRUE, [2*v+1] when it says FALSE --
    MiniSat's [toLit(v)] and [lit_neg(toLit(v))] read back off the
    assignment.  The value at an unassigned variable is junk and never used:
    every lemma below takes [mt_pv t v = Some b]. *)
Definition trail_lit_of (t : mtrail) (v : Z) : Z :=
  if Znth v (mt_assigns t) 0 =? -1 then 2 * v + 1 else 2 * v.

(** *** The reason word codec.

    MiniSat writes [reasons[lit_var(q)] = clause_from_lit(p)] during
    [solver_propagate], where
    [q] is the literal being ENQUEUED and [p] is the literal that PROPAGATED
    it -- a different variable, and TRUE.  The antecedent is the binary clause
    [{q, lit_neg(p)}] (the C itself writes exactly that
    negation when it builds the conflict:
    [(clause_begin(confl))[1] = lit_neg(p)]).

    The word alone cannot name [q], so the predicate now takes the trail [t]
    and the variable [v] and reads [q] back off the assignment.  Note the
    polarity: the SECOND literal is the NEGATION of the tag literal, because
    the tag stores the propagator, which is true. *)
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

(** The table field and every watcher list except the currently open source
    slot.  This remains stable while propagation compacts that source. *)
Definition wlists_source_hole_handle
    (s base hole : Z) (pre post : list (list Z))
    (capspre capspost : list Z) : Assertion :=
  solver_wlists_handle s base **
  wlists_rep_from base 0 pre capspre **
  wlists_rep_from base (hole + 1) post capspost.

(** Full-table remainder after opening two distinct watcher vectors.  This is
    symmetric in the two indices and is used by [clause_new]/[clause_remove],
    where both watcher slots must remain open at once. *)
Definition wlists_two_remainder
    (base i j : Z) (wm : wmap) (caps : list Z) : Assertion :=
  if Z.ltb i j then
    wlists_rep_from base 0
      (sublist 0 i wm) (sublist 0 i caps) **
    wlists_rep_from base (i + 1)
      (sublist (i + 1) j wm) (sublist (i + 1) j caps) **
    wlists_rep_from base (j + 1)
      (sublist (j + 1) (Zlength wm) wm)
      (sublist (j + 1) (Zlength caps) caps)
  else
    wlists_rep_from base 0
      (sublist 0 j wm) (sublist 0 j caps) **
    wlists_rep_from base (j + 1)
      (sublist (j + 1) i wm) (sublist (j + 1) i caps) **
    wlists_rep_from base (i + 1)
      (sublist (i + 1) (Zlength wm) wm)
      (sublist (i + 1) (Zlength caps) caps).

Definition clause_new_transaction_rest
    (s begin clause_out wl i0 i1 : Z) (M : msolver)
    (words : list Z) : Assertion :=
  solver_wlists_handle s wl **
  wlists_two_remainder wl i0 i1 (ms_wm M) (ms_wcaps M) **
  clause_new_frame s M.

Definition clause_new_transaction_rest_at
    (s begin clause_out wl i0 i1 : Z) (M : msolver)
    (words : list Z) (lvl : Z) : Assertion :=
  solver_wlists_handle s wl **
  wlists_two_remainder wl i0 i1 (ms_wm M) (ms_wcaps M) **
  clause_new_frame_at s M lvl.

Lemma wlists_rep_from_app_join : forall base i xs ys xcaps ycaps,
  Zlength xs = Zlength xcaps ->
  wlists_rep_from base i xs xcaps **
  wlists_rep_from base (i + Zlength xs) ys ycaps
  |-- wlists_rep_from base i (xs ++ ys) (xcaps ++ ycaps).
Proof.
  intros base i xs. revert i.
  induction xs as [|x xs IH]; intros i ys xcaps ycaps Hlen;
    destruct xcaps as [|xcap xcaps].
  - simpl. rewrite Zlength_nil. replace (i + 0) with i by lia.
    entailer_with lia.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - rewrite !Zlength_cons in Hlen. simpl.
    replace (i + Zlength (x :: xs)) with
      ((i + 1) + Zlength xs) by (rewrite Zlength_cons; lia).
    sep_apply (IH (i + 1) ys xcaps ycaps ltac:(lia)). entailer_with lia.
Qed.

Lemma wlists_rep_from_single : forall base i words cap,
  vecp_rep (vecp_slot base i) words cap
  |-- wlists_rep_from base i [words] [cap].
Proof. intros. simpl. entailer_with lia. Qed.

Lemma wlists_rep_from_insert_at :
  forall base start index pre words post capspre cap capspost,
  Zlength pre = Zlength capspre ->
  index = start + Zlength pre ->
  wlists_rep_from base start pre capspre **
  vecp_rep (vecp_slot base index) words cap **
  wlists_rep_from base (index + 1) post capspost
  |-- wlists_rep_from base start (pre ++ words :: post)
                              (capspre ++ cap :: capspost).
Proof.
  intros base start index pre words post capspre cap capspost Hlen Hindex.
  subst index. sep_apply (wlists_rep_from_single base
    (start + Zlength pre) words cap).
  sep_apply (wlists_rep_from_app_join base start pre [words]
    capspre [cap] Hlen).
  replace (start + Zlength pre + 1) with
    (start + Zlength (pre ++ [words])) by
    (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  sep_apply (wlists_rep_from_app_join base start (pre ++ [words]) post
    (capspre ++ [cap]) capspost
    ltac:(rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; lia)).
  assert (Hwords : (pre ++ [words]) ++ post = pre ++ (words :: post)) by
    (rewrite <- app_assoc; reflexivity).
  assert (Hcaps : (capspre ++ [cap]) ++ capspost =
                  capspre ++ (cap :: capspost)) by
    (rewrite <- app_assoc; reflexivity).
  rewrite Hwords, Hcaps. entailer_with lia.
Qed.

Lemma solver_shape_wcaps_len : forall M,
  solver_shape M -> Zlength (ms_wcaps M) = 2 * ms_size M.
Proof. intros M H. unfold solver_shape in H. tauto. Qed.

(** ** Notes on what this file deliberately does NOT own.

    - The [order]/[trail_lim]/[model]/[tagged]/[stack] payload arrays are
      inside their [veci]s, so [heap_wf] (S7) reads [ms_order] and
      [ms_orderpos] but touches no spatial atom.
    - [s->binary] is owned as a plain [MiniSatClause::rep] alongside the DB; S9
      asserts it is in neither [ms_prob] nor [ms_learnt] and in no watch list.
    - Reason and watcher words are stored as integers.  [reason_word_ok]
      interprets reason words; [entry_watchers] and the focused scan carriers
      interpret watcher words.  Pointer/tag separation follows from the
      clause-pointer parity facts in the spatial database representation. *)

(* ================= SECTION msat_s9_contract ================= *)

(** * S9 -- contract vocabulary and the two endgame theorems.

    Everything below is assembly: S1-S8 own the mathematics, this section
    bolts the pieces onto the single ghost record [msolver] that the spatial
    bundle carries, and derives the two facts [solver_solve] has to return.

    Design points worth stating up front.

    - The invariant is a [Record] in [Prop], not a right-nested conjunction:
      named projections are stable under reordering, a nested [/\] is not.
    - The bundle is split.  [msolver_inv_weak] carries the persistent
      semantics and exact watcher map.  [msolver_inv] additionally carries
      [prop_level], the occurrence-indexed propagation frontier, and heap
      coverage.  A conflict may return while the current watcher scan is in
      flux, so UNSAT endgames consume the weak bundle; SAT endgames receive
      the frontier and heap facts explicitly.
    - The bundle is
      parameterised by BOTH assumption lists.  [A_arr] is the caller's array;
      [A_inst] is the installed sub-list [decisions_upto core root_level]
      (an assumption already true when processed creates no decision level,
      so [A_inst] can be a strict sub-list).  The
      bundle records [incl A_inst A_arr] and that every [A_arr] literal is
      true on the trail at level <= root_level, which is exactly what the SAT
      arm needs to claim the model satisfies the caller's assumptions and what
      [cnf_unsat_units_mono] needs to strengthen the UNSAT verdict.
    - The invariant is deliberately kept OUT of [solver_rep] (S8): a hand-off
      between two functions is then a spatial cancellation plus a pure
      implication, never an entailment between two big bundles.  [solver_stable]
      is the glued form, using [&&] (not [**]) so no junk heap can sneak in
      under the [coq_prop] -- the [H ** "P"] trap.
    - Facts that are *derivable* from other conjuncts are not conjuncts.
      [db_entailed], [trail_covers] and [assigns_total] are lemmas here, not
      fields; carrying them would mean re-proving them at every state change. *)

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

(** The logical clause set the view sees. *)
Definition msolver_clauses (M : msolver) : list clause :=
  db_clauses (msolver_db M).

(** The order heap, as S7's record. *)
Definition msolver_heap (M : msolver) : mheap :=
  {| mh_heap := ms_order M; mh_orderpos := ms_orderpos M |}.

(** The CDCL view the S3 algebra is stated over. *)
Definition msolver_view (n : Z) (M : msolver) : cdcl_view :=
  view_of n (ms_core M) (ms_reason_of M) (msolver_clauses M).

(** ** Database matching (the two halves of DB-IMPLIED) and DB-COMPLETE. *)

(** Every *problem* clause object is a permutation of an original clause.
    [solver_addclause] sorts the literals before [clause_new] copies them, and
    [solver_propagate] may swap [lits[0]] with [lits[1]]; both are permutations
    and nothing else ever reorders a clause. *)
Definition db_matches_cnf (F : cnf) (M : msolver) : Prop :=
  Forall (fun c => exists c0, In c0 F /\ Permutation c c0)
         (db_clauses (ms_prob M)).

(** Every *learnt* clause is a logical consequence.  This is DB-IMPLIED. *)
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

(** ** Reason side conditions that the spatial layer cannot state.

    S8's [reasons_match] already says each [reasons[v]] word decodes to the
    ghost reason clause (and, for a real reason, that the object is still
    resident in the database).  Two facts remain, and both are what
    [solver_analyze] reads off the memory directly. *)

(** lits[0] discipline: a clause object serving as a real reason
    keeps the implied literal in slot 0. *)
Definition reason_head_ok (M : msolver) : Prop :=
  forall v co,
    0 <= v < ms_size M ->
    is_tag (Znth v (ms_reason_words M) 0) = false ->
    Znth v (ms_reason_words M) 0 <> 0 ->
    In (Znth v (ms_reason_words M) 0, co) (msolver_db M) ->
    lit_var_c (co_watch0 co) = v.

(** A binary reason's partner literal is well formed, sits at the same
    decision level, and names a different variable from the implied literal.
    The strong bundle's [prop_level] fact establishes the level half at
    propagation sites; native propagation supplies the variable disequality.

    The [lit_wf_c] half is the ONLY place the bundle bounds a TAGGED reason
    word.  It is needed and it is not redundant: [reasons_match]'s tagged arm
    ([reason_word_ok], is_tag branch) adds owner liveness and an equation on
    the ghost clause, but still does not bound the tag word; [reason_head_ok] is gated on
    [is_tag _ = false]; [solver_shape] gives only [Zlength]; and the level
    equation below is stated with total [Znth ... 0] lookups, so it survives
    a wildly out-of-range word.  Without this conjunct the tagged disjunct of
    [reason_target_wf] is underivable from the bundle -- see
    [inv_tagged_reason_target_arm], which is exactly what the
    [solver_lit_removable] / [solver_analyze] "which implies" blocks need.

    Positivity need not be carried separately: [0 < w] follows from
    [lit_wf_c] because the word is odd ([tag_pos_of_lit_wf]). *)
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

(** Exact operational shadow required by the audited random facade.  It is
    deliberately not embedded in the weak semantic endgames. *)
Definition msolver_seed_shadow (M : msolver) : Prop :=
  exists z, ms_random_seed M = Z_to_fp64 z /\ seed_ok z.

(** ** The assumption vocabulary.

    An [A_arr] literal is true on the trail at a level at or below
    [root_level].  This is what the assumption loop guarantees for every
    element of the caller's array: case 1 (already true -- assigned at some
    earlier level, no new decision) and case 0 (installed as a decision at
    the new level) both land here, and the fact survives every
    [canceluntil(blevel)] with [blevel >= root_level] because the cells at
    levels <= root_level are never cleared inside [solver_search]. *)
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
  (* --- the CDCL algebra (S3) --- *)
  msw_stable      : stable_view (msolver_view n M);
  msw_reasons_ent : reasons_entailed F (msolver_view n M);
  msw_reasons_inj : reasons_var_injective (msolver_view n M);
  (* --- TRAIL-IMPLIED (S4) --- *)
  msw_trail_impl  : trail_implied F (ms_core M);
  (* --- the clause database (S5) --- *)
  msw_db_wf       : db_wf n (msolver_db M);
  msw_db_matches  : db_matches_cnf F M;
  msw_db_implied  : db_implied F M;
  msw_db_complete : db_complete F M;
  msw_learnt_db   : learnt_db (ms_learnt M);
  msw_prob_db     : prob_db (ms_prob M);
  msw_binary_out  : ~ In (ms_binary M) (map fst (msolver_db M));
  (* --- reason words vs ghost reasons (S8) --- *)
  msw_reasons_mem : reasons_match n (ms_core M) (msolver_db M)
                                  (ms_reason_words M) (ms_reason_of M);
  msw_reason_head : reason_head_ok M;
  msw_reason_bin  : binary_reason_same_level M;
  (* --- watcher table exactness (S5; membership only, no soundness) --- *)
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

(** ** ...and the strong stable-point bundle.

    It adds the propagation-level boundary, the occurrence-indexed watcher
    frontier, and full heap coverage.  [order_select] temporarily uses
    [heap_covers_except]; propagation temporarily uses a focused scan carrier. *)

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

(** The state predicate the top-level contract quantifies over. *)
Definition solver_at_root (M : msolver) : Prop :=
  Zlength (mt_lim (ms_core M)) = ms_root_level M.

(** ** The mid-assumption-loop bundle.

    During [solver_solve]'s assumption loop
    [s->root_level] still holds its pre-loop value 0 while [solver_dlevel(s)]
    grows, so the [ms_root_level]-pinned conjuncts of [msolver_inv_weak] are
    FALSE as soon as one assumption has been installed: [msw_assumptions]
    forces [A_inst = decisions_upto _ 0 = []], while [msw_assump_sat] pins
    every array element to level 0 -- contradicting the installed decisions at
    levels >= 1.  Its two failure routes are a false cursor assumption and a
    propagation conflict.

    [msolver_inv_assuming n F A_arr A_proc M] is the mid-loop bundle:
    [msolver_inv_weak] minus every [ms_root_level] conjunct, with the
    assumption conjuncts restated against the CURRENT decision level
    [Zlength (mt_lim (ms_core M))] and the loop's processed prefix [A_proc]
    (the elements already installed as decisions or skipped as already-true;
    the cursor element and the unvisited tail are in [A_arr] only).  The two
    wrappers below are the packaged discharges for the two failure routes;
    both conclude over the caller's full array via [cnf_unsat_units_mono].
    [w4_assuming_gen] inhabits this bundle independently of the stale stored
    root field and with a non-empty processed prefix. *)

Record msolver_inv_assuming (n : Z) (F : cnf) (A_arr A_proc : list literal)
                            (M : msolver) : Prop := {
  (* --- sizes, ranges, well-formed inputs --- *)
  msa_size        : n = ms_size M;
  msa_n_range     : 0 <= n;
  msa_shape       : solver_shape M;
  msa_F_wf        : cnf_wf n F;
  msa_A_wf        : Forall (literal_wf n) A_arr;
  (* --- the concrete trail (S4) --- *)
  msa_trail_wf    : mtrail_wf n (ms_core M);
  msa_level_bound : Zlength (mt_lim (ms_core M)) <= n;
  (* --- assumptions, against the CURRENT dlevel and the processed prefix:
         every decision installed so far is a processed assumption, the
         processed prefix sits inside the caller's array, and every processed
         element is true on the trail at a level at or below the current one.
         [ms_root_level] is deliberately absent: it is STALE here. *)
  msa_decisions   : exists A_inst,
                      decisions_upto (ms_core M) (Zlength (mt_lim (ms_core M)))
                        = A_inst /\ incl A_inst A_proc;
  msa_proc_incl   : incl A_proc A_arr;
  msa_proc_sat    : Forall (assump_true_at_root (ms_core M)
                              (Zlength (mt_lim (ms_core M)))) A_proc;
  (* --- the CDCL algebra (S3) --- *)
  msa_stable      : stable_view (msolver_view n M);
  msa_reasons_ent : reasons_entailed F (msolver_view n M);
  msa_reasons_inj : reasons_var_injective (msolver_view n M);
  (* --- TRAIL-IMPLIED (S4) --- *)
  msa_trail_impl  : trail_implied F (ms_core M);
  (* --- the clause database (S5) --- *)
  msa_db_wf       : db_wf n (msolver_db M);
  msa_db_matches  : db_matches_cnf F M;
  msa_db_implied  : db_implied F M;
  msa_db_complete : db_complete F M;
  msa_learnt_db   : learnt_db (ms_learnt M);
  msa_prob_db     : prob_db (ms_prob M);
  msa_binary_out  : ~ In (ms_binary M) (map fst (msolver_db M));
  (* --- reason words vs ghost reasons (S8) --- *)
  msa_reasons_mem : reasons_match n (ms_core M) (msolver_db M)
                                  (ms_reason_words M) (ms_reason_of M);
  msa_reason_head : reason_head_ok M;
  msa_reason_bin  : binary_reason_same_level M;
  (* --- watcher table exactness (S5) --- *)
  msa_wmap_exact  : wmap_exact n (msolver_db M) (ms_wm M);
  (* --- stable analysis scratch --- *)
  msa_tags_clear  : solver_tags_clear M;
  (* --- heuristics (S7) --- *)
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

(** Propagation may be entered immediately after [order_select] has removed the
    decision variable from the heap and [assume] has appended its literal to
    the queue.  In that corridor full heap coverage is missing for exactly the
    variable at the next queue cursor.  A successful first dequeue restores
    ordinary coverage; a capacity abort rolls the cursor back and must retain
    this exact exception rather than overclaiming the strong bundle. *)
Definition propagation_heap_ready (n : Z) (M : msolver) : Prop :=
  heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) \/
  (0 < Zlength (mt_lim (ms_core M)) /\
   mt_qhead (ms_core M) < ms_qtail M /\
   heap_covers_except n (msolver_heap M) (mt_assigns (ms_core M))
     (mt_trail (ms_core M)) (mt_qhead (ms_core M))
     (lit_var_c (Znth (mt_qhead (ms_core M))
                       (mt_trail (ms_core M)) 0))).

(** The exact heap fact needed if a capacity failure rolls the already
    advanced propagation cursor back by one.  [p] is pinned to that concrete
    trail cell, excluding the default-[Znth] state.  At a non-root level the
    ordinary one-variable exception is available; at root, the focus remains
    in the decision heap and full coverage can be recovered. *)
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
    conflict.  Pointer/object ownership remains inside [solver_rep]. *)
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
   ~ In p (map fst (msolver_db M))) \/
  exists co, p <> ms_binary M /\
    In (p, co) (msolver_db M) /\ C = denote_obj co.

(** Propagation preserves decision boundaries, the root marker, the model
    vector, clause decay and variable capacity. Callers use the capacity
    equality to retain the unused outer watcher-table storage across queries;
    inner watcher vectors and other mutable fields remain unrestricted. *)
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

(** Semantic carrier for the open watcher scan.  The live arm retains the
    weak solver invariant plus the propagation-only facts, opens the generic
    frontier at exactly [lit_denote p], and aligns the compacted/pending words
    with occurrence-indexed contribution tokens.  The occurrence identity is
    essential when distinct binary clauses emit the same tagged word.  The
    conflict arm has consumed the whole source suffix and carries the exact
    real-or-binary conflict certificate. *)
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

(** Checked growth is rejected precisely when a full vector's current
    capacity is already above MiniSat's largest safely growable value. *)
Definition minisat_max_growable_cap : Z := 1073741823.

Definition vector_capacity_exhausted (len cap : Z) : Prop :=
  len = cap /\ minisat_max_growable_cap < cap <= INT_MAX.

(** In the verified [solver_solve] call graph only the learnt database and
    individual watcher lists are lifetime-unbounded. *)
Definition solver_capacity_exhausted (M : msolver) : Prop :=
  vector_capacity_exhausted (Zlength (ms_learnt M)) (ms_learnt_cap M) \/
  exists i,
    0 <= i < Zlength (ms_wm M) /\
    vector_capacity_exhausted
      (Zlength (Znth i (ms_wm M) []))
      (Znth i (ms_wcaps M) 0).

(** The two statistics counters the watcher scan mutates; every other stats
    field stays inside [stats_propagate_frame]. *)
Definition stats_propagate_scan (q prop insp : Z) : Assertion :=
  &( q # "stats_t" ->ₛ "propagations") # UInt64 |-> prop **
  &( q # "stats_t" ->ₛ "inspects") # UInt64 |-> insp.

(** The scan core owns the solver components left untouched by the watcher
    step. Its array addresses are explicit. The writable [qhead] cell remains
    outside the core because capacity failure rolls it back separately.

    Assignment storage also stays separate where the replacement scan reads
    it. [solver_propagation_scan_arrays_noqh_at] adds those segments back at
    sites that carry the combined frame. *)
Definition solver_propagation_scan_core_at
    (s : Z) (M : msolver) (asg rsn lvl trl simp prop : Z) : Assertion :=
  PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
  PtrArray.undef_seg rsn (ms_size M) (ms_cap M) **
  IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
  IntArray.undef_seg lvl (ms_size M) (ms_cap M) **
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  IntArray.undef_seg trl (ms_qtail M) (ms_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) (ms_lim_cap M) **
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

Definition solver_selected_cap (type : Z) (M : msolver) : Z :=
  if Z.eqb type 0 then ms_prob_cap M else ms_learnt_cap M.

Definition solver_selected_is_learnt (type : Z) : bool :=
  negb (Z.eqb type 0).

Definition solver_other_db_vec_rep
    (s type : Z) (M : msolver) : Assertion :=
  if Z.eqb type 0 then
    vecp_rep &( s # "solver_t" ->ₛ "learnts")
      (map fst (ms_learnt M)) (ms_learnt_cap M)
  else
    vecp_rep &( s # "solver_t" ->ₛ "clauses")
      (map fst (ms_prob M)) (ms_prob_cap M).

Definition solver_other_clause_db_rep
    (type : Z) (M : msolver) : Assertion :=
  if Z.eqb type 0
  then clause_db_rep (ms_learnt M)
  else clause_db_rep (ms_prob M).

(** Exact complement of simplification's selected parent vector, selected
    live clause objects, watcher table, reasons, size, and statistics.  It is
    symmetric in the problem/learnt choice and therefore does not reuse the
    learnt-only reducedb frame. *)


(** Complement used while the current selected clause, the live assignment
    prefix, and the empty decision-level vector are exposed to
    [clause_simplify]. *)
Definition solver_simplify_clause_frame_at
    (s type : Z) (M : msolver) (asg lvl : Z) : Assertion :=
  clause_new_scalars_frame s M ** solver_fp_rep s M **
  solver_other_db_vec_rep s type M **
  veci_rep &( s # "solver_t" ->ₛ "tagged")
    (ms_tagged M) (ms_tagged_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "stack")
    (ms_stack M) (ms_stack_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "order")
    (ms_order M) (ms_order_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")
    (ms_model M) (ms_model_cap M) **
  (EX act opos trl tgs : Z,
    &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
    &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
    &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
    &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
    &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
    DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
    DoubleArray.undef_seg act (ms_size M) (ms_cap M) **
    CharArray.undef_seg asg (ms_size M) (ms_cap M) **
    IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
    IntArray.undef_seg opos (ms_size M) (ms_cap M) **
    IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
    IntArray.undef_seg trl (ms_qtail M) (ms_cap M) **
    CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
    CharArray.undef_seg tgs (ms_size M) (ms_cap M)) **
  solver_levels_slice_at s M lvl **
  solver_other_clause_db_rep type M **
  MiniSatClause.rep (ms_binary M) false (ms_binary_lits M).

(** Exact complement while simplification exposes the selected database,
    assignments, empty decision-level vector, watcher/reason arrays, and
    statistics needed by the two clause calls. *)
Definition solver_simplify_db_rest_at
    (s type : Z) (M : msolver) (reasons lvl wl asg : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  solver_wlists_handle s wl **
  wlists_rep wl (ms_size M) (ms_wm M) (ms_wcaps M) **
  &( s # "solver_t" ->ₛ "reasons") # Ptr |-> reasons **
  PtrArray.seg reasons 0 (ms_size M) (ms_reason_words M) **
  PtrArray.undef_seg reasons (ms_size M) (ms_cap M) **
  stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M) **
  solver_simplify_clause_frame_at s type M asg lvl.

(** Shared internal [-2] handoff consumed immediately by public capacity
    normalization.  Failing-vector identity and raw cursor detail remain
    local to the producer that proves this prepare-ready projection. *)
Definition solver_internal_capacity_ready
    (n : Z) (F : cnf) (A_arr A_inst : list literal) (M : msolver) : Prop :=
  solver_propagation_inv n F A_arr (PropagationStable A_inst) M /\
  solver_capacity_exhausted M /\ msolver_seed_shadow M.

(** After cancellation, recording consumes an asserting-clause certificate
    in the post-backjump view: the head is unassigned and the tail remains
    false.  This deliberately replaces the invalid practice of reusing a UIP
    certificate tied to the pre-backjump state. *)
Definition record_ready_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) : Prop :=
  1 <= Zlength words /\ Forall (lit_wf_c n) words /\
  NoDup (map lit_var_c words) /\
  entails_clause F (lits_denote words) /\
  Znth (lit_var_c (Znth 0 words 0)) (mt_assigns (ms_core M)) 0 = 0 /\
  clause_false (mt_pv (ms_core M)) (tl (lits_denote words)) /\
  (Zlength words = 1 -> solver_at_root M).

Definition record_clause_cert := record_ready_cert.

Definition clause_new_caps_progress
    (entry : msolver) (words : list Z) (current : msolver) : Prop :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  current = entry \/
  (exists learnt_cap,
     current = msolver_with_clause_caps
       entry learnt_cap (ms_wcaps entry)) \/
  (exists learnt_cap cap0,
     current = msolver_with_clause_caps entry learnt_cap
       (replace_Znth i0 cap0 (ms_wcaps entry))) \/
  (exists learnt_cap cap0 cap1,
     current = msolver_with_clause_caps entry learnt_cap
       (replace_Znth i1 cap1
         (replace_Znth i0 cap0 (ms_wcaps entry)))).

Definition clause_allocator_fresh (M : msolver) (c : Z) : Prop :=
  0 < c /\ Z.even c = true /\ c <> ms_binary M /\
  ~ In c (map fst (msolver_db M)).

Definition clause_new_stage_rep_at
    (s begin clause_out database watch0 watch1 wl lvl : Z)
    (M : msolver) (words : list Z) : Assertion :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  “ database = &( s # "solver_t" ->ₛ "learnts") /\
    watch0 = vecp_slot wl i0 /\ watch1 = vecp_slot wl i1 /\
    i0 <> i1 ” &&
  (vecp_rep database (map fst (ms_learnt M)) (ms_learnt_cap M) **
   vecp_rep watch0 (Znth i0 (ms_wm M) []) (Znth i0 (ms_wcaps M) 1) **
   vecp_rep watch1 (Znth i1 (ms_wm M) []) (Znth i1 (ms_wcaps M) 1) **
   clause_db_rep (ms_learnt M) **
   clause_new_transaction_rest_at
     s begin clause_out wl i0 i1 M words lvl **
   &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
   IntArray.seg begin 0 (Zlength words) words **
   clause_out # Ptr |-> 0).

Definition clause_new_stage_ready
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry current : msolver) (words : list Z) : Prop :=
  2 <= Zlength words /\ 2 * Zlength words + 1 <= INT_MAX /\
  clause_new_caps_progress entry words current /\
  msolver_inv n F A_arr A_inst current /\
  ms_capacity_root_propagation_pending current = 0 /\
  msolver_seed_shadow current /\
  record_clause_cert n F current words.

(** Which of the three vectors in [clause_new] has already been reserved.
    The implications let one compact carrier accumulate room without
    restating the three inequalities at every transaction checkpoint. *)
Definition clause_new_reserved_rooms
    (stage : Z) (words : list Z) (M : msolver) : Prop :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  (1 <= stage ->
     Zlength (map fst (ms_learnt M)) < ms_learnt_cap M) /\
  (2 <= stage ->
     Zlength (Znth i0 (ms_wm M) []) < Znth i0 (ms_wcaps M) 1) /\
  (3 <= stage ->
     Zlength (Znth i1 (ms_wm M) []) < Znth i1 (ms_wcaps M) 1).

Definition clause_new_capacity_failure
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry current : msolver) (words : list Z) : Prop :=
  clause_new_caps_progress entry words current /\
  solver_internal_capacity_ready n F A_arr A_inst current.

(* ================= SECTION msat_problem_clause_install ================= *)

(** * Generalising clause installation over the [learnt] flag.

    [clause_new] is called from two places in MiniSat: [solver_record]
    installs a learned clause into [s->learnts], and [solver_addclause]
    installs a problem clause into [s->clauses].  Only the first was
    specifiable: [msolver_install_learnt_clause] hard-codes
    [ms_learnt M ++ [(c, .. co_learnt := true ..)]].

    This section supplies the logical half of the second.  The
    representation layer needed no change -- [activity_state] and
    [clause_hdr_word] already take the tag -- so everything here is about
    the *algebra*: the generic installation, its projections, the
    permutation bridge (a problem clause lands in the MIDDLE of
    [msolver_db = ms_prob ++ ms_learnt], not at its end), and the
    [F]-monotonicity toolkit that a *growing* formula needs. *)


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
    (ms_binary_lits M) (clause_new_watch_map M c words)
    (ms_wcaps M) (ms_stats M).

(** The existing learned-clause installation is the [learnt = true]
    instance, definitionally.  Nothing that already depends on it changes. *)
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

(** ** The remaining pointwise fields, and the assembled preservation. *)

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

(** *** The certificate a PROBLEM clause carries.

    [record_clause_cert] is the learned-clause certificate: head unassigned,
    TAIL FALSE.  A problem clause satisfies neither -- every one of its
    literals is unassigned, because [solver_addclause]'s dedup pass keeps a
    literal only when its [values] cell reads 0.  This is its sibling. *)
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
  exists Mcaps,
    clause_new_caps_progress entry words Mcaps /\
    clause_allocator_fresh Mcaps c /\
    M' = msolver_install_learnt_clause Mcaps c words /\
    msolver_inv n F A_arr A_inst M' /\
    ms_capacity_root_propagation_pending M' = 0 /\
    msolver_seed_shadow M' /\
    record_clause_cert n F M' words.

Definition clause_new_pre_at
    (s begin finish learnt database clause_out lvl n : Z)
    (F : cnf) (A_arr A_inst : list literal)
    (M : msolver) (words : list Z) : Assertion :=
  “ learnt = 1 /\
    database = &( s # "solver_t" ->ₛ "learnts") /\
    finish = begin + Zlength words * sizeof(INT) /\
    2 <= Zlength words /\ 2 * Zlength words + 1 <= INT_MAX /\
    Forall (lit_wf_c n) words /\ NoDup (map lit_var_c words) /\
    record_clause_cert n F M words /\
    msolver_inv n F A_arr A_inst M /\
    ms_capacity_root_propagation_pending M = 0 /\
    msolver_seed_shadow M ” &&
  (solver_rep_levels_at s M lvl **
   IntArray.seg begin 0 (Zlength words) words **
   clause_out # Ptr |->_).

Definition clause_new_post_at
    (s begin finish clause_out lvl n : Z)
    (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (ret : Z) : Assertion :=
  ((“ ret = 1 ” &&
    (EX M' : msolver, EX c : Z,
      “ clause_new_success_transition
          n F A_arr A_inst entry words c M' ” &&
      (solver_rep_levels_at s M' lvl **
       IntArray.seg begin 0 (Zlength words) words **
       clause_out # Ptr |-> c))) ||
   (“ ret = -2 ” &&
    (EX M' : msolver,
      “ clause_new_capacity_failure
          n F A_arr A_inst entry M' words ” &&
      (solver_rep_levels_at s M' lvl **
       IntArray.seg begin 0 (Zlength words) words **
       clause_out # Ptr |-> 0)))).

(** ** The audited seed shadow, and a closed state that carries it.

    [msolver_seed_shadow M := exists z, ms_random_seed M = Z_to_fp64 z /\
    seed_ok z] is a conjunct of [solver_solve_pre] -- the precondition of the
    top-level contract -- and of every other C-facing contract that can reach
    the random facade.  Unlike [msolver_seed_ok] (mere finiteness) it demands
    an EXACT integer shadow, so a witness state must pin its seed field to a
    genuine [Z_to_fp64] image.

    [msat_fp64_zero] cannot serve.  [msat_fp64_zero_no_shadow] below does not
    merely fail to establish the shadow, it REFUTES it: a state whose seed is
    the constructor-level zero satisfies no instance of
    [msolver_seed_shadow].  The witnesses [w0] .. [w4] all set that field, so
    before [w0s] (end of this section) the top-level precondition had no
    closed inhabitant on its pure side.

    The seed used here is MiniSat's own default, [91648253], which lies in the
    recorded seed domain [[1, 2147483646]] fixed by [seed_ok].

    Two deliberate containment decisions.  (1) All reasoning about
    [Z_to_fp64] lives inside [MSatFloatFacts], so the Flocq/reals vocabulary
    is imported there and nowhere else.  (2) [w0] .. [w4] are left ALONE and
    the seeded state [w0s] is built from [w0] by [msolver_reseed]; writing the
    seed into [w0] directly would have made every result that flows through
    those witnesses -- including the two UNSAT endgames and
    [msolver_inv_weak_unsat_inhabited] -- depend on Coq's axiomatisation of
    [R], where today they are all "Closed under the global context".

    Note that any statement mentioning [Z_to_fp64] necessarily depends on that
    axiomatisation: the dependency comes from the STATEMENT, not from these
    proofs.  [Print Assumptions] on [eq_refl : Z_to_fp64 z = Z_to_fp64 z]
    already reports the same four axioms. *)

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

(** [fp32_of_real] is finite and reads back as the rounded real whenever the
    rounded value is inside the binary32 exponent range. *)
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

Lemma fp32_scale_positive_finite :
  msat_fp32_positive_finite (fp32_of_real (1e-20)%R).
Proof.
  apply (fp32_of_real_positive_from_bpow (1e-20)%R (-100) 0); try lia.
  - unfold bpow. simpl. field_simplify; nra.
  - rewrite Rabs_right by lra.
    change (bpow radix2 0) with 1%R. lra.
Qed.


Lemma fp32_search_decay_positive_finite :
  msat_fp32_positive_finite
    (fp32_of_real (1.00100100040435791015625)%R).
Proof.
  apply (fp32_of_real_positive_from_bpow
           (1.00100100040435791015625)%R 0 1); try lia.
  - change (bpow radix2 0) with 1%R. lra.
  - rewrite Rabs_right by lra.
    change (bpow radix2 1) with 2%R. lra.
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

Lemma fp32_count_limit_of_div : forall count inc,
  (0 <= count <= 2147483647)%Z ->
  msat_fp32_nonnegative inc ->
  msat_fp32_count_limit count (fp32_div inc (Z_to_fp32 count)).
Proof.
  intros count inc Hcount Hinc.
  unfold msat_fp32_count_limit. intros Hpositive.
  apply fp32_nonnegative_div_positive_finite; [exact Hinc|].
  apply Z_to_fp32_i32_positive_finite. lia.
Qed.

(** [fp64_of_real] on an in-range argument is finite, and reads back as the
    rounded real.  This is Flocq's [binary_normalize_correct] plus the fact
    that a rounded value is already in [generic_format], so the rounding
    performed inside [binary_normalize] is the identity. *)
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

(** Every 32-bit integer sits well inside the binary64 exponent range. *)
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

(** A positive integer seed rounds to at least one, hence is not zero. *)
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

End MSatFloatFacts.

(** ===== group: act_clause_bump ===== *)
(* Rebuild two watcher slots in increasing index order. The caller chooses
   the order; the prefix/middle/suffix reconstruction is shared. *)
Local Ltac msat_wlists_refold_ordered base i j wm caps Hj :=
  assert (Hpre : Zlength (sublist 0 i wm) = Zlength (sublist 0 i caps))
    by (rewrite !Zlength_sublist by lia; lia);
  assert (Hprefix_w :
    sublist 0 i wm ++ Znth i wm nil :: sublist (i + 1) j wm = sublist 0 j wm)
    by (rewrite (sublist_split 0 j i wm) by lia;
        rewrite (sublist_split i j (i + 1) wm) by lia;
        rewrite (sublist_single nil) by lia; reflexivity);
  assert (Hprefix_c :
    sublist 0 i caps ++ Znth i caps 1 :: sublist (i + 1) j caps = sublist 0 j caps)
    by (rewrite (sublist_split 0 j i caps) by lia;
        rewrite (sublist_split i j (i + 1) caps) by lia;
        rewrite (sublist_single 1) by lia; reflexivity);
  transitivity
    (wlists_rep_from base 0 (sublist 0 i wm) (sublist 0 i caps) **
     vecp_rep (vecp_slot base i) (Znth i wm nil) (Znth i caps 1) **
     wlists_rep_from base (i + 1) (sublist (i + 1) j wm) (sublist (i + 1) j caps) **
     vecp_rep (vecp_slot base j) (Znth j wm nil) (Znth j caps 1) **
     wlists_rep_from base (j + 1) (sublist (j + 1) (Zlength wm) wm)
       (sublist (j + 1) (Zlength caps) caps));
    [ entailer_with lia | ];
  sep_apply (wlists_rep_from_insert_at base 0 i
    (sublist 0 i wm) (Znth i wm nil) (sublist (i + 1) j wm)
    (sublist 0 i caps) (Znth i caps 1) (sublist (i + 1) j caps)
    Hpre ltac:(rewrite Zlength_sublist by lia; lia));
  rewrite Hprefix_w, Hprefix_c;
  sep_apply (wlists_rep_from_insert_at base 0 j
    (sublist 0 j wm) (Znth j wm nil) (sublist (j + 1) (Zlength wm) wm)
    (sublist 0 j caps) (Znth j caps 1) (sublist (j + 1) (Zlength caps) caps)
    ltac:(rewrite !Zlength_sublist by lia; lia)
    ltac:(rewrite Zlength_sublist by lia; lia));
  replace (sublist 0 j wm ++ Znth j wm nil :: sublist (j + 1) (Zlength wm) wm)
    with wm by (apply list_Znth_split; exact Hj);
  replace (sublist 0 j caps ++ Znth j caps 1 :: sublist (j + 1) (Zlength caps) caps)
    with caps by (apply list_Znth_split; lia);
  entailer_with lia.

Lemma wlists_two_remainder_refold__act_clause_bump :
  forall base i j wm caps,
  Zlength wm = Zlength caps ->
  0 <= i < Zlength wm ->
  0 <= j < Zlength wm ->
  i <> j ->
  wlists_two_remainder base i j wm caps **
  vecp_rep (vecp_slot base i) (Znth i wm nil) (Znth i caps 1) **
  vecp_rep (vecp_slot base j) (Znth j wm nil) (Znth j caps 1)
  |-- wlists_rep_from base 0 wm caps.
Proof.
  intros base i j wm caps Hlen Hi Hj Hne.
  unfold wlists_two_remainder.
  destruct (Z.ltb i j) eqn:Eij.
  - apply Z.ltb_lt in Eij.
    msat_wlists_refold_ordered base i j wm caps Hj.
  - apply Z.ltb_ge in Eij. assert (Eji : j < i) by lia.
    msat_wlists_refold_ordered base j i wm caps Hi.
Qed.

Lemma vecp_full_refold__act_clause_bump : forall v p l cap,
  Zlength l = cap ->
  0 < cap <= INT_MAX ->
  vecp_size_addr v # Int |-> Zlength l **
  vecp_cap_addr v # Int |-> cap **
  vecp_ptr_addr v # Ptr |-> p **
  PtrArray.seg p 0 (Zlength l) l
  |-- vecp_rep v l cap.
Proof.
  intros v p l cap Hfull Hcap.
  unfold vecp_rep. Exists p.
  unfold vecp_rep_at.
  split_pure_spatial.
  - rewrite <- Hfull.
    rewrite PtrArray.undef_seg_empty.
    entailer_with lia.
  - dump_pre_spatial.
    pose proof (Zlength_nonneg l). lia.
Qed.

Lemma sublist_replace_Znth_outside_wmap__clause_new :
  forall (l : list (list Z)) i v lo hi,
  0 <= lo <= hi ->
  hi <= Zlength l ->
  0 <= i < Zlength l ->
  (i < lo \/ hi <= i) ->
  sublist lo hi (replace_Znth i v l) = sublist lo hi l.
Proof. msat_sublist_replace_outside (@nil Z). Qed.

Lemma wlists_two_remainder_replace_wm_i__clause_new :
  forall base i j wm caps words,
  Zlength wm = Zlength caps ->
  0 <= i < Zlength wm ->
  0 <= j < Zlength wm ->
  i <> j ->
  wlists_two_remainder base i j wm caps =
  wlists_two_remainder base i j (replace_Znth i words wm) caps.
Proof.
  intros base i j wm caps words Hlen Hi Hj Hne.
  unfold wlists_two_remainder.
  rewrite Zlength_replace_Znth.
  destruct (Z.ltb i j) eqn:Eij.
  - apply Z.ltb_lt in Eij.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm i words 0 i) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm i words (i + 1) j) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm i words (j + 1) (Zlength wm)) by lia.
    reflexivity.
  - apply Z.ltb_ge in Eij. assert (Hji : j < i) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm i words 0 j) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm i words (j + 1) i) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm i words (i + 1) (Zlength wm)) by lia.
    reflexivity.
Qed.

Lemma wlists_two_remainder_replace_wm_j__clause_new :
  forall base i j wm caps words,
  Zlength wm = Zlength caps ->
  0 <= i < Zlength wm ->
  0 <= j < Zlength wm ->
  i <> j ->
  wlists_two_remainder base i j wm caps =
  wlists_two_remainder base i j (replace_Znth j words wm) caps.
Proof.
  intros base i j wm caps words Hlen Hi Hj Hne.
  unfold wlists_two_remainder.
  rewrite Zlength_replace_Znth.
  destruct (Z.ltb i j) eqn:Eij.
  - apply Z.ltb_lt in Eij.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm j words 0 i) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm j words (i + 1) j) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm j words (j + 1) (Zlength wm)) by lia.
    reflexivity.
  - apply Z.ltb_ge in Eij. assert (Hji : j < i) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm j words 0 j) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm j words (j + 1) i) by lia.
    rewrite (sublist_replace_Znth_outside_wmap__clause_new
      wm j words (i + 1) (Zlength wm)) by lia.
    reflexivity.
Qed.

Lemma clause_db_rep_learnt_snoc_rev__clause_new :
  forall db c words,
  MiniSatClause.rep c true words ** clause_db_rep db
  |-- clause_db_rep (db +:: (c, clause_obj_of words true)).
Proof.
  intros db c words.
  transitivity
    (clause_db_rep db **
      clause_db_rep ((c, clause_obj_of words true) :: nil)).
  - simpl. entailer_with lia.
  - apply clause_db_rep_app_intro.
Qed.

Lemma replace_Znth_split_list__clause_new :
  forall {A : Type} (d v : A) i l,
  0 <= i < Zlength l ->
  replace_Znth i v l = sublist 0 i l ++ v :: sublist (i + 1) (Zlength l) l.
Proof.
  intros A d v i l Hi.
  pose proof (list_Znth_split d l i Hi) as E.
  assert (HA : Zlength (sublist 0 i l) = i)
    by (apply Zlength_sublist0; lia).
  rewrite E at 1.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  rewrite HA. replace (i - i) with 0 by lia. reflexivity.
Qed.

Lemma wlists_two_remainder_update_refold__clause_new :
  forall base i j wm caps wi wj,
  Zlength wm = Zlength caps ->
  0 <= i < Zlength wm ->
  0 <= j < Zlength wm ->
  i <> j ->
  wlists_two_remainder base i j wm caps **
  vecp_rep (vecp_slot base i) wi (Znth i caps 1) **
  vecp_rep (vecp_slot base j) wj (Znth j caps 1)
  |-- wlists_rep_from base 0
        (replace_Znth j wj (replace_Znth i wi wm)) caps.
Proof.
  intros base i j wm caps wi wj Hlen Hi Hj Hne.
  pose proof (wlists_two_remainder_refold__act_clause_bump
    base i j (replace_Znth j wj (replace_Znth i wi wm)) caps
    ltac:(rewrite !Zlength_replace_Znth; exact Hlen)
    ltac:(rewrite !Zlength_replace_Znth; exact Hi)
    ltac:(rewrite !Zlength_replace_Znth; exact Hj) Hne) as Hrefold.
  rewrite (Znth_replace_Znth_Diff nil (replace_Znth i wi wm) j i wj)
    in Hrefold by (rewrite ?Zlength_replace_Znth; lia).
  rewrite (Znth_replace_Znth_Same nil wm i wi Hi) in Hrefold.
  rewrite (Znth_replace_Znth_Same nil (replace_Znth i wi wm) j wj)
    in Hrefold by (rewrite Zlength_replace_Znth; exact Hj).
  rewrite <- (wlists_two_remainder_replace_wm_j__clause_new
    base i j (replace_Znth i wi wm) caps wj
    ltac:(rewrite Zlength_replace_Znth; exact Hlen)
    ltac:(rewrite Zlength_replace_Znth; exact Hi)
    ltac:(rewrite Zlength_replace_Znth; exact Hj) Hne) in Hrefold.
  rewrite <- (wlists_two_remainder_replace_wm_i__clause_new
    base i j wm caps wi Hlen Hi Hj Hne) in Hrefold.
  exact Hrefold.
Qed.

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

(** ===== group: clause_cmp ===== *)
(** The [clause_cmp] comparator family.  First, a
    compositional (++) fact about [learnt_sort_rep], the spatial
    representation the sort routine walks (pure shape).  Second, the
    [learnt_cmp_result] lemmas: per the file's own note just above them,
    the [*_two] variants differ only in the [**] order of the spatial
    atoms (same fact, reassociated heap), not in which comparator branch
    they cover; each unfolds [learnt_cmp_result]/[learnt_cmp_lt] to the
    outcome on its stated case, pure arithmetic over the sort keys. *)
Lemma learnt_sort_rep_app_intro__clause_cmp : forall db1 db2 a1 a2,
  List.length db1 = List.length a1 ->
  learnt_sort_rep db1 a1 ** learnt_sort_rep db2 a2 |--
  learnt_sort_rep (db1 ++ db2) (a1 ++ a2).
Proof.
  intros db1. induction db1 as [|[p co] db1 IH];
    intros db2 a1 a2 Hlen.
  - destruct a1 as [|a a1].
    + simpl. entailer_with lia.
    + simpl in Hlen. lia.
  - destruct a1 as [|a a1].
    + simpl in Hlen. lia.
    + simpl in Hlen.
      cbn [List.app learnt_sort_rep].
      Intros_p Hhead.
      sep_apply (IH db2 a1 a2 ltac:(lia)).
      entailer_with lia.
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
  entailer_with lia.
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
  rewrite <- Hlits at 1.
  sep_apply
    (learnt_sort_rep_cons_intro__clause_cmp
       x co post xa apost Htag).
  sep_apply
    (learnt_sort_rep_app_intro__clause_cmp
       pre ((x, co) :: post) apre (xa :: apost) Hlen).
  entailer_with lia.
Qed.

(* Reattach one clause and the untouched segment preceding it. The two
   remainder arms select the clause order explicitly at their call sites. *)
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
    rewrite <- Hxlits at 1; rewrite <- Hylits at 1.
  - msat_learnt_sort_refold_prefix y coy post ya apost Hytag mid amid Hmid.
    msat_learnt_sort_refold_prefix x cox (mid ++ (y, coy) :: post)
      xa (amid ++ ya :: apost) Hxtag pre apre Hpre.
    entailer_with lia.
  - msat_learnt_sort_refold_prefix x cox post xa apost Hxtag mid amid Hmid.
    msat_learnt_sort_refold_prefix y coy (mid ++ (x, cox) :: post)
      ya (amid ++ xa :: apost) Hytag pre apre Hpre.
    entailer_with lia.
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
    Intros cox coy.
    apply coq_prop_imply.
    intros [Hxkey [Hykey [Hxlits Hylits]]].
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
  sepcon_assoc_change.
  rewrite (logic_equiv_sepcon_swap
    (IntArray.seg (clause_lits_addr p) 0 (Zlength l1) l1)
    (clause_hdr_addr p # Int |-> clause_hdr_word true (Zlength l2))
    ((clause_act_addr p # Float |-> a2) **
     IntArray.seg (clause_lits_addr p) 0 (Zlength l2) l2)).
  rewrite (logic_equiv_sepcon_swap
    (clause_act_addr p # Float |-> a1)
    (clause_hdr_addr p # Int |-> clause_hdr_word true (Zlength l2))
    ((IntArray.seg (clause_lits_addr p) 0 (Zlength l1) l1) **
     ((clause_act_addr p # Float |-> a2) **
      IntArray.seg (clause_lits_addr p) 0 (Zlength l2) l2))).
  sep_apply (dup_store_int (clause_hdr_addr p)
    (clause_hdr_word true (Zlength l1))
    (clause_hdr_word true (Zlength l2))).
  entailer_with ltac:(lia).
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
        entailer_with int_auto.
        apply derivable1_truep_intros.
      * cbn [learnt_sort_rep].
        Intros_p Hhead.
        sep_apply (IH activities p co a Htail).
        entailer_with int_auto.
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
    sepcon_assoc_change.
    rewrite (logic_equiv_sepcon_swap (TT)
      (learnt_sort_rep post apost)
      (learnt_clause_snapshot_raw x xlits xa)).
    rewrite (logic_equiv_sepcon_swap
      (learnt_clause_snapshot_raw x (co_lits co) a)
      (learnt_sort_rep post apost)
      ((TT) ** (learnt_clause_snapshot_raw x xlits xa))).
    rewrite (logic_equiv_sepcon_swap
      (learnt_clause_snapshot_raw x (co_lits co) a)
      (TT)
      (learnt_clause_snapshot_raw x xlits xa)).
    sep_apply (learnt_clause_snapshot_raw_dup__clause_cmp x (co_lits co) a xlits xa).
    entailer_with ltac:(lia).
  - cbn [learnt_sort_key] in Hrest.
    destruct Hrest as [[Hx [Hco Ha]] | Hinpost].
    + subst co a. apply derivable1s_coq_prop_r.
      split; [exact Hlits | reflexivity].
    + sep_apply (learnt_sort_rep_key_focus__clause_cmp
        post apost x co a Hinpost).
      sepcon_assoc_change.
      rewrite (logic_equiv_sepcon_swap (TT)
        (learnt_sort_rep pre apre)
        (learnt_clause_snapshot_raw x xlits xa)).
      rewrite (logic_equiv_sepcon_swap
        (learnt_clause_snapshot_raw x (co_lits co) a)
        (learnt_sort_rep pre apre)
        ((TT) ** (learnt_clause_snapshot_raw x xlits xa))).
      rewrite (logic_equiv_sepcon_swap
        (learnt_clause_snapshot_raw x (co_lits co) a)
        (TT)
        (learnt_clause_snapshot_raw x xlits xa)).
      sep_apply (learnt_clause_snapshot_raw_dup__clause_cmp x (co_lits co) a xlits xa).
      entailer_with ltac:(lia).
Qed.

Lemma learnt_cmp_stop_alias__clause_cmp :
  forall db activities x xlits xa,
  msat_fp32_nonnegative xa ->
  learnt_clause_snapshot_raw x xlits xa **
  learnt_sort_alias_remainder db activities x xlits xa |--
  “ learnt_cmp_stop db activities x x ”.
Proof.
  intros db activities x xlits xa Hnonnegative.
  (* Descent to the model.  The conclusion is a [coq_prop] whose proof needs
     [learnt_sort_alias_key_unique__clause_cmp] TWICE, at the SAME model:
     once for the key read at [cox] and once at [coy].  [prop_apply] /
     [derivable1s_coq_prop_r] consume the spatial side once each, and the
     remainder is not duplicable, so the entailment is opened by hand and both
     instances are discharged against the one model [m]. *)
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
    rewrite <- Hylits at 1.
    sep_apply (learnt_sort_rep_cons_intro__clause_cmp
      y coy post ya apost Hytag).
    sep_apply (learnt_sort_rep_app_intro__clause_cmp
      mid ((y, coy) :: post) amid (ya :: apost) Hmid).
    unfold learnt_sort_alias_remainder.
    Exists cox pre (mid ++ (y, coy) :: post)
      apre (amid ++ ya :: apost).
    entailer_with lia.
  - Intros cox coy pre mid post apre amid apost.
    destruct H as
      [Hdb [Hactivities [Hprelen [Hmidlen
       [Hxlits [Hylits [Hxtag [Hytag [Hxnonneg Hynonneg]]]]]]]]].
    assert (Hpre : List.length pre = List.length apre).
    { rewrite !Zlength_correct in Hprelen. lia. }
    assert (Hmid : List.length mid = List.length amid).
    { rewrite !Zlength_correct in Hmidlen. lia. }
    rewrite <- Hylits at 1.
    sep_apply (learnt_sort_rep_cons_intro__clause_cmp
      y coy mid ya amid Hytag).
    sep_apply (learnt_sort_rep_app_intro__clause_cmp
      pre ((y, coy) :: mid) apre (ya :: amid) Hpre).
    unfold learnt_sort_alias_remainder.
    Exists cox (pre ++ (y, coy) :: mid) post
      (apre ++ ya :: amid) apost.
    entailer_with lia.
    + rewrite Hdb.
      change (pre ++ (((y, coy) :: mid) ++ ((x, cox) :: post)) =
        (pre ++ ((y, coy) :: mid)) ++ ((x, cox) :: post)).
      apply app_assoc.
    + rewrite Hactivities.
      change (apre ++ ((ya :: amid) ++ (xa :: apost)) =
        (apre ++ (ya :: amid)) ++ (xa :: apost)).
      apply app_assoc.
    + rewrite !Zlength_app, !Zlength_cons.
      lia.
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
    rewrite <- Hxlits at 1.
    sep_apply (learnt_sort_rep_cons_intro__clause_cmp
      x cox mid xa amid Hxtag).
    sep_apply (learnt_sort_rep_app_intro__clause_cmp
      pre ((x, cox) :: mid) apre (xa :: amid) Hpre).
    unfold learnt_sort_alias_remainder.
    Exists coy (pre ++ (x, cox) :: mid) post
      (apre ++ xa :: amid) apost.
    entailer_with lia.
    + rewrite Hdb.
      change (pre ++ (((x, cox) :: mid) ++ ((y, coy) :: post)) =
        (pre ++ ((x, cox) :: mid)) ++ ((y, coy) :: post)).
      apply app_assoc.
    + rewrite Hactivities.
      change (apre ++ ((xa :: amid) ++ (ya :: apost)) =
        (apre ++ (xa :: amid)) ++ (ya :: apost)).
      apply app_assoc.
    + rewrite !Zlength_app, !Zlength_cons.
      lia.
  - Intros cox coy pre mid post apre amid apost.
    destruct H as
      [Hdb [Hactivities [Hprelen [Hmidlen
       [Hxlits [Hylits [Hxtag [Hytag [Hxnonneg Hynonneg]]]]]]]]].
    assert (Hmid : List.length mid = List.length amid).
    { rewrite !Zlength_correct in Hmidlen. lia. }
    rewrite <- Hxlits at 1.
    sep_apply (learnt_sort_rep_cons_intro__clause_cmp
      x cox post xa apost Hxtag).
    sep_apply (learnt_sort_rep_app_intro__clause_cmp
      mid ((x, cox) :: post) amid (xa :: apost) Hmid).
    unfold learnt_sort_alias_remainder.
    Exists coy pre (mid ++ (x, cox) :: post)
      apre (amid ++ xa :: apost).
    entailer_with lia.
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
  (* Descent to the model, same reason as
     [learnt_cmp_stop_alias__clause_cmp] above: the two alias facts
     [learnt_sort_two_to_alias_x/_y] must be read off the SAME model [m], which
     the one-shot [prop_apply] route cannot do with a non-duplicable
     remainder. *)
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

Lemma solver_shape_assume__search : forall M l lim_cap,
  solver_shape M -> ms_qtail M < ms_cap M ->
  ms_capacity_root_propagation_pending M = 0 ->
  ms_lim_cap M <= lim_cap <= INT_MAX ->
  solver_shape (msolver_assume M l lim_cap).
Proof.
  intros M l lim_cap Hshape Hroom Hpending Hlimcap.
  destruct Hshape as
    [Hsize [Hcap [Htwice [Hassigns [Hlevels [Hreasons [Horderpos
    [Hactivity [Htags [Htrail [Hqhead [Hpendingrange [Hpending01
    [Hpendingcase [Hqtail [Hwm [Hwcaps [Hbinarylits [Hstats
    [Hroot [Hbinarynz Hbinaryeven]]]]]]]]]]]]]]]]]]]]].
  unfold solver_shape, msolver_assume, mt_decide, mt_push. cbn.
  repeat rewrite Zlength_replace_Znth.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  repeat split; try assumption; try lia.
Qed.

(* ================= SECTION msat_propagate_db_update ================= *)

(** * The propagation database-update and watch-scan unlock path.

    [solver_propagate] rewrites a clause's literal list in place, moves the
    entry between watch lists, and may abort on a watcher-vector capacity
    failure.  Every lemma in this section transports one field of the
    invariant bundle -- database well-formedness, the reason map, watcher-map
    exactness, the scan carrier, the trail frontier -- across one of those
    three mutations, for the weak bundle and for [msolver_inv_assuming]
    alike.  The names all end in [__propagate_dbu]. *)

(** ===== group: solver_propagate_db_update_unlock ===== *)
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

(* ================= SECTION msat_clause_new_generic ================= *)

(** * Clause installation, generalised over the learnt selector.

    [clause_new] is called both for a problem clause and for a learned one,
    and the two differ only in which vector the clause pointer is pushed onto
    and in the header word's learnt bit.  Rather than two parallel predicate
    families, this section states one family parameterised by a selector
    [sel] in [{0,1}], together with the layer-by-layer projections
    (accessors, capacity growth, the frame that keeps the OTHER database, the
    installed shape) and the refold lemmas that convert between the selected
    spelling and the two concrete ones.  It sits between the setnvars layer
    above and the [solver_addclause] layer below, whose annotation calls
    both. *)

(* ---------------------------------------------------------------------- *)
(* Layer 0.  Accessors.                                                    *)
(*                                                                         *)
(* QCP has no congruence closure, so every annotation site must SPELL the  *)
(* database the same way the state does.  These are that spelling.  Note   *)
(* db_words is definitionally `map fst` but is NOT syntactically it: the   *)
(* frame writes `map fst (ms_prob M)` and the body writes                  *)
(* `db_words (ms_learnt M)`, so each generalised site keeps the spelling   *)
(* its own predicate already used.                                         *)
(* ---------------------------------------------------------------------- *)

(* THE INDEX IS THE C VARIABLE.  This file already carries the selector
   family this generalisation needs, Z-indexed, with clause_new's own
   polarity (0 = problem/s->clauses, nonzero = learnt/s->learnts):

     solver_selected_db        (type : Z) (M : msolver) : dbmap
     solver_selected_vec       (s type : Z) : Z
     solver_selected_cap       (type : Z) (M : msolver) : Z
     solver_selected_is_learnt (type : Z) : bool

   All are already Extern Coq (declared in solver_qcp_def.h) and already used
   in live annotation text with a SYMBOLIC index, inside solver_simplify's
   `for (type = 0; type < 2; type++)` loop over both databases.  So clause_new
   needs NO new ghost and NO bridging Prop: its own
   `int learnt` parameter is the index, passed straight in.

   Each _gen predicate below takes a TRAILING selector `sel : Z`.  Predicates
   that already had the C's `learnt` as a Z parameter keep it; at an annotation
   site both are the same C variable, and the conjunct `learnt = sel` is then
   `learnt = learnt`.  Keeping them distinct is what lets every gate below stay
   a DEFINITIONAL identity at `sel := 1` rather than an entailment. *)

Lemma sel_db_learnt   : forall M, solver_selected_db 1 M = ms_learnt M.      Proof. reflexivity. Qed.

Lemma sel_db_prob   : forall M, solver_selected_db 0 M = ms_prob M.        Proof. reflexivity. Qed.

Lemma sel_cap_learnt  : forall M, solver_selected_cap 1 M = ms_learnt_cap M. Proof. reflexivity. Qed.

Lemma sel_cap_prob  : forall M, solver_selected_cap 0 M = ms_prob_cap M.   Proof. reflexivity. Qed.

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

Lemma sel_other_cap_learnt : forall M, solver_selected_cap (1 - 1) M = ms_prob_cap M.   Proof. reflexivity. Qed.

Lemma sel_other_cap_prob : forall M, solver_selected_cap (1 - 0) M = ms_learnt_cap M. Proof. reflexivity. Qed.

Lemma sel_other_vec_learnt : forall s, solver_selected_vec s (1 - 1) = &( s # "solver_t" ->ₛ "clauses").
Proof. reflexivity. Qed.

Lemma sel_other_vec_prob : forall s, solver_selected_vec s (1 - 0) = &( s # "solver_t" ->ₛ "learnts").
Proof. reflexivity. Qed.

(* The formula after installation: a learnt clause is entailed by F and does
   not extend it; a problem clause does.  Exactly what
   msolver_inv_install_problem concludes. *)
Definition cn_F (F : cnf) (words : list Z) (sel : Z) : cnf :=
  if Z.eqb sel 0 then F ++ (lits_denote words :: nil) else F.

Lemma cn_F_learnt : forall F w, cn_F F w 1 = F.
Proof. reflexivity. Qed.

Lemma cn_F_prob : forall F w, cn_F F w 0 = F ++ (lits_denote w :: nil).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Layer 1.  Capacity growth targets the SELECTED database.                *)
(* ---------------------------------------------------------------------- *)

(* lib.v has no ms_prob_cap setter -- msolver_with_clause_caps hard-codes
   `ms_prob_cap := ms_prob_cap M`.  So the generic is spelled as its own record
   literal, with the two cap fields swapped by the flag.  At sel = 1 both
   `if`s iota-reduce to exactly msolver_with_clause_caps' fields, which is what
   makes the conservativity lemma below `reflexivity`. *)
Definition msolver_with_clause_caps_gen
    (M : msolver) (db_cap : Z) (wcaps : list Z) (sel : Z) : msolver :=
  msolver_capacity_update M ((if Z.eqb sel 0 then db_cap else ms_prob_cap M)) ((if Z.eqb sel 0 then
    ms_learnt_cap M else db_cap)) (wcaps).

Lemma msolver_with_clause_caps_gen_learnt :
  forall M db_cap wcaps,
    msolver_with_clause_caps_gen M db_cap wcaps 1 =
    msolver_with_clause_caps M db_cap wcaps.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Layer 2.  The frame keeps the OTHER database.                           *)
(*                                                                         *)
(* This is the whole structural cost of the generalisation: exactly two    *)
(* sites swap, the first conjunct of clause_new_vecs_frame and the         *)
(* clause_db_rep argument of clause_new_frame(_at).  Everything else in    *)
(* the frame is database-agnostic and is reproduced verbatim.              *)
(* ---------------------------------------------------------------------- *)

Definition clause_new_vecs_frame_gen
    (s : Z) (M : msolver) (sel : Z) : Assertion :=
  vecp_rep (solver_selected_vec s (1 - sel))
           (map fst (solver_selected_db (1 - sel) M)) (solver_selected_cap (1 - sel) M) **
  veci_rep &( s # "solver_t" ->ₛ "tagged")
           (ms_tagged M) (ms_tagged_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "stack")
           (ms_stack M) (ms_stack_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "order")
           (ms_order M) (ms_order_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) (ms_lim_cap M) **
  veci_rep &( s # "solver_t" ->ₛ "model")
           (ms_model M) (ms_model_cap M).

Lemma clause_new_vecs_frame_gen_learnt :
  forall s M, clause_new_vecs_frame_gen s M 1 = clause_new_vecs_frame s M.
Proof. reflexivity. Qed.

Definition clause_new_frame_gen
    (s : Z) (M : msolver) (sel : Z) : Assertion :=
  EX act asg opos rsn lvl trl tgs : Z,
    clause_new_scalars_frame s M ** solver_fp_rep s M **
    clause_new_vecs_frame_gen s M sel **
    clause_new_ptrs_frame s M act asg opos rsn lvl trl tgs **
    solver_var_arrays_rep M act asg opos rsn lvl tgs **
    solver_trail_array_rep M trl **
    clause_db_rep (solver_selected_db (1 - sel) M) **
    MiniSatClause.rep (ms_binary M) false (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

Lemma clause_new_frame_gen_learnt :
  forall s M, clause_new_frame_gen s M 1 = clause_new_frame s M.
Proof. reflexivity. Qed.

Definition clause_new_frame_at_gen
    (s : Z) (M : msolver) (lvl : Z) (sel : Z) : Assertion :=
  EX act asg opos rsn trl tgs : Z,
    clause_new_scalars_frame s M ** solver_fp_rep s M **
    clause_new_vecs_frame_gen s M sel **
    clause_new_ptrs_frame s M act asg opos rsn lvl trl tgs **
    solver_var_arrays_rep M act asg opos rsn lvl tgs **
    solver_trail_array_rep M trl **
    clause_db_rep (solver_selected_db (1 - sel) M) **
    MiniSatClause.rep (ms_binary M) false (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

Lemma clause_new_frame_at_gen_learnt :
  forall s M lvl, clause_new_frame_at_gen s M lvl 1 = clause_new_frame_at s M lvl.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Layer 3.  Transaction remainder.                                        *)
(* ---------------------------------------------------------------------- *)

Definition clause_new_transaction_rest_gen
    (s begin clause_out wl i0 i1 : Z) (M : msolver)
    (words : list Z) (sel : Z) : Assertion :=
  solver_wlists_handle s wl **
  wlists_two_remainder wl i0 i1 (ms_wm M) (ms_wcaps M) **
  clause_new_frame_gen s M sel.

Lemma clause_new_transaction_rest_gen_learnt :
  forall s begin clause_out wl i0 i1 M words,
    clause_new_transaction_rest_gen s begin clause_out wl i0 i1 M words 1 =
    clause_new_transaction_rest s begin clause_out wl i0 i1 M words.
Proof. reflexivity. Qed.

Definition clause_new_transaction_rest_at_gen
    (s wl i0 i1 : Z) (M : msolver) (lvl : Z) (sel : Z) : Assertion :=
  solver_wlists_handle s wl **
  wlists_two_remainder wl i0 i1 (ms_wm M) (ms_wcaps M) **
  clause_new_frame_at_gen s M lvl sel.

Lemma clause_new_transaction_rest_at_gen_learnt :
  forall s begin clause_out wl i0 i1 M words lvl,
    clause_new_transaction_rest_at_gen s wl i0 i1 M lvl 1 =
    clause_new_transaction_rest_at s begin clause_out wl i0 i1 M words lvl.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Layer 4.  Staging.                                                      *)
(* ---------------------------------------------------------------------- *)

Definition clause_new_stage_rep_at_gen
    (s begin clause_out database watch0 watch1 wl lvl : Z)
    (M : msolver) (words : list Z) (sel : Z) : Assertion :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  “ database = solver_selected_vec s sel /\
    watch0 = vecp_slot wl i0 /\ watch1 = vecp_slot wl i1 /\
    i0 <> i1 ” &&
  (vecp_rep database (map fst (solver_selected_db sel M)) (solver_selected_cap sel M) **
   vecp_rep watch0 (Znth i0 (ms_wm M) (@nil Z)) (Znth i0 (ms_wcaps M) 1) **
   vecp_rep watch1 (Znth i1 (ms_wm M) (@nil Z)) (Znth i1 (ms_wcaps M) 1) **
   clause_db_rep (solver_selected_db sel M) **
   clause_new_transaction_rest_at_gen s wl i0 i1 M lvl sel **
   &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
   IntArray.seg begin 0 (Zlength words) words **
   clause_out # Ptr |-> 0).

Lemma clause_new_stage_rep_at_gen_learnt :
  forall s begin clause_out database watch0 watch1 wl lvl M words,
    clause_new_stage_rep_at_gen s begin clause_out database watch0 watch1 wl lvl M words 1 =
    clause_new_stage_rep_at s begin clause_out database watch0 watch1 wl lvl M words.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Layer 4b.  Capacity progress.                                           *)
(*                                                                         *)
(* THE GAP THIS CLOSES.  The shipped `clause_new_caps_progress` threads     *)
(* `msolver_with_clause_caps`, which sets ms_learnt_cap and PINS            *)
(* `ms_prob_cap := ms_prob_cap entry`.  On the problem path the C calls     *)
(* vecp_reserve(&s->clauses), which grows ms_prob_cap -- so after that      *)
(* reserve NO disjunct is satisfiable (1 needs current = entry; 2-4 can     *)
(* only move the learnt cap).  The false arm would be unprovable, and the   *)
(* sel=1-only gates above cannot see it by construction.                 *)
(* ---------------------------------------------------------------------- *)

Definition clause_new_caps_progress_gen
    (entry : msolver) (words : list Z) (current : msolver)
    (sel : Z) : Prop :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  current = entry \/
  (exists db_cap,
     current = msolver_with_clause_caps_gen
       entry db_cap (ms_wcaps entry) sel) \/
  (exists db_cap cap0,
     current = msolver_with_clause_caps_gen entry db_cap
       (replace_Znth i0 cap0 (ms_wcaps entry)) sel) \/
  (exists db_cap cap0 cap1,
     current = msolver_with_clause_caps_gen entry db_cap
       (replace_Znth i1 cap1
         (replace_Znth i0 cap0 (ms_wcaps entry))) sel).

Lemma clause_new_caps_progress_gen_learnt :
  forall entry words current,
    clause_new_caps_progress_gen entry words current 1 =
    clause_new_caps_progress entry words current.
Proof. reflexivity. Qed.

(* The capacity-failure path was learnt-pinned too, one level deeper:
   [solver_capacity_exhausted] offers only the learnt database or a
   watch list as the exhausted vector, so a PROBLEM-database capacity failure
   satisfies neither disjunct.  It has 22 other consumers in lib.v, so it is
   generalised alongside rather than edited in place.  Neither it nor
   [solver_internal_capacity_ready] is named in any VC statement -- both live
   only inside definition bodies -- so this costs no re-emission. *)

Definition solver_capacity_exhausted_gen (M : msolver) (sel : Z) : Prop :=
  vector_capacity_exhausted
    (Zlength (solver_selected_db sel M)) (solver_selected_cap sel M) \/
  exists i,
    0 <= i < Zlength (ms_wm M) /\
    vector_capacity_exhausted
      (Zlength (Znth i (ms_wm M) (@nil Z)))
      (Znth i (ms_wcaps M) 0).

Definition solver_internal_capacity_ready_gen
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (M : msolver) (sel : Z) : Prop :=
  solver_propagation_inv n F A_arr (PropagationStable A_inst) M /\
  solver_capacity_exhausted_gen M sel /\ msolver_seed_shadow M.

Definition clause_new_capacity_failure_gen
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry current : msolver) (words : list Z) (sel : Z) : Prop :=
  clause_new_caps_progress_gen entry words current sel /\
  solver_internal_capacity_ready_gen n F A_arr A_inst current sel.

Lemma clause_new_capacity_failure_gen_learnt :
  forall n F A_arr A_inst entry current words,
    clause_new_capacity_failure_gen n F A_arr A_inst entry current words 1 =
    clause_new_capacity_failure n F A_arr A_inst entry current words.
Proof. reflexivity. Qed.

(* The failure arm keeps F: nothing was installed, so the formula does not
   grow on either path.  Only the SUCCESS arm uses cn_F. *)

(* ---------------------------------------------------------------------- *)
(* The ENTRY certificate.                                                   *)
(*                                                                          *)
(* [problem_clause_cert] carries [In (lits_denote words) F], which is right *)
(* for the state AFTER the install (the post spells F as [cn_F F words 0] = *)
(* [F ++ [lits_denote words]], so membership is immediate) but wrong for the *)
(* state BEFORE it: [solver_addclause] installs a clause that is not yet in  *)
(* F and could never supply it.  [msolver_inv_install_problem]            *)
(* confirms the design -- it concludes [msolver_inv n (F ++ [lits_denote     *)
(* words])] and takes NO membership hypothesis.  So the precondition uses    *)
(* the pending cert and the postcondition keeps the full one.               *)
(* ---------------------------------------------------------------------- *)

Definition problem_clause_pending_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) : Prop :=
  2 <= Zlength words /\ Forall (lit_wf_c n) words /\
  NoDup (map lit_var_c words) /\
  Forall (fun l => Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0) words.

Definition clause_install_pending_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) (learnt : bool) : Prop :=
  if learnt then record_clause_cert n F M words
            else problem_clause_pending_cert n F M words.

Definition clause_new_stage_ready_gen
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry current : msolver) (words : list Z) (sel : Z) : Prop :=
  2 <= Zlength words /\ 2 * Zlength words + 1 <= INT_MAX /\
  clause_new_caps_progress_gen entry words current sel /\
  msolver_inv n F A_arr A_inst current /\
  ms_capacity_root_propagation_pending current = 0 /\
  msolver_seed_shadow current /\
  clause_install_pending_cert n F current words (solver_selected_is_learnt sel).

Lemma clause_new_stage_ready_gen_learnt :
  forall n F A_arr A_inst entry current words,
    clause_new_stage_ready_gen n F A_arr A_inst entry current words 1 =
    clause_new_stage_ready n F A_arr A_inst entry current words.
Proof. reflexivity. Qed.

Definition clause_new_reserved_rooms_gen
    (stage : Z) (words : list Z) (M : msolver) (sel : Z) : Prop :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  (1 <= stage -> Zlength (map fst (solver_selected_db sel M)) < solver_selected_cap sel M) /\
  (2 <= stage -> Zlength (Znth i0 (ms_wm M) (@nil Z)) < Znth i0 (ms_wcaps M) 1) /\
  (3 <= stage -> Zlength (Znth i1 (ms_wm M) (@nil Z)) < Znth i1 (ms_wcaps M) 1).

Lemma clause_new_reserved_rooms_gen_learnt :
  forall stage words M,
    clause_new_reserved_rooms_gen stage words M 1 =
    clause_new_reserved_rooms stage words M.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Layer 5.  Transition and contract.                                      *)
(* ---------------------------------------------------------------------- *)

Definition clause_new_success_transition_gen
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (c : Z) (sel : Z)
    (M' : msolver) : Prop :=
  exists Mcaps,
    clause_new_caps_progress_gen entry words Mcaps sel /\
    clause_allocator_fresh Mcaps c /\
    M' = msolver_install_clause Mcaps c words (solver_selected_is_learnt sel) /\
    msolver_inv n (cn_F F words sel) A_arr A_inst M' /\
    ms_capacity_root_propagation_pending M' = 0 /\
    msolver_seed_shadow M' /\
    clause_install_cert n (cn_F F words sel) M' words (solver_selected_is_learnt sel).

Lemma clause_new_success_transition_gen_learnt :
  forall n F A_arr A_inst entry words c M',
    clause_new_success_transition_gen n F A_arr A_inst entry words c 1 M' =
    clause_new_success_transition n F A_arr A_inst entry words c M'.
Proof. reflexivity. Qed.

Definition clause_new_pre_at_gen
    (s begin finish learnt database clause_out lvl n : Z)
    (F : cnf) (A_arr A_inst : list literal)
    (M : msolver) (words : list Z) (sel : Z) : Assertion :=
  “ learnt = sel /\
    database = solver_selected_vec s sel /\
    finish = begin + Zlength words * sizeof(INT) /\
    2 <= Zlength words /\ 2 * Zlength words + 1 <= INT_MAX /\
    Forall (lit_wf_c n) words /\ NoDup (map lit_var_c words) /\
    clause_install_pending_cert n F M words (solver_selected_is_learnt sel) /\
    msolver_inv n F A_arr A_inst M /\
    ms_capacity_root_propagation_pending M = 0 /\
    msolver_seed_shadow M ” &&
  (solver_rep_levels_at s M lvl **
   IntArray.seg begin 0 (Zlength words) words **
   clause_out # Ptr |->_).

Lemma clause_new_pre_at_gen_learnt :
  forall s begin finish learnt database clause_out lvl n F A_arr A_inst M words,
    clause_new_pre_at_gen s begin finish learnt database clause_out lvl n
      F A_arr A_inst M words 1 =
    clause_new_pre_at s begin finish learnt database clause_out lvl n
      F A_arr A_inst M words.
Proof. reflexivity. Qed.

(** The named watch-list address connects the live table to its unused growth
    tail. Keeping the same [wl] in both assertions lets callers reassemble
    [solver_rep_growable] after clause installation. *)

Definition solver_rep_levels_wl_at (s : Z) (M : msolver) (wl lvl : Z) : Assertion :=
  “ solver_shape M ” &&
  ((EX act asg opos rsn trl tgs : Z,
      solver_nonlevel_rep_at s M wl act asg opos rsn trl tgs) **
   solver_levels_slice_at s M lvl).

(** Closing the named view existentially hides the watch-list address.
    The generic learnt-clause postcondition uses this bridge. *)


Lemma solver_rep_levels_wl_at_close : forall s M wl lvl,
  solver_rep_levels_wl_at s M wl lvl |-- solver_rep_levels_at s M lvl.
Proof.
  intros s M wl lvl. unfold solver_rep_levels_at, solver_rep_levels_wl_at,
    solver_nonlevel_rep.
  Intros. Intros act asg opos rsn trl tgs.
  entailer_with lia. Exists wl act asg opos rsn trl tgs. entailer_with lia.
Qed.

(** Preserve [wl] through both clause-creation outcomes so callers can retain
    its growth-tail ownership. *)

Definition clause_new_post_at_gen
    (s begin clause_out lvl n : Z)
    (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (ret : Z) (sel : Z) (wl : Z) : Assertion :=
  ((“ ret = 1 ” &&
    (EX M' : msolver, EX c : Z,
      “ clause_new_success_transition_gen
          n F A_arr A_inst entry words c sel M' ” &&
      (solver_rep_levels_wl_at s M' wl lvl **
       IntArray.seg begin 0 (Zlength words) words **
       clause_out # Ptr |-> c))) ||
   (“ ret = -2 ” &&
    (EX M' : msolver,
      “ clause_new_capacity_failure_gen
          n F A_arr A_inst entry M' words sel ” &&
      (solver_rep_levels_wl_at s M' wl lvl **
       IntArray.seg begin 0 (Zlength words) words **
       clause_out # Ptr |-> 0)))).

Lemma clause_new_post_at_gen_learnt :
  forall s begin finish clause_out lvl n F A_arr A_inst entry words ret wl,
    clause_new_post_at_gen s begin clause_out lvl n F A_arr A_inst
      entry words ret 1 wl
    |-- clause_new_post_at s begin finish clause_out lvl n F A_arr A_inst
          entry words ret.
Proof.
  intros. unfold clause_new_post_at_gen, clause_new_post_at.
  rewrite ?clause_new_success_transition_gen_learnt,
          ?clause_new_capacity_failure_gen_learnt.
  apply derivable1_orp_elim.
  - rewrite <- derivable1_orp_intros1.
    Intros M' c. Exists M' c.
    sep_apply solver_rep_levels_wl_at_close. entailer_with lia.
  - rewrite <- derivable1_orp_intros2.
    Intros M'. Exists M'.
    sep_apply solver_rep_levels_wl_at_close. entailer_with lia.
Qed.

(* The generic snoc refold: the shipped one is hard-coded at [true]. *)
Lemma clause_db_rep_snoc_rev_gen : forall db c words b,
  MiniSatClause.rep c b words ** clause_db_rep db
  |-- clause_db_rep (db +:: (c, clause_obj_of words b)).
Proof.
  intros db c words b.
  transitivity
    (clause_db_rep db ** clause_db_rep ((c, clause_obj_of words b) :: nil)).
  - simpl. entailer_with lia.
  - apply clause_db_rep_app_intro.
Qed.
