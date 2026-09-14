Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From SumLib Require Import Sum ZRange.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import naive_C_Rules.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

From FP Require Import SetsFixedpoints PartialOrder_Setoid BourbakiWitt.
From GraphLib Require Import graph_basic reachable_basic.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrLoop
                               MonadErrHoarePartial monadesafe_lib.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import Kosaraju SCC
  KosarajuCRefinement.
Export MonadNotation.
Local Open Scope monad.

(* Re-import GraphLib's reachable_basic AFTER the MonadErr imports so that the
   graph step (G -> V -> V -> Prop) stays in scope; MonadErrBasic's Section
   monadop also declares a `step : Type` that would otherwise shadow it. *)
From GraphLib Require Import reachable_basic.
Export MonadNotation.
Local Open Scope monad.
Local Open Scope order_scope.
(* Re-open Z_scope AFTER order_scope so that `<=`/`>=` on Z keep resolving to
   Z.le/Z.ge (order_scope defines `<=` as the Order typeclass `order_rel`,
   which would otherwise shadow Z comparisons).  Program equivalence keeps
   using the order_scope `==` notation via the type-based disambiguation. *)
Local Open Scope Z_scope.
Local Open Scope sac.

(* ================================================================= *)
(* Adjacency-list graph carrier (directed, abstract).                *)
(*   adj_fwd !! u = forward (out) neighbours of u                    *)
(*   adj_rev !! u = reversed (in) neighbours of u                    *)
(*   This is the abstract graph the Kosaraju monad reasons about.    *)
(*   The C side stores the same graph in CSR layout (adj_col +       *)
(*   adj_row); the refinement relates the CSR arrays to adj_rev.     *)
(* ================================================================= *)

Record AdjGraph := MkAdjGraph {
  adj_verts : Z;
  adj_fwd   : list (list Z);
  adj_rev   : list (list Z);
}.

Definition adj_vvalid (g : AdjGraph) (v : Z) : Prop :=
  (0 <= v < adj_verts g)%Z.

Definition adj_evalid (g : AdjGraph) (e : Z * Z) : Prop :=
  let (u, v) := e in adj_vvalid g u /\ adj_vvalid g v.

Definition adj_step_aux (g : AdjGraph) (e : Z * Z) (x y : Z) : Prop :=
  e = (x, y) /\
  adj_vvalid g x /\
  adj_vvalid g y /\
  In y (nth (Z.to_nat x) (adj_fwd g) nil).

(* gvalid: well-formed adjacency list.  The converse is guarded because
   Z.to_nat maps negative integers to zero, which is not a graph index. *)
Definition AdjGraphValid (g : AdjGraph) : Prop :=
  (Zlength (adj_fwd g) = adj_verts g)%Z /\
  (Zlength (adj_rev g) = adj_verts g)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_fwd g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
    forall v, In v (nth (Z.to_nat u) (adj_rev g) nil) -> (0 <= v < adj_verts g)%Z) /\
  (forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    In v (nth (Z.to_nat u) (adj_fwd g) nil) <->
    In u (nth (Z.to_nat v) (adj_rev g) nil)).

(* ================================================================= *)
(* Graph type-class instances for AdjGraph.                          *)
(* ================================================================= *)

#[export] Instance AdjGraph_graph : Graph AdjGraph Z (Z * Z) := {|
  graph_basic.vvalid   := adj_vvalid;
  graph_basic.evalid   := adj_evalid;
  graph_basic.step_aux := adj_step_aux;
|}.


#[export] Instance AdjGraph_gvalid : GValid AdjGraph := AdjGraphValid.

#[export] Instance AdjGraph_stepvalid : StepValid AdjGraph Z (Z * Z).
Proof.
  constructor; intros g e x y Hstep.
  - destruct Hstep as [_ [Hvx [_ _]]]. exact Hvx.
  - destruct Hstep as [_ [_ [Hvy _]]]. exact Hvy.
  - destruct Hstep as [Heq [Hvx [Hvy _]]]. subst e.
    unfold adj_evalid. simpl. split; assumption.
Defined.

#[export] Instance AdjGraph_stepuniquedirected : StepUniqueDirected AdjGraph Z (Z * Z).
Proof.
  constructor; intros g e x1 y1 x2 y2 _ H1 H2.
  destruct H1 as [He1 _]. destruct H2 as [He2 _].
  rewrite He1 in He2. injection He2 as Hx Hy. subst. split; reflexivity.
Defined.

#[export] Instance AdjGraph_finitegraph : FiniteGraph AdjGraph Z (Z * Z).
Proof.
  refine {| graph_basic.listV := fun g => map Z.of_nat (seq 0 (Z.to_nat (adj_verts g))) |}.
  intros g Hg v Hv. unfold adj_vvalid in Hv.
  destruct Hv as [Hv1 Hv2].
  apply in_map_iff. exists (Z.to_nat v). split.
  - lia.
  - apply in_seq. lia.
Defined.

(* ================================================================= *)
(* Concrete KosarajuGraph packaging over AdjGraph.                   *)
(* Wraps the Section-parameterised definitions into closed,          *)
(* parameter-free symbols exportable to the C side.                  *)
(* ================================================================= *)

Definition KG : KosarajuGraph AdjGraph Z (Z * Z) :=
  {| kos_graph    := AdjGraph_graph;
     kos_gvalid   := AdjGraph_gvalid;
     kos_stepvalid := AdjGraph_stepvalid;
     kos_unique   := AdjGraph_stepuniquedirected;
     kos_finite   := AdjGraph_finitegraph;
  |}.

(* The Kosaraju abstract state, closed over V = Z. *)
Definition KSt : Type := @St Z.

(* A concrete (empty) adjacency-list graph used to instantiate the
   Section-parameterised monad programs into closed, parameter-free
   symbols.  The actual graph contents live on the C heap side; this
   carrier only carries the type-level packaging. *)
Definition empty_adj : AdjGraph := {| adj_verts := 0; adj_fwd := nil; adj_rev := nil |}.

Lemma empty_adj_valid : gvalid empty_adj.
Proof.
  unfold empty_adj.
  change (gvalid {| adj_verts := 0; adj_fwd := nil; adj_rev := nil |})
    with (AdjGraphValid {| adj_verts := 0; adj_fwd := nil; adj_rev := nil |}).
  unfold AdjGraphValid. simpl. unfold Zlength. simpl.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [intros u [Hu1 Hu2] v Hv; lia|].
  split; [intros u [Hu1 Hu2] v Hv; lia|].
  intros u v. split.
  - intros Hc; destruct (Z.to_nat u); simpl in Hc; exfalso; exact Hc.
  - intros Hc; destruct (Z.to_nat v); simpl in Hc; exfalso; exact Hc.
Qed.

(* ================================================================= *)
(* Closed monad program symbols, instantiating the Section-           *)
(* parameterised DFS_finish / DFS_scc over empty_adj.  These are the  *)
(* high-level (mathematical) specs the C functions refine.            *)
(*                                                                   *)
(* Continuation forms (dfs_finish_from / dfs_scc_from) and the C-side *)
(* preconditions (pre_dfs1 / pre_dfs2) are added by the annotation    *)
(* phase (annotation_scratch_lib -> integrated here once checked).    *)
(* ================================================================= *)

Definition dfs_finish (g : AdjGraph) (u : Z) : program KSt unit :=
  @DFS_finish AdjGraph Z (Z * Z) KG g u.

Definition dfs_finish_schedule (g : AdjGraph) (start fuel : Z) : program KSt unit :=
  @kosaraju_finish_schedule AdjGraph Z (Z * Z) KG g
    (fun i => Z.of_nat i) (Z.to_nat start) (Z.to_nat fuel).

Definition dfs_finish_scheduleK (g : AdjGraph) (start fuel : Z)
  (_ : unit) : program KSt unit :=
  dfs_finish_schedule g start fuel.

Definition dfs_scc (g : AdjGraph) (root u : Z) : program KSt unit :=
  @DFS_scc AdjGraph Z (Z * Z) KG g root u.

(* A case-local phase-2 scheduling bridge.  The scheduled monad program
   chooses between skipping an already visited root and running the C-shaped
   [visit2; set_scc_id; dfs_scc] iteration.  The residual program is passed
   into both branches, so the [visited2] condition is evaluated in the actual
   current state rather than being classified at [init_st]. *)
Definition phase2_c_step (g : AdjGraph) (root : Z) (k : program KSt unit)
  : program KSt unit :=
  if_else (fun st => @visited2 Z st root)
    k
    (visit2 root;; set_scc_id root root;; dfs_scc g root root;; k).

Definition phase2_c_schedule (g : AdjGraph) (root_at : nat -> Z)
           (start fuel : nat) : program KSt unit :=
  @kosaraju_scc_schedule AdjGraph Z (Z * Z) KG g root_at start fuel.

Lemma phase2_c_schedule_step :
  forall (g : AdjGraph) (root_at : nat -> Z) (start fuel : nat),
    phase2_c_schedule g root_at start (S fuel) =
    phase2_c_step g (root_at start)
      (phase2_c_schedule g root_at (S start) fuel).
Proof.
  intros g root_at start fuel.
  unfold phase2_c_schedule, phase2_c_step, dfs_scc.
  rewrite kosaraju_scc_schedule_step.
  reflexivity.
Qed.

Lemma dfs_finish_schedule_done :
  forall (g : AdjGraph) (start : Z),
    dfs_finish_schedule g start 0 = ret tt.
Proof.
  intros g start.
  unfold dfs_finish_schedule.
  rewrite Z2Nat.inj_0.
  apply kosaraju_finish_schedule_done.
Qed.

Lemma dfs_finish_schedule_step :
  forall (g : AdjGraph) (start fuel : Z),
    0 <= start ->
    0 <= fuel ->
    dfs_finish_schedule g start (fuel + 1) =
    if_else (fun st => @visited1 Z st start)
      (dfs_finish_schedule g (start + 1) fuel)
      (dfs_finish g start;;
       dfs_finish_schedule g (start + 1) fuel).
Proof.
  intros g start fuel Hstart Hfuel.
  unfold dfs_finish_schedule, dfs_finish.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  rewrite kosaraju_finish_schedule_step.
  rewrite Z2Nat.id by exact Hstart.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

Lemma dfs_finish_schedule_phase1_order :
  forall (g : AdjGraph) (n : Z),
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    Hoare (fun st => st = @init_st Z)
      (dfs_finish_schedule g 0 n)
      (fun _ st => @Phase1_Order AdjGraph Z (Z * Z) KG g st).
Proof.
  intros g n Hvalid Hverts Hn.
  unfold dfs_finish_schedule.
  change (Z.to_nat 0) with 0%nat.
  eapply (@kosaraju_finish_schedule_phase1_order
    AdjGraph Z (Z * Z) KG g Hvalid (fun i => Z.of_nat i) 0%nat (Z.to_nat n)).
  - intros v Hv.
    change (adj_vvalid g v) in Hv.
    unfold adj_vvalid in Hv.
    exists (Z.to_nat v).
    split.
    + assert (Hv_n : 0 <= v < n) by lia.
      rewrite Nat.add_0_l.
      pose proof (proj2 Hv_n) as Hvlt.
      apply Z2Nat.inj_lt in Hvlt; lia.
    + rewrite Z2Nat.id by lia. reflexivity.
  - intros i Hi.
    change (adj_vvalid g (Z.of_nat i)).
    unfold adj_vvalid.
    rewrite Hverts.
    rewrite Nat.add_0_l in Hi.
    split.
    + apply Nat2Z.is_nonneg.
    + assert (Hlt : Z.of_nat i < Z.of_nat (Z.to_nat n)).
      { apply Nat2Z.inj_lt. lia. }
      rewrite Z2Nat.id in Hlt by lia.
      exact Hlt.
Qed.

Lemma dfs_finish_unfold : forall (g : AdjGraph) (u : Z),
  gvalid g ->
  @PartialOrder_Setoid.equiv (MonadErr.M KSt unit) _
    (dfs_finish g u) (@DFS_finish_f AdjGraph Z (Z * Z) KG g (dfs_finish g) u).
Proof. intros g u Hg. unfold dfs_finish.
  assert (Hg' : @gvalid AdjGraph (@kos_gvalid AdjGraph Z (Z * Z) KG) g) by exact Hg.
  exact (DFS_finish_unfold g u). Qed.

Lemma dfs_scc_unfold : forall (g : AdjGraph) (root u : Z),
  gvalid g ->
  @PartialOrder_Setoid.equiv (MonadErr.M KSt unit) _
    (dfs_scc g root u) (@DFS_scc_f AdjGraph Z (Z * Z) KG g root (dfs_scc g root) u).
Proof. intros g root u Hg. unfold dfs_scc.
  assert (Hg' : @gvalid AdjGraph (@kos_gvalid AdjGraph Z (Z * Z) KG) g) by exact Hg.
  exact (DFS_scc_unfold g root u). Qed.

Definition applyf {A B : Type} (f : A -> B) (a : A) := f a.

(* ================================================================= *)
(* CSR layout helpers (pure mathematical).                            *)
(*   m_of row_l      = row_l[length-1] = packed neighbour count       *)
(*   csr_lo u row_l  = row_l[u]       = start offset of u's neighbours*)
(*   csr_hi u row_l  = row_l[u+1]     = end offset of u's neighbours  *)
(* ================================================================= *)

Definition m_of (row_l : list Z) : Z :=
  Znth (Zlength row_l - 1) row_l 0.

Definition csr_lo (u : Z) (row_l : list Z) : Z :=
  Znth u row_l 0.

Definition csr_hi (u : Z) (row_l : list Z) : Z :=
  Znth (u + 1) row_l 0.

Definition zrange_sum_Znth (lo hi : Z) (l : list Z) : Z :=
  Sum.sum (fun i => lo <= i < hi) (fun i => Znth i l 0).

Definition transpose_count_ready (n j : Z) (cnt_l : list Z) : Prop :=
  zrange_sum_Znth 0 n cnt_l = j /\
  (forall k, 0 <= k < n -> 0 <= Znth k cnt_l 0).

Definition transpose_prefix_inv
  (n m v sum_v : Z) (rr_l cnt_l : list Z) : Prop :=
  zrange_sum_Znth 0 n cnt_l = m /\
  sum_v = zrange_sum_Znth 0 v cnt_l /\
  (forall k, 0 <= k < n -> 0 <= Znth k cnt_l 0) /\
  (forall k, v <= k < n -> Znth k rr_l 0 = Znth k cnt_l 0).

Definition zrange_count_value (lo hi v : Z) (col_l : list Z) : Z :=
  Sum.sum (fun i => lo <= i < hi)
          (fun i => if Z.eq_dec (Znth i col_l 0) v then 1 else 0).

Definition transpose_scatter_inv
  (n m j : Z) (fadj_col_l rr_l pos_l : list Z) : Prop :=
  0 <= j <= m /\
  n <= Zlength pos_l /\
  (forall v, 0 <= v < n ->
     Znth v pos_l 0 =
       Znth v rr_l 0 + zrange_count_value 0 j v fadj_col_l) /\
  (forall v, 0 <= v < n ->
     0 <= Znth v rr_l 0 /\
     Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l <= m).

Definition transpose_scatter_rows
  (n m : Z) (fadj_col_l rr_l : list Z) : Prop :=
  Zlength rr_l = n + 1 /\
  m_of rr_l = m /\
  (forall v, 0 <= v < n ->
     csr_hi v rr_l =
       Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l) /\
  (forall a b, 0 <= a < n -> 0 <= b < n -> a < b ->
     csr_hi a rr_l <= csr_lo b rr_l).

Definition transpose_scatter_contents
  (g : AdjGraph) (n j : Z)
  (fadj_row_l fadj_col_l rr_l rc_l : list Z) : Prop :=
  (forall dst p, 0 <= dst < n ->
     csr_lo dst rr_l <= p <
       Znth dst rr_l 0 + zrange_count_value 0 j dst fadj_col_l ->
     0 <= Znth p rc_l 0 < n) /\
  (forall dst src, 0 <= dst < n -> 0 <= src < n ->
     ((exists p,
         csr_lo dst rr_l <= p <
           Znth dst rr_l 0 + zrange_count_value 0 j dst fadj_col_l /\
         Znth p rc_l 0 = src) <->
      (exists t,
         0 <= t < j /\
         csr_lo src fadj_row_l <= t < csr_hi src fadj_row_l /\
         Znth t fadj_col_l 0 = dst))).

Definition transpose_count_values
  (n j : Z) (fadj_col_l cnt_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    Znth v cnt_l 0 = zrange_count_value 0 j v fadj_col_l.

Definition transpose_prefix_offsets
  (n v : Z) (rr_l pos_l cnt_l : list Z) : Prop :=
  n <= Zlength rr_l /\
  n <= Zlength pos_l /\
  (forall k, 0 <= k < v ->
     Znth k rr_l 0 = zrange_sum_Znth 0 k cnt_l /\
     Znth k pos_l 0 = zrange_sum_Znth 0 k cnt_l) /\
  (forall k, v <= k < n ->
     Znth k rr_l 0 = Znth k cnt_l 0).

Lemma zrange_sum_Znth_nonneg :
  forall lo hi l,
    (forall k, lo <= k < hi -> 0 <= Znth k l 0) ->
    0 <= zrange_sum_Znth lo hi l.
Proof.
  intros lo hi l Hnonneg.
  unfold zrange_sum_Znth.
  apply sum_nonneg. exact Hnonneg.
Qed.

Lemma zrange_sum_Znth_split :
  forall lo mid hi l,
    lo <= mid <= hi ->
    zrange_sum_Znth lo hi l =
    zrange_sum_Znth lo mid l + zrange_sum_Znth mid hi l.
Proof.
  intros lo mid hi l Hmid.
  unfold zrange_sum_Znth.
  apply sum_Z_range_split. exact Hmid.
Qed.

Lemma zrange_sum_Znth_single :
  forall i l,
    zrange_sum_Znth i (i + 1) l = Znth i l 0.
Proof.
  intros i l.
  unfold zrange_sum_Znth.
  exact (sum_Z_range_single i (fun k => Znth k l 0)).
Qed.

Lemma zrange_count_value_nonneg :
  forall lo hi v col_l,
    0 <= zrange_count_value lo hi v col_l.
Proof.
  intros lo hi v col_l.
  unfold zrange_count_value.
  destruct (Z_le_dec lo hi) as [Hle|Hnle].
  - assert (Hpoint :
      forall i : Z, lo <= i < hi ->
        0 <= (if Z.eq_dec (Znth i col_l 0) v then 1 else 0)).
    { intros i Hi. destruct (Z.eq_dec (Znth i col_l 0) v); lia. }
    pose proof (sum_Z_range_lower_bound lo hi
                  (fun i => if Z.eq_dec (Znth i col_l 0) v then 1 else 0)
                  0 Hle Hpoint) as H.
    lia.
  - rewrite sum_Z_range_empty by lia. lia.
Qed.

Lemma zrange_count_value_mono :
  forall lo mid hi v col_l,
    lo <= mid <= hi ->
    zrange_count_value lo mid v col_l <=
    zrange_count_value lo hi v col_l.
Proof.
  intros lo mid hi v col_l Hmid.
  unfold zrange_count_value.
  rewrite (sum_Z_range_split lo mid hi
             (fun i => if Z.eq_dec (Znth i col_l 0) v then 1 else 0))
    by lia.
  pose proof (sum_Z_range_lower_bound mid hi
                (fun i => if Z.eq_dec (Znth i col_l 0) v then 1 else 0) 0).
  assert (0 <= Sum.sum (fun i : Z => mid <= i < hi)
                    (fun i : Z => if Z.eq_dec (Znth i col_l 0) v then 1 else 0)).
  { assert (Hpoint :
      forall i : Z, mid <= i < hi ->
        0 <= (if Z.eq_dec (Znth i col_l 0) v then 1 else 0)).
    { intros i Hi. destruct (Z.eq_dec (Znth i col_l 0) v); lia. }
    pose proof (H ltac:(lia) Hpoint).
    lia. }
  lia.
Qed.

Lemma zrange_count_value_extend_hit :
  forall lo hi v col_l,
    lo <= hi ->
    Znth hi col_l 0 = v ->
    zrange_count_value lo (hi + 1) v col_l =
    zrange_count_value lo hi v col_l + 1.
Proof.
  intros lo hi v col_l Hle Hhit.
  unfold zrange_count_value.
  rewrite sum_Z_range_extend_right by lia.
  rewrite Hhit.
  destruct (Z.eq_dec v v); lia.
Qed.

Lemma transpose_scatter_inv_start :
  forall n m rr_l pos_l fadj_col_l,
    0 <= m ->
    n <= Zlength pos_l ->
    (forall v, 0 <= v < n -> Znth v pos_l 0 = Znth v rr_l 0) ->
    (forall v, 0 <= v < n ->
       0 <= Znth v rr_l 0 /\
       Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l <= m) ->
    transpose_scatter_inv n m 0 fadj_col_l rr_l pos_l.
Proof.
  intros n m rr_l pos_l fadj_col_l Hm Hlen Hpos Hbound.
  unfold transpose_scatter_inv.
  split; [lia|].
  split; [exact Hlen|].
  split.
  - intros v Hv. rewrite Hpos by exact Hv.
    unfold zrange_count_value.
    rewrite sum_Z_range_empty by lia.
    lia.
  - exact Hbound.
Qed.

Lemma transpose_scatter_inv_current_bound :
  forall n m j fadj_col_l rr_l pos_l v,
    transpose_scatter_inv n m j fadj_col_l rr_l pos_l ->
    0 <= v < n ->
    0 <= j < m ->
    Znth j fadj_col_l 0 = v ->
    0 <= Znth v pos_l 0 < m.
Proof.
  intros n m j fadj_col_l rr_l pos_l v Hinv Hv Hj Hhit.
  unfold transpose_scatter_inv in Hinv.
  destruct Hinv as [_ [_ [Hpos Hbound]]].
  rewrite Hpos by exact Hv.
  pose proof (Hbound v Hv) as [Hrr Htotal].
  pose proof (zrange_count_value_nonneg 0 j v fadj_col_l) as Hcnt_nonneg.
  assert (Hcnt_lt :
    zrange_count_value 0 j v fadj_col_l <
    zrange_count_value 0 m v fadj_col_l).
  {
    pose proof (zrange_count_value_extend_hit 0 j v fadj_col_l ltac:(lia) Hhit)
      as Hextend.
    pose proof (zrange_count_value_mono 0 (j + 1) m v fadj_col_l ltac:(lia))
      as Hmono.
    lia.
  }
  lia.
Qed.

Lemma transpose_scatter_inv_step :
  forall n m j fadj_col_l rr_l pos_l v,
    transpose_scatter_inv n m j fadj_col_l rr_l pos_l ->
    0 <= v < n ->
    0 <= j < m ->
    Znth j fadj_col_l 0 = v ->
    transpose_scatter_inv n m (j + 1) fadj_col_l rr_l
      (replace_Znth v (Znth v pos_l 0 + 1) pos_l).
Proof.
  intros n m j fadj_col_l rr_l pos_l v Hinv Hv Hj Hhit.
  unfold transpose_scatter_inv in *.
  destruct Hinv as [Hjrange [Hlen [Hpos Hbound]]].
  split; [lia|].
  split.
  { rewrite Zlength_replace_Znth; lia. }
  split.
  - intros k Hk.
    destruct (Z.eq_dec k v) as [Hkv|Hkv].
    + subst k.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Hpos by exact Hv.
      rewrite zrange_count_value_extend_hit by lia.
      lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite Hpos by exact Hk.
      unfold zrange_count_value.
      rewrite sum_Z_range_extend_right by lia.
      assert (Znth j fadj_col_l 0 <> k) by congruence.
      destruct (Z.eq_dec (Znth j fadj_col_l 0) k); congruence || lia.
  - exact Hbound.
Qed.

Lemma transpose_scatter_contents_start :
  forall g n fadj_row_l fadj_col_l rr_l rc_l,
    transpose_scatter_contents g n 0 fadj_row_l fadj_col_l rr_l rc_l.
Proof.
  unfold transpose_scatter_contents.
  intros g n fadj_row_l fadj_col_l rr_l rc_l.
  split.
  - intros dst p Hdst Hp.
    unfold zrange_count_value in Hp.
    rewrite sum_Z_range_empty in Hp by lia.
    unfold csr_lo in Hp.
    lia.
  - intros dst src Hdst Hsrc.
    split; intros H.
    + destruct H as [p [Hp _]].
      unfold zrange_count_value in Hp.
      rewrite sum_Z_range_empty in Hp by lia.
      unfold csr_lo in Hp.
      lia.
    + destruct H as [t [Ht _]]. lia.
Qed.

Lemma transpose_scatter_contents_step :
  forall g n m j u v fadj_row_l fadj_col_l rr_l pos_l rc_l,
    transpose_scatter_inv n m j fadj_col_l rr_l pos_l ->
    transpose_scatter_rows n m fadj_col_l rr_l ->
    transpose_scatter_contents g n j fadj_row_l fadj_col_l rr_l rc_l ->
    m <= Zlength rc_l ->
    (forall src1 src2 t,
       0 <= src1 < n ->
       0 <= src2 < n ->
       csr_lo src1 fadj_row_l <= t < csr_hi src1 fadj_row_l ->
       csr_lo src2 fadj_row_l <= t < csr_hi src2 fadj_row_l ->
       src1 = src2) ->
    0 <= u < n ->
    0 <= v < n ->
    0 <= j < m ->
    csr_lo u fadj_row_l <= j < csr_hi u fadj_row_l ->
    Znth j fadj_col_l 0 = v ->
    transpose_scatter_contents g n (j + 1) fadj_row_l fadj_col_l rr_l
      (replace_Znth (Znth v pos_l 0) u rc_l).
Proof.
  intros g n m j u v fadj_row_l fadj_col_l rr_l pos_l rc_l
    Hinv Hrows Hcontent Hrc_len Howner Hu Hv Hj Hurow Hhit.
  unfold transpose_scatter_contents in *.
  destruct Hcontent as [Hrange Hcontent].
  unfold transpose_scatter_inv in Hinv.
  destruct Hinv as [Hjrange [Hpos_len [Hpos Hbound]]].
  unfold transpose_scatter_rows in Hrows.
  destruct Hrows as [_ [_ [Hrow_hi Hrow_disjoint]]].
  pose proof (Hpos v Hv) as Hposv.
  pose proof (Hbound v Hv) as [Hrrv Htotalv].
  assert (Hnew_index :
    Znth v pos_l 0 =
      Znth v rr_l 0 + zrange_count_value 0 j v fadj_col_l) by exact Hposv.
  pose proof (transpose_scatter_inv_current_bound
    n m j fadj_col_l rr_l pos_l v
    (conj Hjrange (conj Hpos_len (conj Hpos Hbound)))
    Hv Hj Hhit) as Hnew_bound_m.
  assert (Hnew_bounds : 0 <= Znth v pos_l 0 < Zlength rc_l).
  { lia. }
  split.
  - intros dst p Hdst Hp.
    destruct (Z.eq_dec dst v) as [Hdstv|Hdstv].
    + subst dst.
      rewrite zrange_count_value_extend_hit in Hp by lia.
      destruct (Z.eq_dec p (Znth v pos_l 0)) as [Hpeq|Hpeq].
      * subst p. rewrite Znth_replace_Znth_Same by lia. lia.
      * assert (Hp_bounds : 0 <= p < Zlength rc_l).
        { unfold csr_lo in Hp. rewrite Hnew_index in Hnew_bounds. lia. }
        rewrite Znth_replace_Znth_Diff by lia.
        apply (Hrange v p Hv). lia.
    + unfold zrange_count_value in Hp.
      rewrite sum_Z_range_extend_right in Hp by lia.
      destruct (Z.eq_dec (Znth j fadj_col_l 0) dst) as [Heq|Heq]; [congruence|].
      change (Sum.sum (fun i : Z => 0 <= i < j)
        (fun i : Z => if Z.eq_dec (Znth i fadj_col_l 0) dst then 1 else 0))
        with (zrange_count_value 0 j dst fadj_col_l) in Hp.
      assert (Hold :
        csr_lo dst rr_l <= p <
          Znth dst rr_l 0 + zrange_count_value 0 j dst fadj_col_l) by lia.
      assert (Hpos_v_row : csr_lo v rr_l <= Znth v pos_l 0 < csr_hi v rr_l).
      { pose proof (zrange_count_value_extend_hit 0 j v fadj_col_l ltac:(lia) Hhit)
          as Hextend_v.
        pose proof (zrange_count_value_mono 0 (j + 1) m v fadj_col_l ltac:(lia))
          as Hmono_v.
        rewrite Hnew_index.
        unfold csr_lo.
        split; [pose proof (zrange_count_value_nonneg 0 j v fadj_col_l); lia|].
        rewrite Hrow_hi by exact Hv. lia. }
      assert (Hneq_pos : p <> Znth v pos_l 0).
      { intro Hpeq.
        rewrite Hpeq in Hold.
        pose proof (Hrow_hi dst Hdst) as Hhi_dst.
        pose proof (zrange_count_value_mono 0 j m dst fadj_col_l ltac:(lia))
          as Hcnt_mono_dst.
        assert (Hpos_v_row_final :
          Znth v rr_l 0 <= Znth v pos_l 0 <
            Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l).
        { unfold csr_lo in Hpos_v_row.
          rewrite <- Hrow_hi by exact Hv. exact Hpos_v_row. }
        destruct (Z_lt_ge_dec dst v) as [Hlt|Hge].
        - pose proof (Hrow_disjoint dst v Hdst Hv Hlt) as Hdis.
          unfold csr_lo in Hdis, Hold. rewrite Hhi_dst in Hdis. lia.
        - assert (Hvlt : v < dst) by lia.
          pose proof (Hrow_disjoint v dst Hv Hdst Hvlt) as Hdis.
          unfold csr_lo in Hdis, Hold. rewrite Hrow_hi in Hdis by exact Hv. lia. }
      assert (Hp_bounds : 0 <= p < Zlength rc_l).
      { pose proof (Hbound dst Hdst) as [Hrr_dst Htotal_dst].
        pose proof (zrange_count_value_mono 0 j m dst fadj_col_l ltac:(lia))
          as Hcnt_mono_dst.
        unfold csr_lo in Hold. lia. }
      rewrite Znth_replace_Znth_Diff by lia.
      apply (Hrange dst p Hdst). exact Hold.
  - intros dst src Hdst Hsrc.
    split.
    { intros Hslot.
    destruct Hslot as [p [Hp Hrc]].
    destruct (Z.eq_dec dst v) as [Hdstv|Hdstv].
    + subst dst.
      rewrite zrange_count_value_extend_hit in Hp by lia.
      destruct (Z.eq_dec p (Znth v pos_l 0)) as [Hpeq|Hpeq].
      * exists j.
        rewrite Hpeq in Hrc.
        rewrite Znth_replace_Znth_Same in Hrc by lia.
        subst src.
        split; [lia|].
        split; [lia|exact Hhit].
      * assert (Hold :
          csr_lo v rr_l <= p <
            Znth v rr_l 0 + zrange_count_value 0 j v fadj_col_l) by lia.
        assert (Hp_bounds : 0 <= p < Zlength rc_l).
        { unfold csr_lo in Hold.
          rewrite Hnew_index in Hnew_bounds. lia. }
        rewrite Znth_replace_Znth_Diff in Hrc by lia.
        destruct (proj1 (Hcontent v src Hv Hsrc)) as [t [Ht [Hrow Hcol]]].
        { exists p. exact (conj Hold Hrc). }
        exists t. split; [lia|]. exact (conj Hrow Hcol).
    + unfold zrange_count_value in Hp.
      rewrite sum_Z_range_extend_right in Hp by lia.
      destruct (Z.eq_dec (Znth j fadj_col_l 0) dst) as [Heq|Heq]; [congruence|].
      assert (Hold :
        csr_lo dst rr_l <= p <
          Znth dst rr_l 0 +
            Sum.sum (fun i : Z => 0 <= i < j)
              (fun i : Z => if Z.eq_dec (Znth i fadj_col_l 0) dst then 1 else 0))
        by lia.
      change (Sum.sum (fun i : Z => 0 <= i < j)
        (fun i : Z => if Z.eq_dec (Znth i fadj_col_l 0) dst then 1 else 0))
        with (zrange_count_value 0 j dst fadj_col_l) in Hold.
      assert (Hp_bounds : 0 <= p < Zlength rc_l).
      { pose proof (Hbound dst Hdst) as [Hrr_dst Htotal_dst].
        pose proof (zrange_count_value_mono 0 j m dst fadj_col_l ltac:(lia))
          as Hcnt_mono_dst.
        unfold csr_lo in Hold. lia. }
      assert (Hpos_v_row : csr_lo v rr_l <= Znth v pos_l 0 < csr_hi v rr_l).
      { pose proof (zrange_count_value_extend_hit 0 j v fadj_col_l ltac:(lia) Hhit)
          as Hextend_v.
        pose proof (zrange_count_value_mono 0 (j + 1) m v fadj_col_l ltac:(lia))
          as Hmono_v.
        pose proof (zrange_count_value_nonneg 0 j v fadj_col_l) as Hcnt_nonneg_v.
        rewrite Hnew_index.
        unfold csr_lo.
        split; [lia|].
        rewrite Hrow_hi by exact Hv.
        lia. }
      assert (Hneq_pos : p <> Znth v pos_l 0).
      { intro Hpeq.
        rewrite Hpeq in Hold.
        pose proof (Hrow_hi dst Hdst) as Hhi_dst.
        pose proof (zrange_count_value_mono 0 j m dst fadj_col_l ltac:(lia))
          as Hcnt_mono_dst.
        assert (Hpos_v_row_unfold :
          Znth v rr_l 0 <= Znth v pos_l 0 < csr_hi v rr_l).
        { unfold csr_lo in Hpos_v_row. exact Hpos_v_row. }
        assert (Hpos_v_row_final :
          Znth v rr_l 0 <= Znth v pos_l 0 <
            Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l).
        { rewrite <- Hrow_hi by exact Hv. exact Hpos_v_row_unfold. }
        destruct (Z_lt_ge_dec dst v) as [Hlt|Hge].
        - pose proof (Hrow_disjoint dst v Hdst Hv Hlt) as Hdis.
          unfold csr_lo in Hdis, Hold.
          rewrite Hhi_dst in Hdis.
          lia.
        - assert (Hvlt : v < dst) by lia.
          pose proof (Hrow_disjoint v dst Hv Hdst Hvlt) as Hdis.
          unfold csr_lo in Hdis, Hold.
          rewrite Hrow_hi in Hdis by exact Hv.
          lia. }
      rewrite Znth_replace_Znth_Diff in Hrc by lia.
      destruct (proj1 (Hcontent dst src Hdst Hsrc)) as [t [Ht [Hrow Hcol]]].
      { exists p. exact (conj Hold Hrc). }
      exists t. split; [lia|]. exact (conj Hrow Hcol). }
    { intros Hedge.
    destruct Hedge as [t [Ht [Hrow Hcol]]].
    destruct (Z.eq_dec t j) as [Ht_eq|Ht_ne].
    + subst t.
      exists (Znth v pos_l 0).
      rewrite Znth_replace_Znth_Same by lia.
      assert (Hdstv : dst = v) by congruence.
      subst dst.
      assert (Hsrcu : src = u).
      { eapply Howner; eauto; lia. }
      subst src.
      rewrite zrange_count_value_extend_hit by lia.
      split.
      { pose proof (zrange_count_value_nonneg 0 j v fadj_col_l) as Hcnt_nonneg_v.
        rewrite Hhit.
        rewrite Hnew_index. unfold csr_lo. lia. }
      reflexivity.
    + assert (Ht_old : 0 <= t < j) by lia.
      destruct (proj2 (Hcontent dst src Hdst Hsrc)) as [p [Hp Hrc]].
      { exists t. exact (conj Ht_old (conj Hrow Hcol)). }
      exists p.
      destruct (Z.eq_dec dst v) as [Hdstv|Hdstv].
      * subst dst.
        assert (p <> Znth v pos_l 0).
        { intro Hpeq.
          unfold csr_lo in Hp.
          rewrite Hpeq in Hp. rewrite Hnew_index in Hp.
          rewrite Hdstv in Hp. lia. }
        assert (Hp_bounds : 0 <= p < Zlength rc_l).
        { pose proof (zrange_count_value_mono 0 j m v fadj_col_l ltac:(lia))
            as Hcnt_mono_v.
          unfold csr_lo in Hp. rewrite Hdstv in Hp. lia. }
        rewrite zrange_count_value_extend_hit by lia.
        rewrite Znth_replace_Znth_Diff by lia.
        split; [lia|exact Hrc].
      * unfold zrange_count_value.
        rewrite sum_Z_range_extend_right by lia.
        destruct (Z.eq_dec (Znth j fadj_col_l 0) dst) as [Heq|Heq]; [congruence|].
        assert (p <> Znth v pos_l 0).
        { intro Hpeq.
          rewrite Hpeq in Hp.
          pose proof (Hrow_hi dst Hdst) as Hhi_dst.
          pose proof (zrange_count_value_mono 0 j m dst fadj_col_l ltac:(lia))
            as Hcnt_mono_dst.
          pose proof (zrange_count_value_extend_hit 0 j v fadj_col_l ltac:(lia) Hhit)
            as Hextend_v.
          pose proof (zrange_count_value_mono 0 (j + 1) m v fadj_col_l ltac:(lia))
            as Hmono_v.
          assert (Hpos_v_row_final :
            Znth v rr_l 0 <= Znth v pos_l 0 <
              Znth v rr_l 0 + zrange_count_value 0 m v fadj_col_l).
          { rewrite Hnew_index.
            pose proof (zrange_count_value_nonneg 0 j v fadj_col_l) as Hcnt_nonneg_v.
            lia. }
          destruct (Z_lt_ge_dec dst v) as [Hlt|Hge].
          - pose proof (Hrow_disjoint dst v Hdst Hv Hlt) as Hdis.
            unfold csr_lo in Hdis, Hp.
            rewrite Hhi_dst in Hdis.
            lia.
          - assert (Hvlt : v < dst) by lia.
            pose proof (Hrow_disjoint v dst Hv Hdst Hvlt) as Hdis.
            unfold csr_lo in Hdis, Hp.
            rewrite Hrow_hi in Hdis by exact Hv.
            lia. }
        assert (Hp_bounds : 0 <= p < Zlength rc_l).
        { pose proof (Hbound dst Hdst) as [Hrr_dst Htotal_dst].
          pose proof (zrange_count_value_mono 0 j m dst fadj_col_l ltac:(lia))
            as Hcnt_mono_dst.
          unfold csr_lo in Hp. lia. }
        rewrite Znth_replace_Znth_Diff by lia.
        change (Sum.sum (fun x : Z => 0 <= x < j)
          (fun i : Z => if Z.eq_dec (Znth i fadj_col_l 0) dst then 1 else 0))
          with (zrange_count_value 0 j dst fadj_col_l).
        split; [lia|exact Hrc]. }
Qed.

Lemma transpose_scatter_rows_from_prefix :
  forall n m fadj_col_l rr_l pos_l cnt_l,
    1 <= n ->
    0 <= m ->
    Zlength rr_l = n + 1 ->
    Znth n rr_l 0 = m ->
    transpose_prefix_inv n m n m rr_l cnt_l ->
    transpose_count_values n m fadj_col_l cnt_l ->
    transpose_prefix_offsets n n rr_l pos_l cnt_l ->
    transpose_scatter_rows n m fadj_col_l rr_l.
Proof.
  intros n m fadj_col_l rr_l pos_l cnt_l Hn Hm Hrrlen_full Hrr_last Hpinv Hcnt Hpoff.
  unfold transpose_prefix_inv in Hpinv.
  unfold transpose_prefix_offsets in Hpoff.
  unfold transpose_count_values in Hcnt.
  unfold transpose_scatter_rows.
  destruct Hpinv as [Htotal [Hsum [Hnonneg Htail]]].
  destruct Hpoff as [Hrrlen [Hposlen [Hdone Hnone]]].
  split; [lia|].
  split.
  { unfold m_of, csr_hi.
    replace (Zlength rr_l - 1) with n by lia.
    exact Hrr_last. }
  split.
  - intros v Hv.
    unfold csr_hi.
    destruct (Z.eq_dec (v + 1) n) as [Hv_last|Hv_not_last].
    + replace v with (n - 1) by lia.
      pose proof (Hdone (n - 1) ltac:(lia)) as [Hrr_v _].
      rewrite Hrr_v.
      replace (n - 1 + 1) with n by lia.
      rewrite Hrr_last.
      rewrite <- Hcnt by lia.
      replace (zrange_sum_Znth 0 (n - 1) cnt_l + Znth (n - 1) cnt_l 0)
        with (zrange_sum_Znth 0 n cnt_l).
      2:{ rewrite (zrange_sum_Znth_split 0 (n - 1) n cnt_l) by lia.
          replace n with ((n - 1) + 1) by lia.
          replace (n - 1 + 1 - 1) with (n - 1) by lia.
          rewrite zrange_sum_Znth_single. lia. }
      lia.
    + pose proof (Hdone v ltac:(lia)) as [Hrr_v _].
      pose proof (Hdone (v + 1) ltac:(lia)) as [Hrr_next _].
      rewrite Hrr_v, Hrr_next.
      rewrite <- Hcnt by lia.
      rewrite (zrange_sum_Znth_split 0 v (v + 1) cnt_l) by lia.
      rewrite zrange_sum_Znth_single.
      lia.
  - intros a b Ha Hb Hab.
    unfold csr_lo, csr_hi.
    destruct (Z.eq_dec (a + 1) n) as [Ha_last|Ha_last].
    { lia. }
    pose proof (Hdone (a + 1) ltac:(lia)) as [Hrr_a_hi _].
    pose proof (Hdone b ltac:(lia)) as [Hrr_b _].
    rewrite Hrr_a_hi, Hrr_b.
    pose proof (zrange_sum_Znth_nonneg (a + 1) b cnt_l
      ltac:(intros k Hk; apply Hnonneg; lia)) as Hnonneg_mid.
    rewrite (zrange_sum_Znth_split 0 (a + 1) b cnt_l) by lia.
    lia.
Qed.

Lemma transpose_count_values_zero :
  forall n cnt_l fadj_col_l,
    (forall v, 0 <= v < n -> Znth v cnt_l 0 = 0) ->
    transpose_count_values n 0 fadj_col_l cnt_l.
Proof.
  intros n cnt_l fadj_col_l Hzero v Hv.
  rewrite Hzero by exact Hv.
  unfold zrange_count_value.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.

Lemma transpose_count_values_step :
  forall n j v fadj_col_l cnt_l,
    transpose_count_values n j fadj_col_l cnt_l ->
    0 <= v < n ->
    0 <= v < Zlength cnt_l ->
    n <= Zlength cnt_l ->
    0 <= j ->
    Znth j fadj_col_l 0 = v ->
    transpose_count_values n (j + 1) fadj_col_l
      (replace_Znth v (Znth v cnt_l 0 + 1) cnt_l).
Proof.
  intros n j v fadj_col_l cnt_l Hvals Hv Hlen Hnlen Hj Hhit k Hk.
  destruct (Z.eq_dec k v) as [Hkv|Hkv].
  - subst k.
    rewrite Znth_replace_Znth_Same by exact Hlen.
    rewrite Hvals by exact Hv.
    rewrite zrange_count_value_extend_hit by lia.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite Hvals by exact Hk.
    unfold zrange_count_value.
    rewrite sum_Z_range_extend_right by lia.
    assert (Znth j fadj_col_l 0 <> k) by congruence.
    destruct (Z.eq_dec (Znth j fadj_col_l 0) k); congruence || lia.
Qed.

Lemma transpose_prefix_offsets_start :
  forall n rr_l pos_l cnt_l,
    n <= Zlength rr_l ->
    n <= Zlength pos_l ->
    (forall k, 0 <= k < n -> Znth k rr_l 0 = Znth k cnt_l 0) ->
    transpose_prefix_offsets n 0 rr_l pos_l cnt_l.
Proof.
  intros n rr_l pos_l cnt_l Hrrlen Hposlen Hrr.
  unfold transpose_prefix_offsets.
  split; [exact Hrrlen|].
  split; [exact Hposlen|].
  split.
  - intros k0 Hk0. lia.
  - intros k0 Hk0. apply Hrr. lia.
Qed.

Lemma transpose_prefix_offsets_step :
  forall n v sum_v deg rr_l pos_l cnt_l,
    transpose_prefix_offsets n v rr_l pos_l cnt_l ->
    0 <= v < n ->
    sum_v = zrange_sum_Znth 0 v cnt_l ->
    deg = Znth v cnt_l 0 ->
    transpose_prefix_offsets n (v + 1)
      (replace_Znth v sum_v rr_l)
      (replace_Znth v sum_v pos_l)
      cnt_l.
Proof.
  intros n v sum_v deg rr_l pos_l cnt_l Hoff Hv Hsum Hdeg.
  unfold transpose_prefix_offsets in *.
  destruct Hoff as [Hrrlen [Hposlen [Hdone Htail]]].
  split.
  { rewrite Zlength_replace_Znth; lia. }
  split.
  { rewrite Zlength_replace_Znth; lia. }
  split.
  - intros k Hk.
    destruct (Z.eq_dec k v) as [Hkv|Hkv].
    + subst k.
      rewrite !Znth_replace_Znth_Same by lia.
      split; exact Hsum.
    + rewrite !Znth_replace_Znth_Diff by lia.
      apply Hdone. lia.
  - intros k Hk.
    rewrite Znth_replace_Znth_Diff by lia.
    apply Htail. lia.
Qed.

Lemma transpose_scatter_inv_from_prefix :
  forall n m fadj_col_l rr_l pos_l cnt_l,
    0 <= m ->
    transpose_prefix_inv n m n m rr_l cnt_l ->
    transpose_count_values n m fadj_col_l cnt_l ->
    transpose_prefix_offsets n n rr_l pos_l cnt_l ->
    transpose_scatter_inv n m 0 fadj_col_l rr_l pos_l.
Proof.
  intros n m fadj_col_l rr_l pos_l cnt_l Hm Hpref Hvals Hoff.
  unfold transpose_prefix_inv in Hpref.
  destruct Hpref as [Htotal [_ [Hnonneg _]]].
  unfold transpose_prefix_offsets in Hoff.
  destruct Hoff as [_ [Hposlen [Hdone _]]].
  apply transpose_scatter_inv_start; try assumption.
  - intros v Hv.
    specialize (Hdone v ltac:(lia)) as [Hrr Hpos].
    rewrite Hpos, Hrr.
    reflexivity.
  - intros v Hv.
    specialize (Hdone v ltac:(lia)) as [Hrr _].
    rewrite Hrr.
    pose proof (Hvals v Hv) as Hcnt.
    split.
    + pose proof (zrange_sum_Znth_nonneg 0 v cnt_l ltac:(intros k Hk; apply Hnonneg; lia)).
      exact H.
    + assert (Hsplit :
        zrange_sum_Znth 0 n cnt_l =
        zrange_sum_Znth 0 v cnt_l + zrange_sum_Znth v n cnt_l).
      { apply zrange_sum_Znth_split. lia. }
      rewrite Htotal in Hsplit.
      assert (Hvpart : zrange_sum_Znth v n cnt_l =
                       Znth v cnt_l 0 + zrange_sum_Znth (v + 1) n cnt_l).
      {
        rewrite (zrange_sum_Znth_split v (v + 1) n cnt_l) by lia.
        rewrite zrange_sum_Znth_single. lia.
      }
      pose proof (zrange_sum_Znth_nonneg (v + 1) n cnt_l
                    ltac:(intros k Hk; apply Hnonneg; lia)).
      lia.
Qed.

Lemma transpose_count_ready_prefix_start :
  forall n m cnt_l,
    1 <= n ->
    transpose_count_ready n m cnt_l ->
    transpose_prefix_inv n m 0 0 cnt_l cnt_l.
Proof.
  intros n m cnt_l Hn [Hsum Hnonneg].
  unfold transpose_prefix_inv.
  split.
  { exact Hsum. }
  split.
  { unfold zrange_sum_Znth. rewrite sum_Z_range_empty by lia. reflexivity. }
  split.
  { exact Hnonneg. }
  { intros k Hk. reflexivity. }
Qed.

Lemma transpose_prefix_inv_zero_sum :
  forall n m sum_v rr_l cnt_l,
    transpose_prefix_inv n m 0 sum_v rr_l cnt_l ->
    sum_v = 0.
Proof.
  intros n m sum_v rr_l cnt_l Hinv.
  unfold transpose_prefix_inv in Hinv.
  destruct Hinv as [_ [Hsum _]].
  rewrite Hsum.
  unfold zrange_sum_Znth.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.

Lemma transpose_prefix_inv_sum_bounds :
  forall n m v sum_v rr_l cnt_l,
    0 <= v <= n ->
    transpose_prefix_inv n m v sum_v rr_l cnt_l ->
    0 <= sum_v <= m.
Proof.
  intros n m v sum_v rr_l cnt_l Hv Hinv.
  unfold transpose_prefix_inv in Hinv.
  destruct Hinv as [Htotal [Hsum [Hnonneg _]]].
  subst sum_v.
  assert (Hsplit : zrange_sum_Znth 0 n cnt_l =
                   zrange_sum_Znth 0 v cnt_l + zrange_sum_Znth v n cnt_l).
  { apply zrange_sum_Znth_split. lia. }
  rewrite Htotal in Hsplit.
  pose proof (zrange_sum_Znth_nonneg 0 v cnt_l ltac:(intros k Hk; apply Hnonneg; lia)).
  pose proof (zrange_sum_Znth_nonneg v n cnt_l ltac:(intros k Hk; apply Hnonneg; lia)).
  lia.
Qed.

Lemma transpose_prefix_inv_next_bound :
  forall n m v sum_v rr_l cnt_l,
    0 <= v < n ->
    transpose_prefix_inv n m v sum_v rr_l cnt_l ->
    sum_v + Znth v rr_l 0 <= m.
Proof.
  intros n m v sum_v rr_l cnt_l Hv Hinv.
  unfold transpose_prefix_inv in Hinv.
  destruct Hinv as [Htotal [Hsum [Hnonneg Htail]]].
  subst sum_v.
  rewrite (Htail v) by lia.
  assert (Hsplit1 : zrange_sum_Znth 0 (v + 1) cnt_l =
                    zrange_sum_Znth 0 v cnt_l + zrange_sum_Znth v (v + 1) cnt_l).
  { apply zrange_sum_Znth_split. lia. }
  rewrite zrange_sum_Znth_single in Hsplit1.
  assert (Hsplit2 : zrange_sum_Znth 0 n cnt_l =
                    zrange_sum_Znth 0 (v + 1) cnt_l + zrange_sum_Znth (v + 1) n cnt_l).
  { apply zrange_sum_Znth_split. lia. }
  rewrite Htotal in Hsplit2.
  pose proof (zrange_sum_Znth_nonneg (v + 1) n cnt_l ltac:(intros k Hk; apply Hnonneg; lia)).
  lia.
Qed.

Lemma zrange_sum_Znth_replace_inside_0 :
  forall hi idx x l,
    0 <= idx < hi ->
    hi <= Zlength l ->
    zrange_sum_Znth 0 hi (replace_Znth idx x l) =
    zrange_sum_Znth 0 hi l - Znth idx l 0 + x.
Proof.
  intros hi idx x l Hidx Hhi_len.
  assert (Hlen : 0 <= idx < Zlength l) by lia.
  rewrite (zrange_sum_Znth_split 0 idx hi l) by lia.
  rewrite (zrange_sum_Znth_split 0 idx hi (replace_Znth idx x l)) by lia.
  rewrite (zrange_sum_Znth_split idx (idx + 1) hi l) by lia.
  rewrite (zrange_sum_Znth_split idx (idx + 1) hi (replace_Znth idx x l)) by lia.
  rewrite !zrange_sum_Znth_single.
  assert (Hleft :
    zrange_sum_Znth 0 idx (replace_Znth idx x l) =
    zrange_sum_Znth 0 idx l).
  {
    unfold zrange_sum_Znth.
    apply sum_Z_range_ext. intros k Hk.
    assert (Hklen : 0 <= k < Zlength l) by lia.
    assert (Hneq : idx <> k) by lia.
    rewrite (Znth_replace_Znth_Diff 0 l idx k x Hlen Hklen Hneq).
    reflexivity.
  }
  assert (Hright :
    zrange_sum_Znth (idx + 1) hi (replace_Znth idx x l) =
    zrange_sum_Znth (idx + 1) hi l).
  {
    unfold zrange_sum_Znth.
    apply sum_Z_range_ext. intros k Hk.
    assert (Hklen : 0 <= k < Zlength l) by lia.
    assert (Hneq : idx <> k) by lia.
    rewrite (Znth_replace_Znth_Diff 0 l idx k x Hlen Hklen Hneq).
    reflexivity.
  }
  rewrite Hleft, Hright.
  rewrite Znth_replace_Znth_Same by exact Hlen.
  lia.
Qed.

Lemma transpose_count_ready_zero :
  forall n cnt_l,
    0 <= n ->
    (forall k, 0 <= k < n -> Znth k cnt_l 0 = 0) ->
    transpose_count_ready n 0 cnt_l.
Proof.
  intros n cnt_l Hn Hzero.
  unfold transpose_count_ready, zrange_sum_Znth.
  split.
  - rewrite (sum_Z_range_ext 0 n (fun i => Znth i cnt_l 0) (fun _ => 0)).
    + rewrite sum_Z_range_const by lia. lia.
    + intros i Hi. apply Hzero. exact Hi.
  - intros k Hk. rewrite Hzero by exact Hk. lia.
Qed.

Lemma transpose_count_ready_step :
  forall n j v cnt_l,
    0 <= v < n ->
    0 <= v < Zlength cnt_l ->
    n <= Zlength cnt_l ->
    transpose_count_ready n j cnt_l ->
    transpose_count_ready n (j + 1)
      (replace_Znth v (Znth v cnt_l 0 + 1) cnt_l).
Proof.
  intros n j v cnt_l Hv Hlen Hn_len [Hsum Hnonneg].
  unfold transpose_count_ready.
  split.
  - rewrite zrange_sum_Znth_replace_inside_0 by lia.
    rewrite Hsum. lia.
  - intros k Hk.
    destruct (Z.eq_dec k v) as [Hkv|Hkv].
    + subst k. rewrite Znth_replace_Znth_Same by exact Hlen.
      pose proof (Hnonneg v Hv). lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hnonneg. exact Hk.
Qed.

Lemma transpose_prefix_inv_step :
  forall n m v sum_v rr_l cnt_l,
    0 <= v < n ->
    0 <= v < Zlength rr_l ->
    n <= Zlength rr_l ->
    transpose_prefix_inv n m v sum_v rr_l cnt_l ->
    transpose_prefix_inv n m (v + 1) (sum_v + Znth v rr_l 0)
      (replace_Znth v sum_v rr_l) cnt_l.
Proof.
  intros n m v sum_v rr_l cnt_l Hv Hlen Hn_len Hinv.
  unfold transpose_prefix_inv in *.
  destruct Hinv as [Htotal [Hsum [Hnonneg Htail]]].
  split.
  { exact Htotal. }
  split.
  { rewrite (zrange_sum_Znth_split 0 v (v + 1) cnt_l) by lia.
    rewrite zrange_sum_Znth_single.
    rewrite Hsum.
    rewrite Htail by lia.
    lia. }
  split.
  { exact Hnonneg. }
  { intros k Hk.
    rewrite Znth_replace_Znth_Diff by lia.
    apply Htail. lia. }
Qed.

(* ================================================================= *)
(* Scoped abstract-state preconditions.                              *)
(*                                                                   *)
(* pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st :        *)
(*   relates the abstract monad state st to the CSR arrays the C     *)
(*   side owns.  vis1/fin/timer are encoded as Z lists over the      *)
(*   abstract St fields (visited1 as 0/1, finish as nat-to-Z, timer  *)
(*   nat).  Pure mathematical relation; NOT an algorithm mirror.     *)
(*                                                                   *)
(* pre_dfs2 is the phase-2 analogue over the forward graph; it also  *)
(* carries the SCC-id array sid_l.                                   *)
(* ================================================================= *)

(* ================================================================= *)
(* count_nonzero: number of nonzero entries in a Z list.             *)
(*   The C side encodes "visited" as 0/1 in vis1/vis2, so            *)
(*   count_nonzero vis_l = number of visited vertices.               *)
(*   The abstract DFS always visit1's a vertex BEFORE set_finish'ing *)
(*   it, hence timer <= count_nonzero vis, i.e. the difference       *)
(*   count_nonzero vis - timer = #visited-but-not-finished, which    *)
(*   dfs1 preserves.  This is the maintainable bound on the timer;   *)
(*   a bare `timer < n` is NOT maintainable through recursion.       *)
(* ================================================================= *)
Fixpoint count_nonzero (l : list Z) : Z :=
  match l with
  | nil => 0%Z
  | z :: rest => (if Z.eqb z 0 then 0%Z else 1%Z) + count_nonzero rest
  end.

Lemma count_nonzero_nonneg : forall (l : list Z), 0 <= count_nonzero l.
Proof. induction l as [| z l IH]; simpl; [lia | destruct (Z.eqb z 0); lia]. Qed.

Lemma count_nonzero_le_Zlength : forall (l : list Z), count_nonzero l <= Zlength l.
Proof.
  induction l as [| z l IH]; simpl.
  - rewrite Zlength_correct; simpl; lia.
  - rewrite Zlength_cons. destruct (Z.eqb z 0); lia.
Qed.

(* Replacing position u with a nonzero value v increases count_nonzero by
   exactly 1 iff the old entry at u was zero; otherwise it is unchanged.
   Requires u to be in range [0, Zlength l). *)
Lemma count_nonzero_replace_Znth :
  forall (u : Z) (v : Z) (l : list Z),
    (0 <= u < Zlength l)%Z ->
    count_nonzero (replace_Znth u v l) =
    count_nonzero l +
    (if Z.eqb (Znth u l 0) 0 then (if Z.eqb v 0 then 0%Z else 1%Z)
                              else (if Z.eqb v 0 then (-1)%Z else 0%Z)).
Proof.
  intros u v l. revert u.
  induction l as [| z l IH]; intros u Hin.
  - exfalso. rewrite Zlength_correct in Hin. simpl in Hin. lia.
  - simpl in Hin. destruct (Z.eqb u 0) eqn:HeqU.
    + (* u = 0: head z gets replaced by v *)
      apply Z.eqb_eq in HeqU. subst u.
      assert (Hz0 : Znth 0 (z :: l) 0 = z) by (rewrite Znth0_cons; reflexivity).
      rewrite Hz0.
      unfold replace_Znth. rewrite Z2Nat.inj_0. simpl.
      simpl count_nonzero at 2.
      destruct (Z.eqb z 0); destruct (Z.eqb v 0); lia.
    + (* u > 0: head z unchanged, recurse on tail with u-1 *)
      assert (Hpos : (0 < u)%Z) by (apply Z.eqb_neq in HeqU; lia).
      rewrite replace_Znth_cons by lia.
      simpl count_nonzero.
      rewrite Zlength_cons in Hin.
      assert (Hu1 : (0 <= u - 1 < Zlength l)%Z) by lia.
      rewrite IH by exact Hu1.
      assert (Heq : Znth u (z :: l) 0 = Znth (u - 1) l 0).
      { rewrite Znth_cons by lia. lia. }
      rewrite Heq.
      destruct (Z.eqb z 0); destruct (Z.eqb (Znth (u - 1) l 0) 0);
      destruct (Z.eqb v 0); lia.
Qed.

(* Specialisation: replacing a zero entry by 1 increases count by 1. *)
Lemma count_nonzero_replace_Znth01 :
  forall (u : Z) (l : list Z),
    (0 <= u < Zlength l)%Z ->
    Znth u l 0 = 0%Z ->
    count_nonzero (replace_Znth u 1 l) = count_nonzero l + 1.
Proof.
  intros u l Hin H. rewrite count_nonzero_replace_Znth by exact Hin.
  rewrite H. simpl. lia.
Qed.

Lemma count_nonzero_lt_Zlength_with_zero :
  forall (l : list Z) (u : Z),
    (0 <= u < Zlength l)%Z ->
    Znth u l 0 = 0%Z ->
    count_nonzero l < Zlength l.
Proof.
  intros l u Hu Hzero.
  pose proof (count_nonzero_le_Zlength (replace_Znth u 1 l)) as Hle.
  rewrite Zlength_replace_Znth in Hle.
  rewrite count_nonzero_replace_Znth01 in Hle by assumption.
  lia.
Qed.

(* Reading back a list after a positional write.  Generic, pure-list;       *)
(* used by the dfs2 Inv establishment/preservation (sid/vis after the       *)
(* preamble's vis[u]=1; sid[u]=sid[root], and the recurse-call poststate).  *)
Lemma Znth_replace_eq :
  forall (l: list Z) n (a d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n a l) d = a.
Proof.
  intros l n a d Hn.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hn.
  remember (Z.to_nat n) as m eqn:Hm.
  assert (HmLen : (m < length l)%nat) by lia.
  clear Hn Hm n.
  revert l HmLen.
  induction m; intros l HmLen.
  - destruct l; simpl in *.
    + lia.
    + reflexivity.
  - destruct l; simpl in *.
    + lia.
    + apply IHm. lia.
Qed.

Lemma Znth_replace_neq :
  forall (l: list Z) i j (a d: Z),
    0 <= i < Zlength l ->
    0 <= j ->
    i <> j ->
    Znth i (replace_Znth j a l) d = Znth i l d.
Proof.
  intros l i j a d Hi Hj Hneq.
  unfold Znth, replace_Znth.
  rewrite Zlength_correct in Hi.
  remember (Z.to_nat i) as ni eqn:HiNat.
  remember (Z.to_nat j) as nj eqn:HjNat.
  assert (HiEq : i = Z.of_nat ni) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HjEq : j = Z.of_nat nj) by (subst; symmetry; apply Z2Nat.id; lia).
  assert (HiLen : (ni < length l)%nat) by lia.
  assert (HneqNat : ni <> nj).
  { intro Heq. apply Hneq. rewrite HiEq, HjEq. now rewrite Heq. }
  clear Hi Hj Hneq HiNat HjNat HiEq HjEq i j.
  revert nj l HiLen HneqNat.
  induction ni; intros nj l HiLen HneqNat.
  - destruct l; simpl in *; try lia.
    destruct nj; [contradiction HneqNat; reflexivity | reflexivity].
  - destruct l; simpl in *; try lia.
    destruct nj; simpl.
    + reflexivity.
    + apply IHni.
      * lia.
      * intro Heq. apply HneqNat. now f_equal.
Qed.

Lemma Znth_replace_old_or_new :
  forall (l : list Z) (i j a d : Z),
    Znth i (replace_Znth j a l) d = a \/
    Znth i (replace_Znth j a l) d = Znth i l d.
Proof.
  intros l i j a d.
  unfold Znth, replace_Znth.
  generalize (Z.to_nat i) (Z.to_nat j).
  induction l as [|x xs IH]; intros ni nj; simpl.
  - right. reflexivity.
  - destruct ni as [|ni], nj as [|nj]; simpl.
    + left. reflexivity.
    + right. reflexivity.
    + right. reflexivity.
    + destruct (IH ni nj) as [H | H]; [left | right]; exact H.
Qed.

(* Pure C-side well-formedness of the CSR/graph input (no monad state).
   These describe the input arrays and the abstract graph; they belong in
   the C function's Require, NOT inside the safeExec precondition. *)
Definition csr_wf1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength radj_row_l = adj_verts g + 1 /\
  Zlength vis1_l = adj_verts g /\
  Zlength fin_l = adj_verts g /\
  m_of radj_row_l = Zlength radj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u radj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u radj_row_l <= m_of radj_row_l)%Z /\
  (* every packed neighbour entry is a valid vertex id in [0, adj_verts g) *)
  (forall j, (0 <= j < m_of radj_row_l)%Z ->
     (0 <= Znth j radj_col_l 0 < adj_verts g)%Z) /\
  (* CSR row array is non-decreasing: each vertex's neighbour range is valid *)
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u radj_row_l <= csr_hi u radj_row_l)%Z) /\
  (m_of radj_row_l <= 2147483646)%Z.

Definition radj_col_particular (g: AdjGraph) (radj_col_l: list Z) : Prop :=
  forall j, (0 <= j < Zlength radj_col_l)%Z ->
     (0 <= Znth j radj_col_l 0 < adj_verts g)%Z.

(* CSR faithfulness: the packed CSR neighbour arrays list exactly the       *)
(* abstract graph's out-/in-neighbours.  This is the refinement link        *)
(* between the C cursor (a CSR position sweep) and the abstract monad's     *)
(* `step_aux g e u v` nondeterministic choice.  It is a pure mathematical   *)
(* property of the (immutable) graph + CSR arrays, so it is loop-invariant  *)
(* in the C code and cheap to carry through dfs1/dfs2.                      *)
Definition csr2_faithful (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) : Prop :=
  forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    step g u v <->
    exists j, (csr_lo u fadj_row_l <= j < csr_hi u fadj_row_l)%Z /\ Znth j fadj_col_l 0 = v.

Definition csr1_faithful (g: AdjGraph) (radj_col_l radj_row_l: list Z) : Prop :=
  forall u v, (0 <= u < adj_verts g)%Z -> (0 <= v < adj_verts g)%Z ->
    step g v u <->
    exists j, (csr_lo u radj_row_l <= j < csr_hi u radj_row_l)%Z /\ Znth j radj_col_l 0 = v.

Lemma csr1_faithful_of_transpose_scatter_contents :
  forall g n m fadj_col_l fadj_row_l rr_l rc_l,
    adj_verts g = n ->
    m = m_of fadj_row_l ->
    csr2_faithful g fadj_col_l fadj_row_l ->
    (forall u, 0 <= u < n -> 0 <= csr_lo u fadj_row_l) ->
    (forall u, 0 <= u < n -> csr_hi u fadj_row_l <= m) ->
    transpose_scatter_rows n m fadj_col_l rr_l ->
    transpose_scatter_contents g n m fadj_row_l fadj_col_l rr_l rc_l ->
    csr1_faithful g rc_l rr_l.
Proof.
  intros g n m fadj_col_l fadj_row_l rr_l rc_l
    Hn Hm Hfwd Hflo Hfhi Hrows Hcontent.
  unfold csr1_faithful.
  intros dst src Hdst Hsrc.
  assert (Hdst_g : 0 <= dst < adj_verts g) by lia.
  assert (Hsrc_g : 0 <= src < adj_verts g) by lia.
  rewrite Hn in Hdst, Hsrc.
  unfold csr2_faithful in Hfwd.
  pose proof (Hfwd src dst Hsrc_g Hdst_g) as Hfwd_dst.
  unfold transpose_scatter_rows in Hrows.
  destruct Hrows as [_ [Hrr_m [Hhi _]]].
  destruct Hcontent as [_ Hcontent].
  pose proof (Hhi dst Hdst) as Hhi_dst.
  specialize (Hcontent dst src Hdst Hsrc).
  split.
  - intro Hstep.
    destruct (proj1 Hfwd_dst Hstep) as [t [[Htlo Hthi] Hcol]].
    destruct (proj2 Hcontent) as [p [Hp Hrc]].
    { exists t. split.
      - pose proof (Hflo src Hsrc) as Hsrc_lo.
        pose proof (Hfhi src Hsrc) as Hsrc_hi. lia.
      - exact (conj (conj Htlo Hthi) Hcol). }
    exists p.
    rewrite <- Hhi_dst in Hp.
    split; [lia|exact Hrc].
  - intros Hex.
    destruct Hex as [p [[Hp_lo Hp_hi] Hrc]].
    rewrite Hhi_dst in Hp_hi.
    destruct (proj1 Hcontent) as [t [Ht [Hrow Hcol]]].
    { exists p. split; [lia|exact Hrc]. }
    apply (proj2 Hfwd_dst).
    exists t. exact (conj Hrow Hcol).
Qed.

(* pre_dfs1: ONLY the C-program-state <-> monad-state correspondence. *)
Definition pre_dfs1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z)
  (st : KSt) : Prop :=
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited1 st u <-> Znth u vis1_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     finish st u = Z.to_nat (Znth u fin_l 0)) /\
  timer st = Z.to_nat timer_v /\
  (forall u, ~ (0 <= u < adj_verts g)%Z -> ~ visited1 st u) /\
  (forall u, ~ (0 <= u < adj_verts g)%Z -> finish st u = 0%nat).

(* The C program stores finished vertices by completion position:
   [fin_l[t] = v] means that the monadic finish time of [v] is [t + 1].
   Only [0, timer_v) is initialized; the remaining malloc'ed suffix is
   deliberately unconstrained.  This is the refinement relation used by the
   current C proof.  [pre_dfs1] is retained as a legacy compatibility layer
   for older helper lemmas, but is no longer used by the C contracts. *)
Definition fin_sequence_rep (g : AdjGraph) (fin_l : list Z)
  (timer_v : Z) (st : KSt) : Prop :=
  (0 <= timer_v <= adj_verts g)%Z /\
  Zlength fin_l = adj_verts g /\
  timer st = Z.to_nat timer_v /\
  (forall t, (0 <= t < timer_v)%Z ->
     (0 <= Znth t fin_l 0 < adj_verts g)%Z /\
     finish st (Znth t fin_l 0) = S (Z.to_nat t)) /\
  (forall v, (0 <= v < adj_verts g)%Z ->
     finish st v <> 0%nat ->
     exists t, (0 <= t < timer_v)%Z /\ Znth t fin_l 0 = v) /\
  (forall v, ~ (0 <= v < adj_verts g)%Z -> finish st v = 0%nat).

Definition pre_dfs1_sequence (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z)
  (st : KSt) : Prop :=
  (forall v, (0 <= v < adj_verts g)%Z ->
     visited1 st v <-> Znth v vis1_l 0 <> 0%Z) /\
  (forall v, ~ (0 <= v < adj_verts g)%Z -> ~ visited1 st v) /\
  fin_sequence_rep g fin_l timer_v st.

(* Compatibility name for older proof-side helpers.  Cursor refinements must
   not strengthen the concrete C-array/monad-state representation with the
   transient algorithm fact that an active root has not yet finished. *)
Definition pre_dfs1_active_sequence (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v root : Z)
  (st : KSt) : Prop :=
  pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l timer_v st.

Definition pre_dfs1_sequence_initial (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (n : Z)
  (st : KSt) : Prop :=
  st = @Kosaraju.init_st Z /\
  pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l 0 st /\
  Zlength vis1_l = n /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 = 0%Z).

Definition dfs1_sequence_state_ready (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z) : Prop :=
  csr_wf1 g radj_col_l radj_row_l vis1_l fin_l /\
  csr1_faithful g radj_col_l radj_row_l /\
  (0 <= timer_v <= adj_verts g)%Z.

Definition dfs1_sequence_extension (g : AdjGraph)
  (vis0 fin0 : list Z) (timer0 : Z)
  (vis1 fin1 : list Z) (timer1 root : Z) : Prop :=
  (0 <= timer0 /\ timer0 <= timer1 /\ timer1 <= adj_verts g)%Z /\
  (forall v, (0 <= v < adj_verts g)%Z ->
     Znth v vis0 0 <> 0%Z -> Znth v vis1 0 <> 0%Z) /\
  Znth root vis1 0 <> 0%Z /\
  (forall t, (0 <= t < timer0)%Z -> Znth t fin1 0 = Znth t fin0 0) /\
  (forall v, (0 <= v < adj_verts g)%Z ->
     Znth v vis0 0 <> 0%Z ->
     forall t, (timer0 <= t < timer1)%Z -> Znth t fin1 0 <> v).

Definition dfs1_finish_prefix_marked
    (fin_l vis_l : list Z) (timer_v n : Z) : Prop :=
  forall t, (0 <= t < timer_v)%Z ->
    (0 <= Znth t fin_l 0 < n)%Z /\
    Znth (Znth t fin_l 0) vis_l 0 <> 0%Z.

Definition dfs1_root_not_in_finish_prefix
    (fin_l : list Z) (timer_v root : Z) : Prop :=
  forall t, (0 <= t < timer_v)%Z -> Znth t fin_l 0 <> root.

Definition dfs1_active_sequence_extension (g : AdjGraph)
  (vis0 fin0 : list Z) (timer0 : Z)
  (vis1 fin1 : list Z) (timer1 root : Z) : Prop :=
  dfs1_sequence_extension g vis0 fin0 timer0 vis1 fin1 timer1 root /\
  dfs1_root_not_in_finish_prefix fin1 timer1 root.

Lemma dfs1_finish_prefix_marked_root_fresh :
  forall fin_l vis_l timer_v n root,
    dfs1_finish_prefix_marked fin_l vis_l timer_v n ->
    (0 <= root < n)%Z ->
    Znth root vis_l 0 = 0%Z ->
    dfs1_root_not_in_finish_prefix fin_l timer_v root.
Proof.
  intros fin_l vis_l timer_v n root Hmarked Hroot Hvis0 t Ht Heq.
  specialize (Hmarked t Ht) as [_ Hvis].
  rewrite Heq in Hvis.
  rewrite Hvis0 in Hvis.
  contradiction.
Qed.

Lemma dfs1_active_sequence_extension_entry :
  forall g vis_l fin_l timer_v root,
    (0 <= timer_v <= adj_verts g)%Z ->
    Zlength vis_l = adj_verts g ->
    (0 <= root < adj_verts g)%Z ->
    Znth root vis_l 0 = 0%Z ->
    dfs1_finish_prefix_marked fin_l vis_l timer_v (adj_verts g) ->
    dfs1_active_sequence_extension g vis_l fin_l timer_v
      (replace_Znth root 1 vis_l) fin_l timer_v root.
Proof.
  intros g vis_l fin_l timer_v root Htimer Hlen Hroot Hroot0 Hmarked.
  unfold dfs1_active_sequence_extension, dfs1_sequence_extension.
  split.
  - split; [lia |].
    split.
    + intros v Hv Hvis.
      destruct (Z.eq_dec v root) as [-> | Hne].
      * congruence.
      * rewrite (Znth_replace_neq vis_l v root 1 0) by lia.
        exact Hvis.
    + split.
      * rewrite (Znth_replace_eq vis_l root 1 0) by lia.
        discriminate.
      * split.
        -- intros t _. reflexivity.
        -- intros v Hv Hvis t Ht. lia.
  - eapply dfs1_finish_prefix_marked_root_fresh; eauto.
Qed.

Lemma dfs1_active_sequence_extension_recurse :
  forall g vis0 fin0 timer0 vis1 fin1 timer1 vis2 fin2 timer2 root child,
    (0 <= timer0)%Z ->
    (0 <= root < adj_verts g)%Z ->
    dfs1_active_sequence_extension g vis0 fin0 timer0 vis1 fin1 timer1 root ->
    dfs1_sequence_extension g vis1 fin1 timer1 vis2 fin2 timer2 child ->
    dfs1_active_sequence_extension g vis0 fin0 timer0 vis2 fin2 timer2 root.
Proof.
  intros g vis0 fin0 timer0 vis1 fin1 timer1 vis2 fin2 timer2 root child
    Htimer0 Hroot Hactive Hchild.
  unfold dfs1_active_sequence_extension in *.
  destruct Hactive as [Hparent Hroot_fresh].
  unfold dfs1_sequence_extension in *.
  destruct Hparent as
    [Htimer01 [Hvis01 [Hroot_vis1 [Hprefix01 Hnew01]]]].
  destruct Hchild as
    [Htimer12 [Hvis12 [Hchild_vis [Hprefix12 Hnew12]]]].
  split.
  - split; [lia |].
    split.
    + intros v Hv Hvis0.
      apply Hvis12; [exact Hv |].
      apply Hvis01; assumption.
    + split.
      * apply Hvis12; assumption.
      * split.
        -- intros t Ht.
           rewrite Hprefix12 by lia.
           apply Hprefix01; lia.
        -- intros v Hv Hvis0 t Ht.
           destruct (Z_lt_ge_dec t timer1) as [Hlt | Hge].
           ++ rewrite Hprefix12 by lia.
              apply Hnew01; try assumption; lia.
           ++ apply Hnew12; try assumption; [apply Hvis01; assumption | lia].
  - intros t Ht.
    destruct (Z_lt_ge_dec t timer1) as [Hlt | Hge].
    + rewrite Hprefix12 by lia.
      apply Hroot_fresh; lia.
    + apply Hnew12; try assumption; lia.
Qed.

Lemma dfs1_sequence_extension_close_active :
  forall g vis0 fin0 timer0 vis1 fin1 timer1 root,
    dfs1_active_sequence_extension g vis0 fin0 timer0 vis1 fin1 timer1 root ->
    Zlength fin1 = adj_verts g ->
    (0 <= timer0)%Z ->
    (0 <= timer1 < adj_verts g)%Z ->
    Znth root vis0 0 = 0%Z ->
    dfs1_sequence_extension g vis0 fin0 timer0 vis1
      (replace_Znth timer1 root fin1) (timer1 + 1) root.
Proof.
  intros g vis0 fin0 timer0 vis1 fin1 timer1 root
    Hactive Hlen Htimer0 Htimer1 Hroot0.
  unfold dfs1_active_sequence_extension in Hactive.
  destruct Hactive as [Hext _].
  unfold dfs1_sequence_extension in *.
  destruct Hext as
    [Htimer [Hvis_old [Hroot_vis [Hprefix Hnew]]]].
  split; [lia |].
  split; [exact Hvis_old |].
  split; [exact Hroot_vis |].
  split.
  - intros t Ht.
    rewrite (Znth_replace_neq fin1 t timer1 root 0) by lia.
    apply Hprefix; lia.
  - intros v Hv Hvis0 t Ht.
    destruct (Z.eq_dec t timer1) as [-> | Hne].
    + rewrite (Znth_replace_eq fin1 timer1 root 0) by lia.
      intro Heq.
      subst v.
      congruence.
    + rewrite (Znth_replace_neq fin1 t timer1 root 0) by lia.
      apply Hnew; try assumption; lia.
Qed.

Lemma dfs1_finish_prefix_marked_extend :
  forall fin_l vis_l timer_v n root,
    dfs1_finish_prefix_marked fin_l vis_l timer_v n ->
    Zlength fin_l = n ->
    (0 <= timer_v < n)%Z ->
    (0 <= root < n)%Z ->
    Znth root vis_l 0 <> 0%Z ->
    dfs1_finish_prefix_marked
      (replace_Znth timer_v root fin_l) vis_l (timer_v + 1) n.
Proof.
  intros fin_l vis_l timer_v n root Hmarked Hlen Htimer Hroot Hroot_vis t Ht.
  destruct (Z.eq_dec t timer_v) as [-> | Hne].
  - rewrite (Znth_replace_eq fin_l timer_v root 0) by lia.
    split; assumption.
  - rewrite (Znth_replace_neq fin_l t timer_v root 0) by lia.
    apply Hmarked; lia.
Qed.

Definition phase1_sequence_refinement (g : AdjGraph)
  (radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l : list Z)
  (timer_v n u : Z) : Prop :=
  dfs1_sequence_state_ready g radj_col_l radj_row_l vis_l fin_l timer_v /\
  (timer_v <= count_nonzero vis_l)%Z /\
  safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis_l fin_l timer_v)
    (dfs_finish_schedule g u (n - u))
    (result_state
      (pre_dfs1_sequence_initial g radj_col_l radj_row_l vis0_l fin0_l n)
      (dfs_finish_schedule g 0 n)).

Definition phase2_sequence_state_rep
    (g : AdjGraph) (fin_l vis1_l vis2_l sid_l : list Z)
    (timer_v n : Z) (st : KSt) : Prop :=
  pre_dfs1_sequence g nil nil vis1_l fin_l timer_v st /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 <> 0%Z) /\
  (forall v, (0 <= v < n)%Z ->
     visited2 st v <-> Znth v vis2_l 0 <> 0%Z) /\
  (forall v, (0 <= v < n)%Z -> visited2 st v ->
     Z.of_nat (scc_id st v) = Znth v sid_l 0).

Definition phase2_sequence_final_post
    (g : AdjGraph) (_ : unit) (st : KSt) : Prop :=
  (forall v, (0 <= v < adj_verts g)%Z -> visited2 st v) /\
  (forall u v,
    (0 <= u < adj_verts g)%Z ->
    (0 <= v < adj_verts g)%Z ->
    (scc_id st u = scc_id st v <->
     @Kosaraju.mutually_reachable AdjGraph Z (Z * Z) KG g u v)).

Definition pre_dfs1_initial (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (n : Z)
  (st : KSt) : Prop :=
  st = @Kosaraju.init_st Z /\
  pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l 0 st /\
  (forall u, (0 <= u < n)%Z ->
     Znth u vis1_l 0 = 0%Z /\ Znth u fin_l 0 = 0%Z).

Definition dfs1_finish_arrays_inv (g : AdjGraph)
  (vis1_l fin_l : list Z) (timer_v : Z) : Prop :=
  (0 <= timer_v)%Z /\
  timer_v = count_nonzero fin_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     Znth u vis1_l 0 = 0%Z ->
     Znth u fin_l 0 = 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     Znth u vis1_l 0 <> 0%Z ->
     (0 <= Znth u fin_l 0 <= timer_v)%Z).

(* DFS1 phase-1 readiness is intentionally separate from [pre_dfs1].
   [pre_dfs1] remains the C-array/monad-state correspondence.  The state
   predicate is preserved by a DFS1 call; the call predicate adds the root
   facts needed to apply [DFS_finish_phase1_plus]. *)
Definition dfs1_phase1_state_ready (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v : Z) : Prop :=
  csr_wf1 g radj_col_l radj_row_l vis1_l fin_l /\
  csr1_faithful g radj_col_l radj_row_l /\
  dfs1_finish_arrays_inv g vis1_l fin_l timer_v.

Definition fin_order_prefix
    (fin_l vis_l : list Z) (timer n : Z) : Prop :=
  0 <= timer <= n /\
  Zlength fin_l = n /\
  Zlength vis_l = n /\
  (forall i, 0 <= i < timer -> 0 <= Znth i fin_l 0 < n) /\
  (forall i, timer <= i < n -> Znth i fin_l 0 = 0) /\
  (forall v, 0 <= v < n ->
    (Znth v vis_l 0 <> 0 <->
      exists i, 0 <= i < timer /\ Znth i fin_l 0 = v)).

Definition dfs1_phase1_ready (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v u : Z) : Prop :=
  dfs1_phase1_state_ready g radj_col_l radj_row_l vis1_l fin_l timer_v /\
  (0 <= u < adj_verts g)%Z /\
  Znth u vis1_l 0 = 0%Z /\
  (forall st,
    pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st ->
    ~ @visited1 Z st u /\
    @vvalid AdjGraph Z (Z * Z)
      (@kos_graph AdjGraph Z (Z * Z) KG) g u) /\
  fin_order_prefix fin_l vis1_l timer_v (adj_verts g).

Definition pre_dfs1_phase1 (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v u : Z)
  (st : KSt) : Prop :=
  pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st /\
  dfs1_phase1_ready g radj_col_l radj_row_l vis1_l fin_l timer_v u.

Lemma pre_dfs1_phase1_exists :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u : Z),
    dfs1_phase1_ready g radj_col_l radj_row_l vis1_l fin_l timer_v u ->
    exists st,
      pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u st.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u Hready.
  set (st0 :=
    MkSt (Z.to_nat timer_v)
      (fun v =>
         match Z_lt_ge_dec v 0 with
         | left _ => 0%nat
         | right Hv0 =>
             match Z_lt_ge_dec v (adj_verts g) with
             | left _ => Z.to_nat (Znth v fin_l 0)
             | right _ => 0%nat
             end
         end)
      (fun v => (0 <= v < adj_verts g)%Z /\ Znth v vis1_l 0 <> 0%Z)
      (fun _ => False)
      (fun _ => 0%nat)
      0%nat).
  exists st0.
  split; [ | exact Hready ].
  unfold pre_dfs1, st0; simpl.
  split.
  - intros v Hv. tauto.
  - split.
    + intros v Hv.
      destruct (Z_lt_ge_dec v 0) as [Hlt | Hge]; [ lia | ].
      destruct (Z_lt_ge_dec v (adj_verts g)) as [Hlt | Hge']; [ reflexivity | lia ].
    + split.
      * reflexivity.
      * split.
        -- intros v Hinvalid [Hv _]. apply Hinvalid. exact Hv.
        -- intros v Hinvalid.
           destruct (Z_lt_ge_dec v 0) as [Hlt | Hge]; [ reflexivity | ].
           destruct (Z_lt_ge_dec v (adj_verts g)) as [Hlt | Hge']; [ exfalso; apply Hinvalid; lia | reflexivity ].
Qed.

Definition dfs1_phase1_result (g : AdjGraph) (u : Z)
  (entry : KSt) (st : KSt) : Prop :=
  @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
  @visited1 Z st u /\
  @visited1 Z entry ⊆ @visited1 Z st /\
  (forall x, @visited1 Z entry x ->
     @finish Z st x = @finish Z entry x).

Definition dfs_finish_phase1_checked (g : AdjGraph)
  (radj_col_l radj_row_l vis1_l fin_l : list Z) (timer_v u : Z)
  : program KSt unit :=
  entry <- get (fun st entry => entry = st);;
  assertS (fun st =>
    st = entry /\
    pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u st);;
  dfs_finish g u;;
  assertS (dfs1_phase1_result g u entry).

Lemma safeExec_dfs_finish_phase1_checked_raw :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u : Z) (X : unit -> KSt -> Prop),
    safeExec
      (pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u)
      (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l timer_v u)
      X ->
    safeExec
      (pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish g u) X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u X Hsafe.
  unfold safeExec, safe in *.
  destruct Hsafe as [sigma [Hpre Hwp]].
  exists sigma. split; [ exact (proj1 Hpre) | ].
  unfold dfs_finish_phase1_checked in Hwp.
  rewrite wp_bind in Hwp.
  pose proof
    (wp_spec (get (fun st entry : KSt => entry = st)) sigma sigma sigma
       (conj eq_refl eq_refl) _ Hwp) as Hwp_assert_entry.
  rewrite wp_bind in Hwp_assert_entry.
  pose proof
    (wp_spec
       (assertS
          (fun st : KSt =>
             st = sigma /\
             pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u st))
       sigma sigma tt (conj eq_refl (conj eq_refl Hpre)) _
       Hwp_assert_entry) as Hwp_dfs.
  unfold weakestpre in *.
  destruct Hwp_dfs as [Hnoerr Hpost].
  split.
  - intro Herr. apply Hnoerr.
    cbv [MonadErr.bind MonadErr.nrm_err] in *; simpl in *; sets_unfold.
    left. exact Herr.
  - intros [] sigma' Hnrm.
    assert (Hresult : dfs1_phase1_result g u sigma sigma').
    { apply NNPP. intro Hnot.
      apply Hnoerr.
      cbv [MonadErr.bind MonadErr.nrm_err assertS] in *; simpl in *; sets_unfold.
      right. exists tt. exists sigma'. split; [ exact Hnrm | exact Hnot ]. }
    apply (Hpost tt sigma').
    cbv [MonadErr.bind MonadErr.nrm_nrm assertS] in *; simpl in *; sets_unfold.
    exists tt. exists sigma'. split; [ exact Hnrm | split; [ reflexivity | exact Hresult ] ].
Qed.

Lemma dfs_finish_phase1_checked_nrm_result :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u : Z) (entry st : KSt),
    MonadErr.nrm
      (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l timer_v u)
      entry tt st ->
    dfs1_phase1_result g u entry st.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u entry st Hnrm.
  unfold dfs_finish_phase1_checked in Hnrm.
  cbv [MonadErr.bind MonadErr.nrm_nrm get assertS] in Hnrm.
  destruct Hnrm as [entry0 [s0 [[Hentry0 Hs0] Hrest]]].
  subst entry0 s0.
  destruct Hrest as [r0 [s1 [[Hs1 _] Hrest]]].
  destruct r0.
  subst s1.
  destruct Hrest as [r1 [s2 [Hdfs [Hs2 Hresult]]]].
  destruct r1.
  subst s2.
  exact Hresult.
Qed.

Lemma dfs_finish_phase1_checked_nrm_raw :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u : Z) (entry st : KSt),
    MonadErr.nrm
      (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l timer_v u)
      entry tt st ->
    MonadErr.nrm (dfs_finish g u) entry tt st.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u entry st Hnrm.
  unfold dfs_finish_phase1_checked in Hnrm.
  cbv [MonadErr.bind MonadErr.nrm_nrm get assertS] in Hnrm.
  destruct Hnrm as [entry0 [s0 [[Hentry0 Hs0] Hrest]]].
  subst entry0 s0.
  destruct Hrest as [r0 [s1 [[Hs1 _] Hrest]]].
  destruct r0.
  subst s1.
  destruct Hrest as [r1 [s2 [Hdfs [Hs2 _]]]].
  destruct r1.
  subst s2.
  exact Hdfs.
Qed.

Definition csr_wf2 (g : AdjGraph)
  (fadj_col_l fadj_row_l vis2_l sid_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength fadj_row_l = adj_verts g + 1 /\
  Zlength vis2_l = adj_verts g /\
  Zlength sid_l = adj_verts g /\
  m_of fadj_row_l = Zlength fadj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u fadj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u fadj_row_l <= m_of fadj_row_l)%Z /\
  (* every packed neighbour entry is a valid vertex id in [0, adj_verts g) *)
  (forall j, (0 <= j < m_of fadj_row_l)%Z ->
     (0 <= Znth j fadj_col_l 0 < adj_verts g)%Z) /\
  (* CSR row array is non-decreasing: each vertex's neighbour range is valid *)
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u fadj_row_l <= csr_hi u fadj_row_l)%Z) /\
  (m_of fadj_row_l <= 2147483646)%Z.

(* The immutable forward-CSR part of [csr_wf2].  It deliberately omits
   vis2/sid: those lists are mutable phase-2 work arrays, while every
   conjunct below is fixed by the CSR construction before [kosaraju]. *)
Definition csr_wf2_core (g : AdjGraph)
  (fadj_col_l fadj_row_l : list Z) : Prop :=
  AdjGraphValid g /\
  Zlength fadj_row_l = adj_verts g + 1 /\
  m_of fadj_row_l = Zlength fadj_col_l /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     0 <= csr_lo u fadj_row_l)%Z /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     csr_hi u fadj_row_l <= m_of fadj_row_l)%Z /\
  (forall j, (0 <= j < m_of fadj_row_l)%Z ->
     (0 <= Znth j fadj_col_l 0 < adj_verts g)%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     (csr_lo u fadj_row_l <= csr_hi u fadj_row_l)%Z) /\
  (m_of fadj_row_l <= 2147483646)%Z.

Lemma csr_wf2_core_m_of_last :
  forall g fadj_col_l fadj_row_l n,
    csr_wf2_core g fadj_col_l fadj_row_l ->
    adj_verts g = n ->
    m_of fadj_row_l = Znth n fadj_row_l 0.
Proof.
  intros g fadj_col_l fadj_row_l n Hcore Hverts.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [Hrow_len _]].
  unfold m_of.
  rewrite Hrow_len, Hverts.
  replace (n + 1 - 1) with n by lia.
  reflexivity.
Qed.

Lemma csr_wf2_core_m_of_bounds :
  forall g fadj_col_l fadj_row_l,
    csr_wf2_core g fadj_col_l fadj_row_l ->
    0 <= m_of fadj_row_l <= 2147483646.
Proof.
  intros g fadj_col_l fadj_row_l Hcore.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [Hm [_ [_ [_ [_ Hbound]]]]]]].
  pose proof (Zlength_nonneg fadj_col_l).
  lia.
Qed.

Lemma csr_row_lo_mono_from_local :
  forall n row_l a b,
    (0 <= a /\ a <= b /\ b < n) ->
    (forall u, 0 <= u < n -> csr_lo u row_l <= csr_hi u row_l) ->
    csr_lo a row_l <= csr_lo b row_l.
Proof.
  intros n row_l a b Hab Horder.
  assert (Hchain :
    forall d, 0 <= d -> a + d <= b -> csr_lo a row_l <= csr_lo (a + d) row_l).
  { intros d Hd.
    remember (Z.to_nat d) as nd eqn:Hnd.
    assert (Hd_eq : d = Z.of_nat nd) by lia.
    subst d.
    clear Hd Hnd.
    induction nd as [|nd IH]; intros Hle.
    - replace (a + Z.of_nat 0) with a by lia. lia.
    - replace (a + Z.of_nat (S nd)) with ((a + Z.of_nat nd) + 1) by lia.
      eapply Z.le_trans.
      + apply IH. lia.
      + pose proof (Horder (a + Z.of_nat nd) ltac:(lia)) as Hstep.
        unfold csr_lo, csr_hi in Hstep |- *.
        exact Hstep. }
  replace b with (a + (b - a)) by lia.
  apply Hchain; lia.
Qed.

Lemma csr_wf2_core_row_owner :
  forall g fadj_col_l fadj_row_l n src1 src2 t,
    csr_wf2_core g fadj_col_l fadj_row_l ->
    adj_verts g = n ->
    0 <= src1 < n ->
    0 <= src2 < n ->
    csr_lo src1 fadj_row_l <= t < csr_hi src1 fadj_row_l ->
    csr_lo src2 fadj_row_l <= t < csr_hi src2 fadj_row_l ->
    src1 = src2.
Proof.
  intros g fadj_col_l fadj_row_l n src1 src2 t Hcore Hn Hsrc1 Hsrc2 Hrow1 Hrow2.
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [_ [Horder _]]]]]]].
  assert (Horder_n :
    forall u, 0 <= u < n -> csr_lo u fadj_row_l <= csr_hi u fadj_row_l).
  { intros x Hx. apply Horder. rewrite Hn. exact Hx. }
  destruct (Z_lt_ge_dec src1 src2) as [Hlt|Hge].
  - pose proof (csr_row_lo_mono_from_local n fadj_row_l (src1 + 1) src2
      ltac:(lia) Horder_n) as Hmono.
    unfold csr_hi in Hrow1.
    unfold csr_lo in Hmono, Hrow2.
    lia.
  - destruct (Z_lt_ge_dec src2 src1) as [Hgt|Hle]; [|lia].
    pose proof (csr_row_lo_mono_from_local n fadj_row_l (src2 + 1) src1
      ltac:(lia) Horder_n) as Hmono.
    unfold csr_hi in Hrow2.
    unfold csr_lo in Hmono, Hrow1.
    lia.
Qed.

Lemma csr_wf2_of_core :
  forall g fadj_col_l fadj_row_l vis2_l sid_l,
    csr_wf2_core g fadj_col_l fadj_row_l ->
    Zlength vis2_l = adj_verts g ->
    Zlength sid_l = adj_verts g ->
    csr_wf2 g fadj_col_l fadj_row_l vis2_l sid_l.
Proof.
  intros g fadj_col_l fadj_row_l vis2_l sid_l Hcore Hvis Hsid.
  unfold csr_wf2_core in Hcore.
  unfold csr_wf2.
  destruct Hcore as
    [Hvalid [Hrow [Hm [Hlo [Hhi [Hcol [Horder Hbound]]]]]]].
  split; [exact Hvalid|].
  split; [exact Hrow|].
  split; [exact Hvis|].
  split; [exact Hsid|].
  split; [exact Hm|].
  split; [exact Hlo|].
  split; [exact Hhi|].
  split; [exact Hcol|].
  split; [exact Horder|exact Hbound].
Qed.

(* pre_dfs2: ONLY the C-program-state <-> monad-state correspondence. *)
Definition pre_dfs2 (g : AdjGraph)
  (fadj_col_l fadj_row_l vis2_l sid_l : list Z) (root_v : Z)
  (st : KSt) : Prop :=
  (forall u, (0 <= u < adj_verts g)%Z ->
     visited2 st u <-> Znth u vis2_l 0 <> 0%Z) /\
  (forall u, (0 <= u < adj_verts g)%Z ->
     scc_id st u = Z.to_nat (Znth u sid_l 0)).

(* The MonadErr model supplies [DFS_scc_absorb]: when a vertex and all of its
   forward neighbours are already marked, and its SCC label agrees with the
   root label, the recursive call has a no-op normal transition.  The C
   refinement uses the following two local bridges to turn that transition
   into the residual [safeExec] return obligation. *)

Lemma dfs_scc_absorb :
  forall (g : AdjGraph) (root u : Z) (st : KSt),
    AdjGraphValid g ->
    (forall v, step g u v -> visited2 st v) ->
    visited2 st u ->
    scc_id st u = scc_id st root ->
    (dfs_scc g root u).(MonadErr.nrm) st tt st.
Proof.
  intros g root u st Hg Hneigh Hvis Hsid.
  unfold dfs_scc.
  exact (@DFS_scc_absorb AdjGraph Z (Z * Z) KG g root u st
           Hneigh Hvis Hsid).
Qed.

Lemma dfs_scc_safe_return :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l vis_l sid_l : list Z)
         (root u root_v : Z) (X : unit -> KSt -> Prop),
    AdjGraphValid g ->
    (forall st,
        pre_dfs2 g fadj_col_l fadj_row_l vis_l sid_l root_v st ->
        (forall v, step g u v -> visited2 st v) /\
        visited2 st u /\
        scc_id st u = scc_id st root) ->
    safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis_l sid_l root_v)
             (dfs_scc g root u) X ->
    safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis_l sid_l root_v)
             (ret tt) X.
Proof.
  intros g fadj_col_l fadj_row_l vis_l sid_l root u root_v X
         Hg Habsorb Hsafe.
  destruct Hsafe as [st [Hpre Hsafe]].
  destruct (Habsorb st Hpre) as [Hneigh [Hvis Hsid]].
  exists st. split; [exact Hpre |].
  unfold safe, weakestpre. split.
  - intro Herr.
    cbv beta iota delta [MonadErr.ret] in Herr.
    sets_unfold in Herr. exfalso. exact Herr.
  - intros r st' Hret.
    cbv beta iota delta [MonadErr.ret] in Hret.
    inversion Hret; subst r st'.
    destruct Hsafe as [_ Hpost].
    apply Hpost.
    exact (dfs_scc_absorb g root u st Hg Hneigh Hvis Hsid).
Qed.

(* ================================================================= *)
(* Loop continuations — cursor-parameterised.                        *)
(*                                                                   *)
(* The abstract DFS_finish u / DFS_scc root u are non-deterministic  *)
(* over (e,v) ∈ E×V.  The C side reifies this choice as a CSR cursor  *)
(* sweep over u's reverse (resp. forward) neighbours: at cursor i    *)
(* the chosen vertex is radj_col_l[i] (resp. fadj_col_l[i]).         *)
(*                                                                   *)
(* dfs_finish_iter g radj_col_l u hi i fuel is a structurally        *)
(* decreasing (fuel) cursor sweep starting at i.  At each step v =   *)
(* radj_col_l[i]; if v is already visited1, SKIP (advance cursor);   *)
(* otherwise RECURSE into dfs_finish g v then advance.  Once the     *)
(* cursor reaches hi (i >= hi) it performs the set_finish u timer    *)
(* tail — mirroring the C post-loop {t0=timer; fin[u]=t0+1; timer++} *)
(* and the DFS_finish_f break branch's `get timer ;; set_finish u t`. *)
(*                                                                   *)
(* dfs_scc_iter is the phase-2 analogue over the forward graph; its  *)
(* exit is `ret tt` because dfs2 has NO post-loop block (the         *)
(* function returns immediately after the cursor sweep).             *)
(*                                                                   *)
(* dfs_finish_from / dfs_scc_from specialise iter with fuel          *)
(* (csr_hi u row_l - i), so the entry (i = csr_lo u), step, and      *)
(* exit (i = csr_hi u) unfoldings discharge by Fixpoint computation. *)
(* This block uses only proved local facts.                          *)
(* ================================================================= *)

(* AdjGraph VListBijective instance: derived from FiniteGraph, matching the
   Section-local `kos_vlist` in Kosaraju.v.  This lets `bijective_listV g`
   resolve in lib.v definitions (needed by dfs_finish_repeat_body's assertS
   timer <= |V|), and keeps definitional equality with DFS_finish_f's body. *)
#[export] Instance AdjGraph_vlistbijective : VListBijective AdjGraph Z (Z * Z) :=
  finite_graph_vlist_bijective AdjGraph Z (Z * Z).

Fixpoint dfs_finish_iter
  (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
          assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; t <- get (fun st t => t = timer st) ;; set_finish u t)
  | S fuel' =>
      if Z.leb hi i then assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
                           assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; t <- get (fun st t => t = timer st) ;; set_finish u t
      else
        (* vis-conditional cursor — matches the C `if (vis1[v]==0)` and the
           abstract repeat_break's `assume ~visited1 st v` guard.  At position
           i, v = Znth i radj_col_l 0: if v is already visited1, SKIP (advance
           cursor); otherwise RECURSE into dfs_finish g v then advance. *)
        if_else (fun st => visited1 st (Znth i radj_col_l 0))
                (dfs_finish_iter g radj_col_l u hi (i + 1) fuel')
                (pre <- get (fun st pre => pre = st);;
                 _ <- dfs_finish g (Znth i radj_col_l 0) ;;
                 assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                                        visited1 st (Znth i radj_col_l 0) /\
                                        visited1 pre ⊆ visited1 st);;
                 dfs_finish_iter g radj_col_l u hi (i + 1) fuel')
  end.

Fixpoint dfs_scc_iter
  (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
  : program KSt unit :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      if Z.leb hi i then ret tt
      else
        (* B1: vis-conditional cursor — matches the C `if (vis2[v]==0)` and the
           abstract repeat_break's `assume ~visited2 st v` guard.  At position
           i, v = Znth i fadj_col_l 0: if v is already visited2, SKIP (advance
           cursor); otherwise RECURSE into dfs_scc root v then advance. *)
        if_else (fun st => visited2 st (Znth i fadj_col_l 0))
                (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel')
                (_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
                 dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel')
  end.

Definition dfs_finish_from
  (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z) : program KSt unit :=
  dfs_finish_iter g radj_col_l u (csr_hi u radj_row_l) i
    (Z.to_nat (csr_hi u radj_row_l - i)).

Definition dfs_scc_from
  (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z) : program KSt unit :=
  dfs_scc_iter g fadj_col_l root u (csr_hi u fadj_row_l) i
    (Z.to_nat (csr_hi u fadj_row_l - i)).

Definition dfs_finish_fromK
  (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z) : unit -> program KSt unit :=
  fun _ => dfs_finish_from g radj_col_l radj_row_l u i.

Definition dfs_scc_fromK
  (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z) : unit -> program KSt unit :=
  fun _ => dfs_scc_from g fadj_col_l fadj_row_l root u i.

(* ================================================================= *)
(* Structural unfolding lemmas for the cursor continuations.          *)
(*                                                                   *)
(* These discharge by Fixpoint computation; they expose the cursor    *)
(* step (recurse into the chosen neighbour, continue at i+1) and the  *)
(* exit (cursor exhausted: re-enter dfs_finish / dfs_scc to run the   *)
(* abstract set_finish / finalisation tail).                          *)
(* ================================================================= *)

Lemma dfs_finish_iter_skip_step :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    (dfs_finish_iter g radj_col_l u hi (i + 1) fuel).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l u hi i fuel st a s' Hilt Hvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] Hsk]]]. subst s2. exact Hsk.
      * destruct H as [b [s2 [[Hs2 Hncond] _]]]. exfalso. apply Hncond. exact Hvis.
    + intros Hsk. left. exists tt. exists st. split; [ split; [ reflexivity | exact Hvis ] | exact Hsk ].
Qed.

Lemma dfs_finish_iter_recurse_step :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    (pre <- get (fun st pre => pre = st);;
     _ <- dfs_finish g (Znth i radj_col_l 0) ;;
     assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                            visited1 st (Znth i radj_col_l 0) /\
                            visited1 pre ⊆ visited1 st);;
      dfs_finish_iter g radj_col_l u hi (i + 1) fuel).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l u hi i fuel st a s' Hilt Hnvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] _]]]. exfalso. apply Hnvis. exact Hcond.
      * destruct H as [b [s2 [[Hs2 Hncond] Hrec]]]. subst s2. exact Hrec.
    + intros Hrec. right. exists tt. exists st. split; [ split; [ reflexivity | exact Hnvis ] | exact Hrec ].
Qed.

Lemma dfs_finish_iter_exit :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat),
    (hi <= i)%Z ->
    dfs_finish_iter g radj_col_l u hi i (S fuel)
    == (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
        assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; t <- get (fun st t => t = timer st) ;; set_finish u t).
Proof.
  intros g radj_col_l u hi i fuel Hge.
  simpl.
  destruct (Z.leb hi i) eqn:E.
  - reflexivity.
  - apply Z.leb_nle in E. lia.
Qed.

Lemma dfs_scc_iter_skip_step :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l root u hi i fuel st a s' Hilt Hvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] Hsk]]]. subst s2. exact Hsk.
      * destruct H as [b [s2 [[Hs2 Hncond] _]]]. exfalso. apply Hncond. exact Hvis.
    + intros Hsk. left. exists tt. exists st. split; [ split; [ reflexivity | exact Hvis ] | exact Hsk ].
Qed.

Lemma dfs_scc_iter_recurse_step :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt) (a : unit) (s' : KSt),
    (i < hi)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.nrm) st a s' <->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel)).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l root u hi i fuel st a s' Hilt Hnvis.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice, test. unfold_monad. sets_unfold.
    split.
    + intros [H | H].
      * destruct H as [b [s2 [[Hs2 Hcond] _]]]. exfalso. apply Hnvis. exact Hcond.
      * destruct H as [b [s2 [[Hs2 Hncond] Hrec]]]. subst s2. exact Hrec.
    + intros Hrec. right. exists tt. exists st. split; [ split; [ reflexivity | exact Hnvis ] | exact Hrec ].
Qed.

Lemma dfs_scc_iter_exit :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat),
    (hi <= i)%Z ->
    dfs_scc_iter g fadj_col_l root u hi i (S fuel) == ret tt.
Proof.
  intros g fadj_col_l root u hi i fuel Hge.
  simpl.
  destruct (Z.leb hi i) eqn:E.
  - reflexivity.
  - apply Z.leb_nle in E. lia.
Qed.

(* Under MonadErr, `program Σ A` is a record {nrm; err}.  dfs_scc (hence
   dfs_scc_iter / dfs_scc_from, which are built only from dfs_scc, if_else,
   choice, test, and bind) never raises an error: every construct used has an
   empty err component (dfs_scc_f's body uses assume, not assert/assertS; the
   custom visit2/set_scc_id have err := ∅).  We never need to prove the
   full no-error fact by induction over BW_fix iterations, because the
   safeExec-based skip/recurse closers only need an err IMPLICATION
   (err-at-i+1 -> err-at-i) under the visited/¬visited cursor hypothesis,
   which follows by one-level unfolding of the if_else/choice/bind err
   structure (using bind_err_iff / bind_nrm_iff from MonadErrBasic). *)
Lemma dfs_scc_iter_skip_err_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel).(MonadErr.err) st ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hvis Herr.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    left. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hvis ].
Qed.

Lemma dfs_scc_iter_recurse_err_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel)).(MonadErr.err) st ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hnvis Herr.
  simpl. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    right. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hnvis ].
Qed.

(* The dfs_finish_from / dfs_scc_from level lemmas, accounting for the
   Z.to_nat fuel accounting.  When i < hi, Z.to_nat (hi - i) = S _ and
   the next cursor's fuel is Z.to_nat (hi - (i+1)) = pred (Z.to_nat (hi-i)). *)

Lemma dfs_finish_from_skip_step :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.nrm) st a s' <->
    (dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l radj_row_l u i st a s' Hilt Hvis.
  unfold dfs_finish_from.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_finish_iter_skip_step; [ lia | exact Hvis ].
Qed.

Lemma dfs_finish_from_recurse_step :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.nrm) st a s' <->
    (pre <- get (fun st pre => pre = st);;
     _ <- dfs_finish g (Znth i radj_col_l 0) ;;
     assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                            visited1 st (Znth i radj_col_l 0) /\
                            visited1 pre ⊆ visited1 st);;
      dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.nrm) st a s'.
Proof.
  intros g radj_col_l radj_row_l u i st a s' Hilt Hnvis.
  unfold dfs_finish_from.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_finish_iter_recurse_step; [ lia | exact Hnvis ].
Qed.

Lemma dfs_finish_from_skip_err_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.err) st ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel.
  simpl. destruct (Z.leb (csr_hi u radj_row_l) i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    left. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hvis ].
Qed.

Lemma dfs_finish_from_recurse_err_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (pre <- get (fun st pre => pre = st);;
     _ <- dfs_finish g (Znth i radj_col_l 0) ;;
     assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                            visited1 st (Znth i radj_col_l 0) /\
                            visited1 pre ⊆ visited1 st);;
      dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.err) st ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hnvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i =
                   (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel.
  simpl. destruct (Z.leb (csr_hi u radj_row_l) i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice. sets_unfold.
    right. rewrite bind_err_iff. right.
    exists tt. exists st. split; [ | exact Herr ].
    unfold test. sets_unfold. split; [ reflexivity | exact Hnvis ].
Qed.

Lemma dfs_finish_from_exit :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z),
    (csr_hi u radj_row_l <= i)%Z ->
    dfs_finish_from g radj_col_l radj_row_l u i
    == assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
       assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; (t <- get (fun st t => t = timer st) ;; set_finish u t).
Proof.
  intros g radj_col_l radj_row_l u i Hge.
  unfold dfs_finish_from.
  destruct (Z.to_nat (csr_hi u radj_row_l - i)) eqn:E.
  - reflexivity.
  - apply dfs_finish_iter_exit. exact Hge.
Qed.

Lemma dfs_scc_from_skip_step :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.nrm) st a s' <->
    (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l fadj_row_l root u i st a s' Hilt Hvis.
  unfold dfs_scc_from.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_skip_step; [ lia | exact Hvis ].
Qed.

Lemma dfs_scc_from_recurse_step :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt) (a : unit) (s' : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.nrm) st a s' <->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1))).(MonadErr.nrm) st a s'.
Proof.
  intros g fadj_col_l fadj_row_l root u i st a s' Hilt Hnvis.
  unfold dfs_scc_from.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_recurse_step; [ lia | exact Hnvis ].
Qed.

Lemma dfs_scc_from_skip_err_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)).(MonadErr.err) st ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_skip_err_imp; [ exact Hilt | exact Hvis | exact Herr ].
Qed.

Lemma dfs_scc_from_recurse_err_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1))).(MonadErr.err) st ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hnvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i =
                   (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel. apply dfs_scc_iter_recurse_err_imp; [ exact Hilt | exact Hnvis | exact Herr ].
Qed.

(* Reverse-direction err-imps (err at i -> err at i+1 / bind), used by the
   repeat_break-to-cursor simulation dfs_scc_from_sim.  The forward err-imps
   above go i+1 -> i (matching dfs2_skip_close / dfs2_recurse_close); the
   simulation peels the cursor step FORWARD (i -> i+1), so it needs the
   reverse direction, which holds under the same visited/~visited hypothesis
   (the failing test branch contributes no err at st). *)
Lemma dfs_scc_iter_skip_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st ->
    (dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc]. subst s0. exact Hsk2.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. exfalso. apply Hnc. exact Hvis.
Qed.

Lemma dfs_scc_iter_recurse_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l : list Z) (root u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_iter g fadj_col_l root u hi i (S fuel)).(MonadErr.err) st ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_iter g fadj_col_l root u hi (i + 1) fuel)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l root u hi i fuel st Hilt Hnvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc].
        exfalso. apply Hnvis. exact Hc.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. subst s0. exact Hsk2.
Qed.

Lemma dfs_scc_from_skip_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i = (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_scc_iter_skip_err_rev_imp g fadj_col_l root u _ i _ st Hilt Hvis Herr).
Qed.

Lemma dfs_scc_from_recurse_err_rev_imp :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z)
         (st : KSt),
    (i < csr_hi u fadj_row_l)%Z ->
    ~ visited2 st (Znth i fadj_col_l 0) ->
    (dfs_scc_from g fadj_col_l fadj_row_l root u i).(MonadErr.err) st ->
    ((_ <- dfs_scc g root (Znth i fadj_col_l 0) ;;
      dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1))).(MonadErr.err) st.
Proof.
  intros g fadj_col_l fadj_row_l root u i st Hilt Hnvis Herr.
  unfold dfs_scc_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u fadj_row_l - i) =
                  S (Z.to_nat (csr_hi u fadj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u fadj_row_l - i = (csr_hi u fadj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_scc_iter_recurse_err_rev_imp g fadj_col_l root u _ i _ st Hilt Hnvis Herr).
Qed.

Lemma dfs_scc_from_exit :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l : list Z) (root u i : Z),
    (csr_hi u fadj_row_l <= i)%Z ->
    dfs_scc_from g fadj_col_l fadj_row_l root u i == ret tt.
Proof.
  intros g fadj_col_l fadj_row_l root u i Hge.
  unfold dfs_scc_from.
  destruct (Z.to_nat (csr_hi u fadj_row_l - i)) eqn:E.
  - reflexivity.
  - apply dfs_scc_iter_exit. exact Hge.
Qed.

(* dfs2_return_close (the Gap-A loop-exit closer) was HERE; it depended on   *)
(* the absorb chain (dfs_scc_safe_return) and is deleted alongside it — see   *)
(* the SEMANTIC GAP note near the former dfs_scc_absorb.                       *)

(* Absorb chain REMOVED.  With the cursor exit set to `ret tt` (dfs2) and
   `get timer ;; set_finish u t` (dfs1), the loop-exit VC no longer needs to
   bridge a re-entered `dfs_scc g root u` / `dfs_finish g u` to a no-op or
   set_finish transition via DFS_scc_absorb.  The exit lemma
   (dfs_scc_from_exit / dfs_finish_from_exit) now equates the cursor
   continuation directly to the exit monad, so the return VC is a plain
   safeExec_proequiv.  No unproved absorb lemmas are needed. *)

(* dfs2 Gap A (loop exit) closer: at i >= hi, dfs_scc_from ... u i == ret tt,
   so `safeExec P (dfs_scc_from ... u i) X` is rewritten to
   `safeExec P (ret tt) X` by program equivalence.  Trivial. *)
Lemma dfs2_return_close :
  forall (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) (root u i: Z)
         (vis2_m sid_m: list Z) (root_v: Z) (X: unit -> KSt -> Prop),
  (csr_hi u fadj_row_l <= i)%Z ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u i) X ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v) (ret tt) X.
Proof.
  intros g fadj_col_l fadj_row_l root u i vis2_m sid_m root_v X Hhige Hsccfrom.
  apply safeExec_proequiv with (c1 := dfs_scc_from g fadj_col_l fadj_row_l root u i).
  - exact (dfs_scc_from_exit g fadj_col_l fadj_row_l root u i Hhige).
  - exact Hsccfrom.
Qed.

(* dfs1 loop-exit closer: at i >= hi, dfs_finish_from ... u i ==
   (t <- get timer ;; set_finish u t).  The C post-loop reads timer_p[0],
   sets fin[u] = t0+1, timer_p[0] = t0+1 — exactly the nrm transition of
   `get (fun st t => t = timer st) ;; set_finish u t`: from st (timer = timer_m)
   it steps to st' with timer st' = S (timer st) and finish st' u = S (timer st).
   Given the safeExec witness sigma with pre_dfs1 vis_m fin_m timer_m and
   timer_m = Z.to_nat (timer sigma), the post-state sigma' has
     timer sigma' = S timer_m,  finish sigma' u = S timer_m,
   which matches pre_dfs1 vis_m (replace_Znth u (timer_m+1) fin_m) (S timer_m)
   (vis1 unchanged by set_finish; finish[u] = timer_m+1; other finish preserved).
   Then X tt sigma' follows from the wp of the exit monad. *)
Lemma dfs1_return_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_m: Z) (X: unit -> KSt -> Prop),
  (0 <= u < adj_verts g)%Z ->
  (0 <= timer_m)%Z ->
  Zlength fin_m = adj_verts g ->
  (csr_hi u radj_row_l <= i)%Z ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_m)
           (dfs_finish_from g radj_col_l radj_row_l u i) X ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m
              (replace_Znth u (timer_m + 1) fin_m) (timer_m + 1)) (ret tt) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_m X
         Hub Htm Hlenfin Hhige Hsccfrom.
  assert (Hexit : PartialOrder_Setoid.equiv
            (dfs_finish_from g radj_col_l radj_row_l u i)
            (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
             assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; t <- get (fun st t => t = timer st) ;; set_finish u t))
    by (apply dfs_finish_from_exit; exact Hhige).
  assert (Hscc : safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_m)
                          (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
                           assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));; t <- get (fun st t => t = timer st) ;; set_finish u t) X).
  { eapply safeExec_proequiv with (c1 := dfs_finish_from g radj_col_l radj_row_l u i).
    - exact Hexit.
    - exact Hsccfrom. }
  apply safeExec_assertS_seq in Hscc.
  apply safeExec_assertS_seq in Hscc.
  destruct Hscc as [sigma [Hpre_asserts Hsafe]].
  destruct Hpre_asserts as [Htimer_eq [Hinv_sigma Hpre]].
  destruct Hpre as [Hpv [Hpf [Hpt [Hvi Hfi]]]].
  pose (sigma' := MkSt (S (timer sigma))
                       (fun v => if Z.eqb v u then S (timer sigma) else finish sigma v)
                       (visited1 sigma) (visited2 sigma)
                       (scc_id sigma) (scc_next sigma)).
  assert (Hfsu : finish sigma' u = S (timer sigma)).
  { unfold sigma'. simpl. destruct (Z.eqb u u) eqn:Eu.
    - reflexivity.
    - apply Z.eqb_neq in Eu. exfalso. apply Eu. reflexivity. }
  assert (Hfsv : forall v, v <> u -> finish sigma' v = finish sigma v).
  { intros v Hvne. unfold sigma'. simpl. destruct (Z.eqb v u) eqn:Ev.
    - apply Z.eqb_eq in Ev. exfalso. apply Hvne. exact Ev.
    - reflexivity. }
  assert (Htimer' : timer sigma' = S (timer sigma)) by (unfold sigma'; reflexivity).
  assert (Hvis1' : visited1 sigma' = visited1 sigma) by (unfold sigma'; reflexivity).
  assert (Hvis2' : visited2 sigma' = visited2 sigma) by (unfold sigma'; reflexivity).
  assert (Hsid' : scc_id sigma' = scc_id sigma) by (unfold sigma'; reflexivity).
  assert (Hsnext' : scc_next sigma' = scc_next sigma) by (unfold sigma'; reflexivity).
  assert (Hnrm : (t <- get (fun st t => t = timer st) ;; set_finish u t).(MonadErr.nrm)
                  sigma tt sigma').
  { cbv beta iota delta [MonadErr.bind MonadErr.nrm_nrm get set_finish custom].
    eexists. exists sigma. split.
    - split; [ reflexivity | reflexivity ].
    - simpl. split; [ exact Htimer' | ].
      split; [ exact Hfsu | ].
      split; [ exact Hfsv | ].
      split; [ exact Hvis1' | ].
      split; [ exact Hvis2' | ].
      split; [ exact Hsid' | ].
      exact Hsnext'. }
  assert (Hxtt : X tt sigma')
    by (eapply wp_spec; eassumption).
  unfold safeExec. exists sigma'. split.
  - unfold pre_dfs1.
    assert (HnZ : Z.to_nat (timer_m + 1) = S (Z.to_nat timer_m)).
    { rewrite Z.add_1_r. apply Z2Nat.inj_succ. lia. }
    rewrite HnZ. split; [ | split; [ | ] ].
    + intros x Hr. unfold sigma'. simpl. split; intros Hvis.
      * apply (proj1 (Hpv x Hr)). exact Hvis.
      * apply (proj2 (Hpv x Hr)). exact Hvis.
    + intros w Hr. unfold sigma'. simpl.
      destruct (Z.eqb w u) eqn:Eu0.
      * apply Z.eqb_eq in Eu0. subst w.
        assert (Hin : (0 <= u < Zlength fin_m)%Z) by (rewrite Hlenfin; lia).
        rewrite (Znth_replace_eq fin_m u (timer_m + 1) 0 Hin).
        rewrite HnZ. f_equal. exact Hpt.
      * apply Z.eqb_neq in Eu0.
        assert (Hin : (0 <= w < Zlength fin_m)%Z) by (rewrite Hlenfin; lia).
        rewrite (Znth_replace_neq fin_m w u (timer_m + 1) 0 Hin (proj1 Hub) Eu0).
        apply (Hpf w Hr).
    + split.
      * rewrite Htimer'. f_equal. exact Hpt.
      * split.
        -- intros w Hinvalid Hvis.
           unfold sigma' in Hvis. simpl in Hvis.
           exact (Hvi w Hinvalid Hvis).
        -- intros w Hinvalid.
           unfold sigma'. simpl.
           destruct (Z.eqb w u) eqn:Ewu.
           ++ apply Z.eqb_eq in Ewu. subst w. contradiction.
           ++ apply Hfi. exact Hinvalid.
  - unfold safe, weakestpre. split.
    + intro Herr. cbv beta iota delta [MonadErr.ret] in Herr. sets_unfold in Herr. exfalso. exact Herr.
    + intros r s' Hnrm2. cbv beta iota delta [MonadErr.ret] in Hnrm2. inversion Hnrm2; subst. exact Hxtt.
Qed.

Lemma dfs1_return_close_sequence_active :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_m: Z) (X: unit -> KSt -> Prop),
    (0 <= u < adj_verts g)%Z ->
    (0 <= timer_m < adj_verts g)%Z ->
    Zlength fin_m = adj_verts g ->
    dfs1_root_not_in_finish_prefix fin_m timer_m u ->
    (csr_hi u radj_row_l <= i)%Z ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1_m fin_m timer_m)
             (dfs_finish_from g radj_col_l radj_row_l u i) X ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1_m
                (replace_Znth timer_m u fin_m) (timer_m + 1)) (ret tt) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_m X
    Hu Htimer Hlenfin Hfresh Hhige Hfrom.
  assert (Hexit : PartialOrder_Setoid.equiv
            (dfs_finish_from g radj_col_l radj_row_l u i)
            (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
             assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));;
             t <- get (fun st t => t = timer st) ;; set_finish u t))
    by (apply dfs_finish_from_exit; exact Hhige).
  assert (Hsafe_exit : safeExec
    (pre_dfs1_sequence g radj_col_l radj_row_l vis1_m fin_m timer_m)
    (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
     assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));;
     t <- get (fun st t => t = timer st) ;; set_finish u t) X).
  { eapply safeExec_proequiv with
      (c1 := dfs_finish_from g radj_col_l radj_row_l u i);
      eauto. }
  apply safeExec_assertS_seq in Hsafe_exit.
  apply safeExec_assertS_seq in Hsafe_exit.
  destruct Hsafe_exit as [sigma [Hpre_asserts Hsafe]].
  destruct Hpre_asserts as [Htimer_count [Hinv_sigma Hpre]].
  destruct Hpre as [Hpv [Hinvalid_vis Hfinrep]].
  unfold fin_sequence_rep in Hfinrep.
  destruct Hfinrep as
    [Htimer_bounds [Hfin_len [Htimer_sigma
    [Hfin_prefix [Hfin_complete Hfin_invalid]]]]].
  pose (sigma' := MkSt (S (timer sigma))
                       (fun v => if Z.eqb v u then S (timer sigma) else finish sigma v)
                       (visited1 sigma) (visited2 sigma)
                       (scc_id sigma) (scc_next sigma)).
  assert (Hfsu : finish sigma' u = S (timer sigma)).
  { unfold sigma'. simpl. destruct (Z.eqb u u) eqn:Eu.
    - reflexivity.
    - apply Z.eqb_neq in Eu. exfalso. apply Eu. reflexivity. }
  assert (Hfsv : forall v, v <> u -> finish sigma' v = finish sigma v).
  { intros v Hvne. unfold sigma'. simpl. destruct (Z.eqb v u) eqn:Ev.
    - apply Z.eqb_eq in Ev. contradiction.
    - reflexivity. }
  assert (Htimer' : timer sigma' = S (timer sigma)) by (unfold sigma'; reflexivity).
  assert (Hvis1' : visited1 sigma' = visited1 sigma) by (unfold sigma'; reflexivity).
  assert (Hvis2' : visited2 sigma' = visited2 sigma) by (unfold sigma'; reflexivity).
  assert (Hsid' : scc_id sigma' = scc_id sigma) by (unfold sigma'; reflexivity).
  assert (Hsnext' : scc_next sigma' = scc_next sigma) by (unfold sigma'; reflexivity).
  assert (Hnrm : (t <- get (fun st t => t = timer st) ;; set_finish u t).(MonadErr.nrm)
                  sigma tt sigma').
  { cbv beta iota delta [MonadErr.bind MonadErr.nrm_nrm get set_finish custom].
    eexists. exists sigma. split.
    - split; [reflexivity | reflexivity].
    - simpl. split; [exact Htimer' |].
      split; [exact Hfsu |].
      split; [exact Hfsv |].
      split; [exact Hvis1' |].
      split; [exact Hvis2' |].
      split; [exact Hsid' |].
      exact Hsnext'. }
  assert (Hxtt : X tt sigma')
    by (eapply wp_spec; eassumption).
  assert (Hsucc_nat : Z.to_nat (timer_m + 1) = S (Z.to_nat timer_m)).
  { rewrite Z.add_1_r. apply Z2Nat.inj_succ. lia. }
  unfold safeExec. exists sigma'. split.
  - unfold pre_dfs1_sequence.
    split.
    + intros v Hv. rewrite Hvis1'. apply Hpv. exact Hv.
    + split.
      * intros v Hv. rewrite Hvis1'. apply Hinvalid_vis. exact Hv.
      * unfold fin_sequence_rep.
        split; [lia |].
        split.
        -- rewrite Zlength_replace_Znth. exact Hfin_len.
        -- split.
           ++ rewrite Htimer', Htimer_sigma. symmetry. exact Hsucc_nat.
           ++ split.
              ** intros t Ht.
                 destruct (Z.eq_dec t timer_m) as [-> | Hne].
                 --- rewrite (Znth_replace_eq fin_m timer_m u 0) by lia.
                     split; [exact Hu |].
                     rewrite Hfsu, Htimer_sigma.
                     reflexivity.
                 --- rewrite (Znth_replace_neq fin_m t timer_m u 0) by lia.
                     specialize (Hfin_prefix t ltac:(lia)) as [Hrange Hfinish].
                     split; [exact Hrange |].
                     rewrite Hfsv.
                     exact Hfinish.
                     intro Heq.
                     subst u.
                     apply (Hfresh t ltac:(lia)).
                     reflexivity.
              ** split.
                 --- intros v Hv Hnz.
                     destruct (Z.eq_dec v u) as [-> | Hne].
                     { exists timer_m.
                       split; [lia |].
                       rewrite (Znth_replace_eq fin_m timer_m u 0) by lia.
                       reflexivity. }
                     { assert (Hnz_old : finish sigma v <> 0%nat).
                       { rewrite <- Hfsv by exact Hne. exact Hnz. }
                       destruct (Hfin_complete v Hv Hnz_old) as [t [Ht Htval]].
                       exists t.
                       split; [lia |].
                       rewrite (Znth_replace_neq fin_m t timer_m u 0) by lia.
                       exact Htval. }
                 --- intros v Hinvalid.
                     unfold sigma'. simpl.
                     destruct (Z.eqb v u) eqn:Evu.
                     { apply Z.eqb_eq in Evu. subst v. lia. }
                     { apply Hfin_invalid. exact Hinvalid. }
  - unfold safe, weakestpre. split.
    + intro Herr. cbv beta iota delta [MonadErr.ret] in Herr. sets_unfold in Herr. exact Herr.
    + intros r s' Hnrm_ret.
      cbv beta iota delta [MonadErr.ret] in Hnrm_ret.
      inversion Hnrm_ret; subst.
      exact Hxtt.
Qed.


(* B1 fallouts: conditional step-closers for the recurse VC (partial_solve_8)
   and the Gap-B skip VC.  Each extracts the safeExec witness sigma, derives
   visited2/~visited2 of v (= Znth i fadj_col_l 0) at sigma via pre_dfs2, applies
   dfs_scc_from_skip_step / dfs_scc_from_recurse_step, and reconstructs. *)
Lemma dfs2_skip_close :
  forall (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) (root u i: Z)
         (vis2_m sid_m: list Z) (root_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u fadj_row_l)%Z ->
  (0 <= Znth i fadj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i fadj_col_l 0) vis2_m 0 <> 0%Z ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u i) X ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u (i + 1)) X.
Proof.
  intros g fadj_col_l fadj_row_l root u i vis2_m sid_m root_v X
         Hilt Hvvb Hvvis Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv Hps].
  assert (Hvisv : visited2 sigma (Znth i fadj_col_l 0))
    by (exact (proj2 (Hpv (Znth i fadj_col_l 0) Hvvb) Hvvis)).
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs2; split; assumption.
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_scc_from_skip_err_imp g fadj_col_l fadj_row_l root u i sigma Hilt Hvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_scc_from_skip_step g fadj_col_l fadj_row_l root u i sigma a s' Hilt Hvisv)).
      exact Ht.
Qed.

Lemma dfs2_recurse_close :
  forall (g: AdjGraph) (fadj_col_l fadj_row_l: list Z) (root u i: Z)
         (vis2_m sid_m: list Z) (root_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u fadj_row_l)%Z ->
  (0 <= Znth i fadj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i fadj_col_l 0) vis2_m 0 = 0%Z ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (dfs_scc_from g fadj_col_l fadj_row_l root u i) X ->
  safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis2_m sid_m root_v)
           (bind (dfs_scc g root (Znth i fadj_col_l 0))
                 (dfs_scc_fromK g fadj_col_l fadj_row_l root u (i + 1))) X.
Proof.
  intros g fadj_col_l fadj_row_l root u i vis2_m sid_m root_v X
         Hilt Hvvb Hvvis0 Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv Hps].
  assert (Hnvisv : ~ visited2 sigma (Znth i fadj_col_l 0)).
  { intro Hvv.
    assert (Hzz : Znth (Znth i fadj_col_l 0) vis2_m 0 <> 0%Z)
      by (apply (proj1 (Hpv (Znth i fadj_col_l 0) Hvvb)); exact Hvv).
    lia. }
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs2; split; assumption.
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_scc_from_recurse_err_imp g fadj_col_l fadj_row_l root u i sigma Hilt Hnvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_scc_from_recurse_step g fadj_col_l fadj_row_l root u i sigma a s' Hilt Hnvisv)).
      exact Ht.
Qed.

(* dfs1 analogues of dfs2_skip_close / dfs2_recurse_close.  vis-conditional
   cursor: at position i, v = Znth i radj_col_l 0; if visited1, SKIP (advance
   cursor); if not, RECURSE into dfs_finish g v then advance.  Each extracts
   the safeExec witness sigma, derives visited1/~visited1 of v at sigma via
   pre_dfs1, applies dfs_finish_from_skip_step / dfs_finish_from_recurse_step,
   and reconstructs. *)
Lemma dfs1_skip_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u radj_row_l)%Z ->
  (0 <= Znth i radj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i radj_col_l 0) vis1_m 0 <> 0%Z ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
           (dfs_finish_from g radj_col_l radj_row_l u i) X ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
           (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_v X
         Hilt Hvvb Hvvis Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv [Hpf [Hpt [Hvi Hfi]]]].
  assert (Hvisv : visited1 sigma (Znth i radj_col_l 0))
    by (exact (proj2 (Hpv (Znth i radj_col_l 0) Hvvb) Hvvis)).
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs1; split; [ exact Hpv | split; [ exact Hpf | split; [ exact Hpt | split; [ exact Hvi | exact Hfi ] ] ] ].
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_finish_from_skip_err_imp g radj_col_l radj_row_l u i sigma Hilt Hvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_finish_from_skip_step g radj_col_l radj_row_l u i sigma a s' Hilt Hvisv)).
      exact Ht.
Qed.

Lemma dfs1_recurse_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_v: Z) (X: unit -> KSt -> Prop),
  (i < csr_hi u radj_row_l)%Z ->
  (0 <= Znth i radj_col_l 0 < adj_verts g)%Z ->
  Znth (Znth i radj_col_l 0) vis1_m 0 = 0%Z ->
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
           (dfs_finish_from g radj_col_l radj_row_l u i) X ->
	  safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_m fin_m timer_v)
	           (pre <- get (fun st pre => pre = st);;
	            _ <- dfs_finish g (Znth i radj_col_l 0) ;;
	            assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
	                                   visited1 st (Znth i radj_col_l 0) /\
	                                   visited1 pre ⊆ visited1 st);;
	            dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_v X
         Hilt Hvvb Hvvis0 Hsccfrom.
  destruct Hsccfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv [Hpf [Hpt [Hvi Hfi]]]].
  assert (Hnvisv : ~ visited1 sigma (Znth i radj_col_l 0)).
  { intro Hvv.
    assert (Hzz : Znth (Znth i radj_col_l 0) vis1_m 0 <> 0%Z)
      by (apply (proj1 (Hpv (Znth i radj_col_l 0) Hvvb)); exact Hvv).
    lia. }
  unfold safeExec. exists sigma. split.
  - unfold pre_dfs1; split; [ exact Hpv | split; [ exact Hpf | split; [ exact Hpt | split; [ exact Hvi | exact Hfi ] ] ] ].
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. exfalso. apply Hnoerr.
      apply (dfs_finish_from_recurse_err_imp g radj_col_l radj_row_l u i sigma Hilt Hnvisv).
      exact Herr.
    + intros a s' Ht. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_finish_from_recurse_step g radj_col_l radj_row_l u i sigma a s' Hilt Hnvisv)).
      exact Ht.
Qed.

(* Scanned-neighbours conjunct helper (dfs2_entail_wit_3 group).  At cursor i,
   vertex v = Znth i fadj_col_l 0.  The conjunct requires both the lo-end
   neighbour and the i-end (= v) neighbour to be visited2.  The i-end is just
   v's visited fact (Hvisv); the lo-end is the scanned range [lo, i) when lo < i,
   or reduces to v when lo = i (the range is then empty and Znth lo = v).  This
   encapsulates the lo=i case split so the main-VC dispatch need not key on
   PreH numbers (reorder-immune). *)
Lemma dfs2_scanned_lo_close :
  forall (fc vis: list Z) (lo i v: Z),
    (forall j, ((lo <= j)%Z /\ (j < i)%Z) -> Znth (Znth j fc 0) vis 0 <> 0%Z) ->
    (lo <= i)%Z ->
    v = Znth i fc 0 ->
    Znth v vis 0 <> 0%Z ->
    Znth (Znth lo fc 0) vis 0 <> 0%Z.
Proof.
  intros fc vis lo i v Hscan Hli Hv Hvisv.
  destruct (Z.eqb lo i) eqn:E.
  - apply Z.eqb_eq in E. subst i. rewrite <- Hv. exact Hvisv.
  - apply Z.eqb_neq in E. assert (Hlli : ((lo <= lo)%Z /\ (lo < i)%Z)) by lia.
    exact (Hscan lo Hlli).
Qed.

(* ===================================================================== *)
(* dfs2_entry_close infrastructure (phase-2 entry refinement).            *)
(*                                                                        *)
(* The entry VC (dfs2_entail_wit_1_split_goal_9) reduces to: given        *)
(*   safeExec (pre_dfs2 vis sid) (dfs_scc g root u) X,                    *)
(* show safeExec (pre_dfs2 vis1 sid') (dfs_scc_from g fc fr root u lo) X, *)
(* where vis1 = replace_Znth u 1 vis, sid' = replace_Znth u (sid[root]) sid. *)
(*                                                                        *)
(* dfs2_repeat_body is the body of DFS_scc_f, u-parametrised, with the    *)
(* recursive leaf W = dfs_scc g root.  It is definitionally equal to the  *)
(* body of DFS_scc_f g root (dfs_scc g root) u (verified by reflexivity    *)
(* in dfs2_scc_unfold_repeat), so repeat_break congruence is free.        *)
(*                                                                        *)
(* visit2_pre_dfs2_step / set_scc_id_pre_dfs2_step peel the visit2 u +    *)
(* set_scc_id u root prelude off safeExec(dfs_scc g root u), leaving      *)
(* safeExec over repeat_break (dfs2_repeat_body g root u) empty at the    *)
(* post-visit/set_scc_id state.  dfs2_visit_setid_decompose composes the  *)
(* two peels with dfs2_scc_unfold_repeat + safeExec_proequiv.             *)
(*                                                                        *)
(* The remaining piece is dfs_scc_from_sim: the cursor-vs-repeat_break    *)
(* simulation (safe(repeat_break B e_set_i) -> safe(dfs_scc_from ... u i)),*)
(* which is the main wp-induction workload and is tracked separately.     *)
(* ===================================================================== *)

Definition dfs2_repeat_body (g: AdjGraph) (root u: Z)
  : (Z * Z -> Prop) -> program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  fun e_set =>
    choice
      (e <- any (Z * Z);;
       v <- any Z;;
       assume (fun (_ : KSt) => ~ e ∈ e_set);;
       assume (fun st => ~ visited2 st v);;
       assume (fun (_ : KSt) => step_aux g e u v);;
       dfs_scc g root v;;
       continue (e_set ∪ Sets.singleton e))
      (assume (fun st =>
                 forall (e: Z * Z) (v: Z),
                   step_aux g e u v ->
                   e ∈ e_set \/ visited2 st v);;
       assertS (fun st => scc_id st u = scc_id st root);;
       break tt).

Lemma dfs2_scc_unfold_repeat :
  forall (g: AdjGraph) (root u: Z),
  gvalid g ->
  dfs_scc g root u
  ==
  visit2 u ;; set_scc_id u root ;; repeat_break (dfs2_repeat_body g root u) ∅.
Proof.
  intros g root u Hg.
  rewrite (dfs_scc_unfold g root u Hg).
  unfold DFS_scc_f.
  reflexivity.
Qed.

Lemma visit2_pre_dfs2_step :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root_v u: Z),
    (Zlength vis = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    pre_dfs2 g fc fr vis sid root_v -@ visit2 u -⥅
      (pre_dfs2 g fc fr (replace_Znth u 1 vis) sid root_v) ♯ tt.
Proof.
  intros g fc fr vis sid root_v u Hvlen Hub st0 Hpre.
  destruct Hpre as [Hpv Hps].
  assert (HLu : (0 <= u < Zlength vis)%Z) by (rewrite Hvlen; exact Hub).
  pose (st1 := MkSt (timer st0) (finish st0) (visited1 st0)
                       (fun w => visited2 st0 w \/ w = u) (scc_id st0) (scc_next st0)).
  assert (Hnrm : (visit2 u).(MonadErr.nrm) st0 tt st1).
  { unfold visit2. simpl. split.
    - (* visited2 st1 == visited2 st0 ∪ {u} *)
      unfold st1. simpl. sets_unfold. intros w. split; intros Hw.
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
    - unfold st1. simpl. repeat split; reflexivity.
  }
  exists st1. split; [ exact Hnrm | ].
  unfold pre_dfs2. split.
  - intros w Hw. assert (HLw : (0 <= w < Zlength vis)%Z) by (rewrite Hvlen; exact Hw).
    unfold st1. simpl. split; intros Hvis.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. rewrite (Znth_replace_eq vis u 1 0 HLu). lia.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis w u 1 0 HLw (proj1 HLu) E).
        destruct Hvis as [Hv | Hwu].
        -- apply (proj1 (Hpv w Hw)). exact Hv.
        -- exfalso. apply E. exact Hwu.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. right. reflexivity.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis w u 1 0 HLw (proj1 HLu) E) in Hvis.
        left. apply (proj2 (Hpv w Hw)). exact Hvis.
  - intros w Hw. unfold st1. simpl. exact (Hps w Hw).
Qed.

Lemma set_scc_id_pre_dfs2_step :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root_v u root: Z),
    (Zlength vis = adj_verts g)%Z ->
    (Zlength sid = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    (0 <= root < adj_verts g)%Z ->
    pre_dfs2 g fc fr vis sid root_v -@ set_scc_id u root -⥅
      (pre_dfs2 g fc fr vis (replace_Znth u (Znth root sid 0) sid) root_v) ♯ tt.
Proof.
  intros g fc fr vis sid root_v u root Hvlen Hslen Hub Hroot st0 Hpre.
  destruct Hpre as [Hpv Hps].
  assert (HLu : (0 <= u < Zlength sid)%Z) by (rewrite Hslen; exact Hub).
  assert (HLroot : (0 <= root < Zlength sid)%Z) by (rewrite Hslen; exact Hroot).
  pose (st1 := MkSt (timer st0) (finish st0) (visited1 st0) (visited2 st0)
              (fun w => if Z.eqb w u then scc_id st0 root else scc_id st0 w)
              (scc_next st0)).
  assert (Hnrm : (set_scc_id u root).(MonadErr.nrm) st0 tt st1).
  { unfold set_scc_id. simpl. split.
    - unfold st1. simpl. destruct (Z.eqb u u) eqn:E.
      + reflexivity.
      + apply Z.eqb_neq in E. exfalso. apply E. reflexivity.
    - split.
      + intros v Hvne. unfold st1. simpl. destruct (Z.eqb v u) eqn:E.
        * apply Z.eqb_eq in E. exfalso. apply Hvne. exact E.
        * reflexivity.
      + unfold st1. simpl. repeat split; reflexivity.
  }
  exists st1. split; [ exact Hnrm | ].
  unfold pre_dfs2. split.
  - intros w Hw. exact (Hpv w Hw).
  - intros w Hw. assert (HLw : (0 <= w < Zlength sid)%Z) by (rewrite Hslen; exact Hw).
    unfold st1. simpl. destruct (Z.eqb w u) eqn:E.
    + apply Z.eqb_eq in E. subst w. rewrite (Znth_replace_eq sid u (Znth root sid 0) 0 HLu).
      apply Hps. exact Hroot.
    + apply Z.eqb_neq in E. rewrite (Znth_replace_neq sid w u (Znth root sid 0) 0 HLw (proj1 HLu) E).
      apply Hps. exact Hw.
Qed.

Lemma dfs2_visit_setid_decompose :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root_v u root: Z) (X: unit -> KSt -> Prop),
    gvalid g ->
    (Zlength vis = adj_verts g)%Z ->
    (Zlength sid = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    (0 <= root < adj_verts g)%Z ->
    safeExec (pre_dfs2 g fc fr vis sid root_v) (dfs_scc g root u) X ->
    safeExec (pre_dfs2 g fc fr (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
             (repeat_break (dfs2_repeat_body g root u) ∅) X.
Proof.
  intros g fc fr vis sid root_v u root X Hg Hvlen Hslen Hub Hroot Hsafe.
  rewrite (dfs2_scc_unfold_repeat g root u Hg) in Hsafe.
  apply (highstepbind_derive (visit2 u)
            (fun _ => set_scc_id u root ;; repeat_break (dfs2_repeat_body g root u) ∅)
            (pre_dfs2 g fc fr vis sid root_v) tt
            (pre_dfs2 g fc fr (replace_Znth u 1 vis) sid root_v)
            (visit2_pre_dfs2_step g fc fr vis sid root_v u Hvlen Hub)) in Hsafe.
  assert (Hvlen1 : (Zlength (replace_Znth u 1 vis) = adj_verts g)%Z).
  { rewrite Zlength_replace_Znth. exact Hvlen. }
  apply (highstepbind_derive (set_scc_id u root)
            (fun _ => repeat_break (dfs2_repeat_body g root u) ∅)
            (pre_dfs2 g fc fr (replace_Znth u 1 vis) sid root_v) tt
            (pre_dfs2 g fc fr (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
            (set_scc_id_pre_dfs2_step g fc fr (replace_Znth u 1 vis) sid root_v u root
               Hvlen1 Hslen Hub Hroot)) in Hsafe.
  exact Hsafe.
Qed.

(* ================================================================= *)
(* Reusable MonadErr helper lemmas (pure monad, no algorithm props). *)
(* Used by dfs_scc_from_sim to factor the repeat_break nrm-step out of *)
(* the simulation's BASE/RECURSE cases.                               *)
(* ================================================================= *)

(* wp_seq: sequence-specialised wp_bind, bridging the eta gap between
   `f ;; rest` (= bind f (fun _ => rest)) and wp_bind's `x <- f ;; g x`. *)
Lemma wp_seq {Σ A B: Type} (f: program Σ A) (rest: program Σ B) (Q: B -> Σ -> Prop) :
  (weakestpre (f ;; rest) Q == weakestpre f (fun _ => weakestpre rest Q))%sets.
Proof.
  intros σ. apply (wp_bind f (fun (_:A) => rest) Q).
Qed.

(* repeat_break_break_step: body produces by_break b at sigma (no state change)
   -> repeat_break produces b at sigma (first iteration takes the break branch). *)
Lemma repeat_break_break_step :
  forall (Σ: Type) {A: Type} {B: Type}
         (body: A -> program Σ (CntOrBrk A B)) (a: A) (b: B) (σ: Σ),
    (body a).(MonadErr.nrm) σ (@by_break A B b) σ ->
    (repeat_break body a).(MonadErr.nrm) σ b σ.
Proof.
  intros Σ A B body a b σ Hbodystep.
  pose proof (repeat_break_unfold body) as Hunf.
  unfold equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  specialize (Hunf a) as Hpt.
  destruct Hpt as [Hnrmpt Herrpt].
  sets_unfold in Hnrmpt.
  specialize (Hnrmpt σ b σ) as [Hfwd Hbwd].
  apply Hbwd.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists (by_break b). exists σ. split.
  - exact Hbodystep.
  - simpl.
    split; [ reflexivity | reflexivity ].
Qed.

(* repeat_break_break_step_gen: generalised break-step allowing the body to
   change the state (sigma -> sigma') before emitting by_break b.  Needed by
   dfs_finish_from_sim BASE: DFS_finish_f's break branch runs `set_finish u t`,
   which mutates the state, unlike phase-2's break (assertS sid ;; break). *)
Lemma repeat_break_break_step_gen :
  forall (Σ: Type) {A: Type} {B: Type}
         (body: A -> program Σ (CntOrBrk A B)) (a: A) (b: B) (σ σ': Σ),
    (body a).(MonadErr.nrm) σ (@by_break A B b) σ' ->
    (repeat_break body a).(MonadErr.nrm) σ b σ'.
Proof.
  intros Σ A B body a b σ σ' Hbodystep.
  pose proof (repeat_break_unfold body) as Hunf.
  unfold equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  specialize (Hunf a) as Hpt.
  destruct Hpt as [Hnrmpt Herrpt].
  sets_unfold in Hnrmpt.
  specialize (Hnrmpt σ b σ') as [Hfwd Hbwd].
  apply Hbwd.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists (by_break b). exists σ'. split.
  - exact Hbodystep.
  - simpl.
    split; [ reflexivity | reflexivity ].
Qed.

(* repeat_break_continue_step: body produces by_continue a' at (σ -> σ'),
   then repeat_break body a' produces b at (σ' -> σ'') -> repeat_break body a
   produces b at (σ -> σ''). *)
Lemma repeat_break_continue_step :
  forall (Σ: Type) {A: Type} {B: Type}
         (body: A -> program Σ (CntOrBrk A B)) (a a': A) (σ σ': Σ) (b: B) (σ'': Σ),
    (body a).(MonadErr.nrm) σ (by_continue a') σ' ->
    (repeat_break body a').(MonadErr.nrm) σ' b σ'' ->
    (repeat_break body a).(MonadErr.nrm) σ b σ''.
Proof.
  intros Σ A B body a a' σ σ' b σ'' Hbodystep Hrec.
  pose proof (repeat_break_unfold body) as Hunf.
  unfold equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  specialize (Hunf a) as Hpt.
  destruct Hpt as [Hnrmpt Herrpt].
  sets_unfold in Hnrmpt.
  specialize (Hnrmpt σ b σ'') as [Hfwd Hbwd].
  apply Hbwd.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists (by_continue a'). exists σ'. split.
  - exact Hbodystep.
  - simpl. exact Hrec.
Qed.

(* ===================================================================== *)
(* dfs_scc_from_sim: cursor (dfs_scc_from) vs repeat_break simulation.   *)
(* The recursive dfs_scc g root v call is treated as an atom; only the   *)
(* scheduling layer (cursor vs repeat_break body dispatch) is related.   *)
(* Fuel: induction on Z.to_nat (hi - i).                                 *)
(* ===================================================================== *)
Lemma dfs_scc_from_sim :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root u: Z) (lo hi i: Z)
         (n: nat) (X: unit -> KSt -> Prop) (σ: KSt),
    let B := dfs2_repeat_body g root u in
    csr_lo u fr = lo ->
    csr_hi u fr = hi ->
    csr_wf2 g fc fr vis sid ->
    csr2_faithful g fc fr ->
    (0 <= u < adj_verts g)%Z ->
    Z.to_nat (hi - i) = n ->
    (lo <= i)%Z ->
    forall (e_set: Z * Z -> Prop),
      (forall (e: Z * Z), e_set e ->
         exists k, (lo <= k < i)%Z /\ e = (u, Znth k fc 0)) ->
      (forall k, (lo <= k < i)%Z -> ~ e_set (u, Znth k fc 0) ->
         visited2 σ (Znth k fc 0)) ->
      (forall j, (lo <= j < hi)%Z -> ~ visited2 σ (Znth j fc 0) ->
         ~ e_set (u, Znth j fc 0)) ->
      scc_id σ u = scc_id σ root ->
      visited2 σ u ->
      safe σ (repeat_break B e_set) X ->
      safe σ (dfs_scc_from g fc fr root u i) X.
Proof.
  intros g fc fr vis sid root u lo hi i n X σ B Hlo Heqhi Hwf Hfaith Hu Hfuel Hloi e_set
         HA HB HE HC HD Hsafe.
  revert i X σ Hfuel Hloi e_set HA HB HE HC HD Hsafe.
  induction n as [|n' IHn].
  - (* BASE: Z.to_nat (hi - i) = 0, hence i >= hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HC HD Hsafe.
    assert (Hge : (hi <= i)%Z).
    { destruct (Z.le_gt_cases hi i) as [Hle | Hgt]; [ exact Hle | ].
      exfalso.
      assert (Hpos : (0 < hi - i)%Z) by lia.
      destruct (Z.eq_dec (hi - i) 0) as [Heq | Hneq].
      - subst. lia.
      - assert (Hn0 : (Z.to_nat (hi - i) <> 0)%nat).
        { intro Hz. assert (0 <= hi - i)%Z by lia.
          pose proof (Z2Nat.id (hi - i) H) as Hid.
          rewrite Hz in Hid. lia. }
        rewrite Hfuel in Hn0. exfalso. apply Hn0. reflexivity. }
    assert (Hclosure : (forall (e: Z * Z) (v: Z), step_aux g e u v ->
                                    e ∈ e_set \/ visited2 σ v)).
    { intros e v Hstep.
      assert (Hstep_g : reachable_basic.step g u v) by (eapply step_trivial; eassumption).
      destruct Hstep as [Heq [Hxv [Hvv Hiny]]].
      subst e.
      pose proof (Hfaith u v Hxv Hvv) as Hiff.
      apply (proj1 Hiff) in Hstep_g as [j [Hjlo Hjv]].
      destruct (classic (e_set (u, v))) as [Hin | Hnin].
      - left. exact Hin.
      - right. rewrite <- Hjv. apply (HB j). lia.
        rewrite Hjv. exact Hnin. }
    assert (Hbodystep : (B e_set).(MonadErr.nrm) σ (@by_break (Z*Z->Prop) unit tt) σ).
    { unfold B, dfs2_repeat_body.
      unfold choice. simpl.
      right.
      unfold_monad. simpl.
      eexists tt. eexists σ. split.
      - split; [ reflexivity | exact Hclosure ].
      - eexists tt. eexists σ. split.
        + split; [ reflexivity | exact HC ].
        + simpl. split; [ reflexivity | reflexivity ]. }
    assert (Hrbstep : (repeat_break B e_set).(MonadErr.nrm) σ tt σ).
    { eapply repeat_break_break_step. exact Hbodystep. }
    assert (Hxtt : X tt σ) by (eapply wp_spec; eassumption).
    unfold safe in *.
    assert (Hge' : (csr_hi u fr <= i)%Z) by (rewrite Heqhi; exact Hge).
    pose proof (wp_progequiv (ret tt) (dfs_scc_from g fc fr root u i) X
                  (dfs_scc_from_exit g fc fr root u i Hge')) as Hwp.
    sets_unfold in Hwp.
    specialize (Hwp σ) as [Hfwd Hbwd].
    unfold weakestpre in *.
    sets_unfold in Hfwd.
    apply Hfwd.
    sets_unfold.
    split.
    + intro Herr. simpl in Herr. exact Herr.
    + intros r σ' Hretstep. simpl in Hretstep.
      destruct Hretstep as [Hr Hσ]. subst r. subst σ'.
      exact Hxtt.
  - (* STEP: hi - i = S n', i.e. lo <= i < hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HC HD Hsafe.
    assert (Hilt : (i < hi)%Z).
    { assert (Hnonneg : (0 <= hi - i)%Z).
      { destruct (Z.le_gt_cases hi i) as [Hle | Hgt].
        - exfalso. assert (Heqz : hi - i = 0) by lia.
          rewrite Heqz in Hfuel. simpl in Hfuel. discriminate.
        - lia. }
      lia. }
    assert (Hilt' : (i < csr_hi u fr)%Z) by (rewrite Heqhi; exact Hilt).
    set (v := Znth i fc 0) in *.
    destruct (classic (visited2 σ v)) as [Hvisv | Hnvisv].
    + (* SKIP: visited2 σ v *)
      assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
      { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
        assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
        rewrite Hsub in Hfuel.
        rewrite Z2Nat.inj_add in Hfuel by lia.
        rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
      assert (Hloi' : (lo <= i + 1)%Z) by lia.
      assert (HA' : forall (e: Z * Z), e_set e ->
                     exists k, (lo <= k < i + 1)%Z /\ e = (u, Znth k fc 0)).
      { intros e He. destruct (HA e He) as [k [Hk Heq]]. exists k. split; [ lia | exact Heq ]. }
      assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set (u, Znth k fc 0) ->
                     visited2 σ (Znth k fc 0)).
      { intros k Hk Hne.
        destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
        - apply (HB k); [ lia | exact Hne ].
        - assert (Hki : k = i) by lia. subst k. exact Hvisv. }
      assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited2 σ (Znth j fc 0) ->
                     ~ e_set (u, Znth j fc 0)).
      { exact HE. }
      assert (Hsafe_ih : safe σ (dfs_scc_from g fc fr root u (i + 1)) X).
      { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
                      exact HC | exact HD | exact Hsafe ]. }
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * intro Herr.
        destruct Hsafe_ih as [Hnoerr _].
        exfalso. apply Hnoerr.
        apply (dfs_scc_from_skip_err_rev_imp g fc fr root u i σ Hilt' Hvisv).
        exact Herr.
      * intros a s' Hstep.
        destruct Hsafe_ih as [_ Hpost].
        apply Hpost.
        apply (proj1 (dfs_scc_from_skip_step g fc fr root u i σ a s' Hilt' Hvisv)).
        exact Hstep.
    + (* RECURSE: ~visited2 σ v *)
      assert (Hagvalid : gvalid g) by (destruct Hwf as [Hgv _]; exact Hgv).
      assert (Hvbound : (0 <= v < adj_verts g)%Z).
      { pose proof Hwf as [Hgv0 [Hlenfr [Hlenvis [Hlensid [Hmof [Hlo0 [Hhilem [Hcolbound [Hlolohi Hmofbound]]]]]]]]].
        assert (Hhilem_u : (csr_hi u fr <= m_of fr)%Z) by (apply Hhilem; exact Hu).
        assert (Hlo0u : (0 <= csr_lo u fr)%Z) by (apply Hlo0; exact Hu).
        assert (Him : (0 <= i < m_of fr)%Z).
        { split; [ rewrite Hlo in Hlo0u; lia | lia ]. }
        exact (Hcolbound i Him). }
      assert (Hnotinv : ~ e_set (u, v)).
      { apply (HE i). split; [ exact Hloi | exact Hilt ]. exact Hnvisv. }
      assert (Hstep_g : reachable_basic.step g u v).
      { destruct (Hfaith u v Hu Hvbound) as [Hfwd Hbwd].
        apply Hbwd. exists i. split.
        - assert (Hloi' : (csr_lo u fr <= i)%Z). { rewrite Hlo. exact Hloi. }
          split; [ exact Hloi' | exact Hilt' ].
        - reflexivity. }
      assert (Hstepeq : step_aux g (u, v) u v).
      { destruct Hstep_g as [e Heq].
        destruct Heq as [Heqrefl [Hxu [Hyv Hiny]]].
        simpl in *. subst e. split; [ reflexivity | split; [ exact Hu | split;
          [ exact Hvbound | exact Hiny ] ] ]. }
      set (e_set' := e_set ∪ Sets.singleton (u, v)).
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * (* ~err (dfs_scc_from ... u i) σ *)
        assert (HnoerrBE : ~ (B e_set).(MonadErr.err) σ).
        { assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                   (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                   (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          pose proof Hsafe as Hsafe0. apply Hwpb in Hsafe0.
          sets_unfold in Hsafe0. destruct Hsafe0 as [HnoerrBind _].
          apply bind_noerr_iff in HnoerrBind. destruct HnoerrBind as [Hne _]. exact Hne. }
        intro Herr.
        apply (dfs_scc_from_recurse_err_rev_imp g fc fr root u i σ Hilt' Hnvisv) in Herr.
        apply bind_err_iff in Herr.
        destruct Herr as [Herrv | [ha [smid [Hnm Hsccerr]]]].
        -- (* dfs_scc g root v errs at σ: contradiction with ~err (B e_set) σ. *)
           exfalso. apply HnoerrBE.
           unfold B, dfs2_repeat_body, choice. sets_unfold. left.
           apply bind_err_iff. right.
           eexists (u, v). eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists v. eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnotinv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnvisv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hstepeq ]. }
           apply bind_err_iff. left. exact Herrv.
        -- (* dfs_scc_from (i+1) errs at smid *)
           assert (Hbodycont_smid :
                     (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') smid).
           { unfold B, dfs2_repeat_body, choice. simpl.
             left. simpl.
             eexists (u, v). eexists σ. split.
             - reflexivity.
             - eexists v. eexists σ. split.
               + reflexivity.
               + eexists tt. eexists σ. split.
                 * split; [ reflexivity | exact Hnotinv ].
                 * eexists tt. eexists σ. split.
                   -- split; [ reflexivity | exact Hnvisv ].
                   -- eexists tt. eexists σ. split.
                      ++ split; [ reflexivity | exact Hstepeq ].
                      ++ eexists ha. eexists smid. split.
                         ** exact Hnm.
                         ** simpl. split; [ reflexivity | reflexivity ]. }
           assert (Hsafe_smid : safe smid (repeat_break B e_set') X).
           { unfold safe in *.
             unfold weakestpre in *.
             assert (Hunf : @equiv (program KSt unit) _
                           (repeat_break B e_set)
                           (x <- B e_set ;;
                            match x with
                            | by_continue a' => repeat_break B a'
                            | by_break b' => ret b'
                            end)).
             { pose proof (repeat_break_unfold B) as Hu2.
               unfold equiv in Hu2. simpl in Hu2.
               unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
               specialize (Hu2 e_set) as [Hn Hh].
               constructor; assumption. }
             pose proof (wp_progequiv
                           (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                           (repeat_break B e_set) X Hunf) as Hwp.
             sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
             unfold weakestpre in Hwpb. sets_unfold in Hwpb.
             apply Hwpb in Hsafe.
             sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
             apply bind_noerr_iff in HnoerrBind.
             destruct HnoerrBind as [HnoerrBEset HpostBEset].
             split.
             - intro Herr'.
               assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
                                    | by_continue a' => repeat_break B a'
                                    | by_break b' => ret b' end).(MonadErr.err) smid).
               { simpl. exact Herr'. }
               apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') smid Hbodycont_smid) in Herrmatch.
               exact Herrmatch.
             - intros r0 σf Hrb.
               apply HpostBind.
               assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
               { unfold MonadErr.bind. simpl.
                 eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists smid. split.
                 - exact Hbodycont_smid.
                 - simpl. exact Hrb. }
               exact HnrmMatch. }
           assert (Huneqv : u <> v).
           { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
           assert (Hvis_mono_smid : visited2 σ ⊆ visited2 smid).
           { pose proof (@DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
               as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             specialize (HhNrm ha σ smid (refl_equal _) Hnm) as [_ [Hmono _]].
             exact Hmono. }
           assert (Hvis_self_smid : visited2 smid v).
           { pose proof (@DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
               as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             specialize (HhNrm ha σ smid (refl_equal _) Hnm) as [Hself _].
             exact Hself. }
           assert (HA'_smid : forall (e: Z * Z), e_set' e ->
                               exists k, (lo <= k < i + 1)%Z /\ e = (u, Znth k fc 0)).
           { intros e He. sets_unfold in He. destruct He as [He | Heuv].
             - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
             - exists i. split; [ split; [ exact Hloi | lia ] | symmetry; exact Heuv ]. }
           assert (HB'_smid : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (u, Znth k fc 0) ->
                               visited2 smid (Znth k fc 0)).
           { intros k Hk Hne.
             destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
             - assert (HkZnth_neq_v : Znth k fc 0 <> v).
               { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
               assert (Hne_eset : ~ e_set (u, Znth k fc 0)).
               { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
               assert (Hklt : (lo <= k < i)%Z) by lia.
               apply Hvis_mono_smid. apply (HB k Hklt Hne_eset).
             - assert (Hki : k = i) by lia. subst k.
               exfalso. apply Hne. sets_unfold. right. reflexivity. }
           assert (HE'_smid : forall j, (lo <= j < hi)%Z -> ~ visited2 smid (Znth j fc 0) ->
                               ~ e_set' (u, Znth j fc 0)).
           { intros j Hj Hnvisj.
             destruct (Z.eq_dec (Znth j fc 0) v) as [Heq | Hneq].
             - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_self_smid).
             - intro Hin. apply Hneq.
               sets_unfold in Hin. destruct Hin as [HinE | Hsin].
               + assert (Hnvis_orig : ~ visited2 σ (Znth j fc 0)).
                 { intro Hv. apply Hnvisj. apply Hvis_mono_smid. exact Hv. }
                 exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
               + injection Hsin as Heqv. exact (eq_sym Heqv). }
           assert (HC'_smid : scc_id smid u = scc_id smid root).
           { pose proof (@DFS_scc_same_root_id AdjGraph Z (Z * Z) KG g σ root v)
               as Hh.
             unfold Hoare in Hh. destruct Hh as [HhNrm _].
             specialize (HhNrm ha σ smid (refl_equal _) Hnm) as [_ [Hkept_sid [Hsid_root _]]].
             rewrite (Hkept_sid u HD Huneqv).
             rewrite Hsid_root.
             exact HC. }
           assert (HD'_smid : visited2 smid u).
           { apply Hvis_mono_smid. exact HD. }
           assert (Hloi_smid : (lo <= i + 1)%Z) by lia.
           assert (Hfuel_smid : Z.to_nat (hi - (i + 1)) = n').
           { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
             assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
             rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
             rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
           assert (Hsafe_ih_smid : safe smid (dfs_scc_from g fc fr root u (i + 1)) X).
           { eapply IHn; [ exact Hfuel_smid | exact Hloi_smid | exact HA'_smid | exact HB'_smid |
                           exact HE'_smid | exact HC'_smid | exact HD'_smid | exact Hsafe_smid ]. }
           destruct Hsafe_ih_smid as [Hnoerr_smid _].
           exfalso. apply Hnoerr_smid. exact Hsccerr.
      * (* forall r σ', nrm (dfs_scc_from ... u i) σ r σ' -> X r σ' *)
        intros r σ' Hstep.
        apply (proj1 (dfs_scc_from_recurse_step g fc fr root u i σ r σ' Hilt' Hnvisv)) in Hstep.
        apply bind_nrm_iff in Hstep.
        destruct Hstep as [hu [σ'' [Hdfsstep Hcontstep]]].
        assert (Hbodycont : (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') σ'').
        { unfold B, dfs2_repeat_body, choice. simpl.
          left. simpl.
          eexists (u, v). eexists σ. split.
          - reflexivity.
          - eexists v. eexists σ. split.
            + reflexivity.
            + eexists tt. eexists σ. split.
              * split; [ reflexivity | exact Hnotinv ].
              * eexists tt. eexists σ. split.
                -- split; [ reflexivity | exact Hnvisv ].
                -- eexists tt. eexists σ. split.
                   ++ split; [ reflexivity | exact Hstepeq ].
                   ++ eexists hu. eexists σ''. split.
                      ** exact Hdfsstep.
                      ** simpl. split; [ reflexivity | reflexivity ]. }
        assert (Hsafe'' : safe σ'' (repeat_break B e_set') X).
        { unfold safe in *.
          unfold weakestpre in *.
          assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                        (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                        (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          apply Hwpb in Hsafe.
          sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
          apply bind_noerr_iff in HnoerrBind.
          destruct HnoerrBind as [HnoerrBEset HpostBEset].
          split.
          - intro Herr'.
            assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
                                 | by_continue a' => repeat_break B a'
                                 | by_break b' => ret b' end).(MonadErr.err) σ'').
            { simpl. exact Herr'. }
            apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') σ'' Hbodycont) in Herrmatch.
            exact Herrmatch.
          - intros r0 σf Hrb.
            apply HpostBind.
            assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
            { unfold MonadErr.bind. simpl.
              eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists σ''. split.
              - exact Hbodycont.
              - simpl. exact Hrb. }
            exact HnrmMatch. }
        assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
        { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
          assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
          rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
          rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
        assert (Hloi' : (lo <= i + 1)%Z) by lia.
        assert (HA' : forall (e: Z * Z), e_set' e ->
                       exists k, (lo <= k < i + 1)%Z /\ e = (u, Znth k fc 0)).
        { intros e He. sets_unfold in He. destruct He as [He | Heuv].
          - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
          - exists i. split; [ split; [ exact Hloi | lia ] | symmetry; exact Heuv ]. }
        assert (Huneqv : u <> v).
        { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
        assert (HQstrong : visited2 σ'' v /\ visited2 σ ⊆ visited2 σ'').
        { pose proof (@DFS_scc_neighbor_visited_strong AdjGraph Z (Z * Z) KG g Hagvalid σ root v)
            as Hh.
          unfold Hoare in Hh.
          destruct Hh as [HhNrm _].
          specialize (HhNrm hu σ σ'' (refl_equal _) Hdfsstep) as [Hself [Hmono _]].
          split; [ exact Hself | exact Hmono ]. }
        assert (HQsid :
                  (forall (w: Z), visited2 σ'' w -> ~ visited2 σ w ->
                                  scc_id σ'' w = scc_id σ'' root) /\
                  (forall (w: Z), visited2 σ w -> w <> v -> scc_id σ'' w = scc_id σ w) /\
                  scc_id σ'' root = scc_id σ root /\ visited2 σ ⊆ visited2 σ'').
        { pose proof (@DFS_scc_same_root_id AdjGraph Z (Z * Z) KG g σ root v)
            as Hh.
          unfold Hoare in Hh.
          destruct Hh as [HhNrm _].
          exact (HhNrm hu σ σ'' (refl_equal _) Hdfsstep). }
        destruct HQstrong as [Hvis_v_self Hvis_mono].
        destruct HQsid as [Hnew_sid [Hkept_sid [Hsid_root Hvis_mono2]]].
        assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (u, Znth k fc 0) ->
                       visited2 σ'' (Znth k fc 0)).
        { intros k Hk Hne.
          destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
          - assert (HkZnth_neq_v : Znth k fc 0 <> v).
            { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
            assert (Hne_eset : ~ e_set (u, Znth k fc 0)).
            { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
            pose proof (HB k) as Hkb.
            assert (Hklt : (lo <= k < i)%Z) by lia.
            specialize (Hkb Hklt Hne_eset).
            apply Hvis_mono. exact Hkb.
          - assert (Hki : k = i) by lia. subst k.
            exfalso. apply Hne. sets_unfold. right. reflexivity. }
        assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited2 σ'' (Znth j fc 0) ->
                       ~ e_set' (u, Znth j fc 0)).
        { intros j Hj Hnvisj.
          destruct (Z.eq_dec (Znth j fc 0) v) as [Heq | Hneq].
          - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_v_self).
          - intro Hin. apply Hneq.
            sets_unfold in Hin. destruct Hin as [HinE | Hsin].
            + assert (Hnvis_orig : ~ visited2 σ (Znth j fc 0)).
              { intro Hv. apply Hnvisj. apply Hvis_mono. exact Hv. }
              exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
            + injection Hsin as Heqv. exact (eq_sym Heqv). }
        assert (HC' : scc_id σ'' u = scc_id σ'' root).
        { rewrite (Hkept_sid u HD Huneqv).
          rewrite Hsid_root.
          exact HC. }
        assert (HD' : visited2 σ'' u).
        { apply Hvis_mono. exact HD. }
        assert (Hsafe_ih : safe σ'' (dfs_scc_from g fc fr root u (i + 1)) X).
        { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
                        exact HC' | exact HD' | exact Hsafe'' ]. }
        apply Hsafe_ih. exact Hcontstep.
Qed.

(* ===================================================================== *)
(* dfs2_entry_close: the entry refinement (split_goal_9).                *)
(* Combines dfs2_visit_setid_decompose (peel visit2 + set_scc_id prelude,*)
(* landing safeExec over repeat_break (dfs2_repeat_body g root u) ∅)     *)
(* with dfs_scc_from_sim (cursor ≡ repeat_break simulation at i=lo).     *)
(* ===================================================================== *)
Lemma dfs2_entry_close :
  forall (g: AdjGraph) (fc fr vis sid: list Z) (root u root_v: Z)
         (X: unit -> KSt -> Prop),
    csr_wf2 g fc fr vis sid ->
    csr2_faithful g fc fr ->
    (0 <= u < adj_verts g)%Z ->
    (0 <= root < adj_verts g)%Z ->
    safeExec (pre_dfs2 g fc fr vis sid root_v) (dfs_scc g root u) X ->
    safeExec (pre_dfs2 g fc fr (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
             (dfs_scc_from g fc fr root u (csr_lo u fr)) X.
Proof.
  intros g fc fr vis sid root u root_v X Hwf Hfaith Hub Hroot Hsafe.
  (* Extract the csr_wf2 conjuncts we need, keeping Hwf intact for sim. *)
  destruct Hwf as [Hgv [Hlenfr [Hlenvis [Hlensid [Hmof [Hlo0 [Hhilem [Hcolbound [Hlolohi Hmofbound]]]]]]]]].
  (* Re-conjoin Hwf for dfs_scc_from_sim. *)
  assert (Hwf' : csr_wf2 g fc fr vis sid).
  { unfold csr_wf2.
    repeat (split; [ assumption | ]);
    try assumption. }
  (* Peel visit2 u + set_scc_id u root prelude: safeExec over repeat_break B ∅. *)
  assert (Hvislen : (Zlength vis = adj_verts g)%Z) by exact Hlenvis.
  assert (Hsidlen : (Zlength sid = adj_verts g)%Z) by exact Hlensid.
  pose proof (dfs2_visit_setid_decompose g fc fr vis sid root_v u root X
                Hgv Hvislen Hsidlen Hub Hroot Hsafe) as Hdec.
  (* Hdec : safeExec (pre_dfs2 ... (replace_Znth u 1 vis) (replace_Znth u (Znth root sid 0) sid) root_v)
                       (repeat_break (dfs2_repeat_body g root u) ∅) X. *)
  destruct Hdec as [σ' [Hpreσ' Hsafeσ']].
  pose proof (proj1 Hpreσ') as Hvis_map.
  pose proof (proj2 Hpreσ') as Hsid_map.
  (* Apply dfs_scc_from_sim at (i = csr_lo u fr, e_set = ∅, σ'). *)
  set (lo := csr_lo u fr) in *.
  set (hi := csr_hi u fr) in *.
  assert (Hlo_eq : csr_lo u fr = lo) by reflexivity.
  assert (Hhi_eq : csr_hi u fr = hi) by reflexivity.
  assert (Hloi : (lo <= lo)%Z) by lia.
  assert (Hlohi : (0 <= hi - lo)%Z).
  { pose proof (Hlolohi u Hub) as Hlh. unfold lo, hi in *. lia. }
  set (n := Z.to_nat (hi - lo)).
  assert (Hfuel : Z.to_nat (hi - lo) = n) by reflexivity.
  (* Invariants at entry (i = lo, e_set = ∅): A/B vacuous (empty ranges / empty
     set), E trivial (e_set = ∅).  C/D from pre_dfs2 σ' + replace_Znth. *)
  assert (HA : forall (e: Z * Z), (fun _ => False) e ->
                exists k, (lo <= k < lo)%Z /\ e = (u, Znth k fc 0)).
  { intros e Hf. exfalso. exact Hf. }
  assert (HB : forall k, (lo <= k < lo)%Z -> ~ (fun _ => False) (u, Znth k fc 0) ->
                 visited2 σ' (Znth k fc 0)).
  { intros k [Hk1 Hk2] _. lia. }
  assert (HE : forall j, (lo <= j < hi)%Z -> ~ visited2 σ' (Znth j fc 0) ->
                 ~ (fun _ => False) (u, Znth j fc 0)).
  { intros j Hj Hnv Hf. exact Hf. }
  (* C: scc_id σ' u = scc_id σ' root, from pre_dfs2 + replace_Znth. *)
  (* Bounds for Znth_replace_eq/neq: u, root within Zlength sid / vis. *)
  assert (Husid : (0 <= u < Zlength sid)%Z) by (rewrite Hsidlen; exact Hub).
  assert (Hrsid : (0 <= root < Zlength sid)%Z) by (rewrite Hsidlen; exact Hroot).
  assert (Huvis : (0 <= u < Zlength vis)%Z) by (rewrite Hvislen; exact Hub).
  assert (HC : scc_id σ' u = scc_id σ' root).
  { (* scc_id σ' u = Z.to_nat (Znth u (replace_Znth u (Znth root sid 0) sid) 0)
       = Z.to_nat (Znth root sid 0).  (Znth_replace_eq.)
       scc_id σ' root = Z.to_nat (Znth root (replace_Znth u (Znth root sid 0) sid) 0).
       Case root = u: Znth u (...) = Znth root sid 0 (replace at root = u). Both equal.
       Case root ≠ u: Znth root (...) = Znth root sid 0 (replace at u ≠ root, no change). *)
    assert (Hsu : scc_id σ' u = Z.to_nat (Znth root sid 0)).
    { rewrite (Hsid_map u Hub).
      rewrite (Znth_replace_eq sid u (Znth root sid 0) 0 Husid). reflexivity. }
    assert (Hsr : scc_id σ' root = Z.to_nat (Znth root sid 0)).
    { rewrite (Hsid_map root Hroot).
      destruct (Z.eq_dec root u) as [Heq | Hneq].
      - subst root. rewrite (Znth_replace_eq sid u (Znth u sid 0) 0 Husid). reflexivity.
      - rewrite (Znth_replace_neq sid root u (Znth root sid 0) 0 Hrsid (proj1 Hub) Hneq).
        reflexivity. }
    rewrite Hsu. symmetry. exact Hsr. }
  (* D: visited2 σ' u, from pre_dfs2 + replace_Znth u 1 vis (Znth u ... = 1 ≠ 0). *)
  assert (HD : visited2 σ' u).
  { assert (Hvu : Znth u (replace_Znth u 1 vis) 0 = 1).
    { rewrite (Znth_replace_eq vis u 1 0 Huvis). reflexivity. }
    apply (proj2 (Hvis_map u Hub)). rewrite Hvu. lia. }
  (* Apply sim. *)
  assert (Hsafe_ih : safe σ' (dfs_scc_from g fc fr root u lo) X).
  { eapply dfs_scc_from_sim; [ exact Hlo_eq | exact Hhi_eq | exact Hwf' | exact Hfaith |
                               exact Hub | exact Hfuel | exact Hloi | exact HA | exact HB |
                               exact HE | exact HC | exact HD | exact Hsafeσ' ]. }
  (* Wrap back to safeExec: exists σ', split. *)
  exists σ'. split; [ exact Hpreσ' | exact Hsafe_ih ].
Qed.

(* ===================================================================== *)
(* dfs1_entry_close infrastructure (phase-1 entry refinement).           *)
(*                                                                        *)
(* The entry VC (dfs1_entail_wit_1, second disjunct) reduces to: given    *)
(*   safeExec (pre_dfs1 vis1 fin timer_v) (dfs_finish g u) X,             *)
(* show safeExec (pre_dfs1 (replace_Znth u 1 vis1) fin timer_v)           *)
(*        (dfs_finish_from g radj_col radj_row u lo) X.                   *)
(*                                                                        *)
(* dfs_finish_repeat_body is the body of DFS_finish_f, u-parametrised,    *)
(* with W = dfs_finish g.  Note: step_aux g e v u (REVERSED — u is the   *)
(* target on the reverse graph), and the break branch does `assertS      *)
(* timer = finished-count;; get timer;; set_finish u t` (state-changing, unlike *)
(* phase-2's assertS sid ;; break).                                       *)
(* ===================================================================== *)

Definition dfs_finish_repeat_body (g: AdjGraph) (u: Z)
  : (Z * Z -> Prop) -> program KSt (CntOrBrk (Z * Z -> Prop) unit) :=
  fun e_set =>
    choice
      (e <- any (Z * Z);;
       v <- any Z;;
       assume (fun (_ : KSt) => ~ e ∈ e_set);;
       assume (fun st => ~ visited1 st v);;
       assume (fun (_ : KSt) => step_aux g e v u);;
       pre <- get (fun st pre => pre = st);;
       dfs_finish g v;;
       assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                              visited1 st v /\ visited1 pre ⊆ visited1 st);;
       continue (e_set ∪ Sets.singleton e))
      (assume (fun st =>
                 forall (e: Z * Z) (v: Z),
                   step_aux g e v u ->
                   e ∈ e_set \/ visited1 st v);;
       assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
       assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));;
       t <- get (fun st t => t = timer st);;
       set_finish u t;;
       break tt).

Lemma dfs_finish_unfold_repeat :
  forall (g: AdjGraph) (u: Z),
  gvalid g ->
  dfs_finish g u
  ==
  visit1 u ;; repeat_break (dfs_finish_repeat_body g u) ∅.
Proof.
  intros g u Hg.
  rewrite (dfs_finish_unfold g u Hg).
  unfold DFS_finish_f.
  reflexivity.
Qed.

(* visit1_pre_dfs1_step: peel the visit1 u prelude off safeExec(dfs_finish g u).
   visit1 u adds u to visited1 (visited1 st2 == visited1 st1 ∪ {u}), all other
   fields unchanged.  So pre_dfs1 vis1 fin timer_v -@ visit1 u -⥅
   pre_dfs1 (replace_Znth u 1 vis1) fin timer_v. *)
Lemma visit1_pre_dfs1_step :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z) (timer_v u: Z),
    (Zlength vis1 = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v -@ visit1 u -⥅
      (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1) fin_l timer_v) ♯ tt.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v u Hvlen Hub st0 Hpre.
  destruct Hpre as [Hpv [Hpf [Hpt [Hvi Hfi]]]].
  assert (HLu : (0 <= u < Zlength vis1)%Z) by (rewrite Hvlen; exact Hub).
  pose (st1 := MkSt (timer st0) (finish st0)
                     (fun w => visited1 st0 w \/ w = u)
                     (visited2 st0) (scc_id st0) (scc_next st0)).
  assert (Hnrm : (visit1 u).(MonadErr.nrm) st0 tt st1).
  { unfold visit1. simpl. split.
    - (* visited1 st1 == visited1 st0 ∪ {u} *)
      unfold st1. simpl. sets_unfold. intros w. split; intros Hw.
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
      + destruct Hw as [Hw | Hw]; [ left; exact Hw | subst w; right; reflexivity ].
    - unfold st1. simpl. repeat split; reflexivity.
  }
  exists st1. split; [ exact Hnrm | ].
  unfold pre_dfs1. split.
  - intros w Hw. assert (HLw : (0 <= w < Zlength vis1)%Z) by (rewrite Hvlen; exact Hw).
    unfold st1. simpl. split; intros Hvis.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. rewrite (Znth_replace_eq vis1 u 1 0 HLu). lia.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis1 w u 1 0 HLw (proj1 HLu) E).
        destruct Hvis as [Hv | Hwu].
        -- apply (proj1 (Hpv w Hw)). exact Hv.
        -- exfalso. apply E. exact Hwu.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. right. reflexivity.
      * apply Z.eqb_neq in E. rewrite (Znth_replace_neq vis1 w u 1 0 HLw (proj1 HLu) E) in Hvis.
        left. apply (proj2 (Hpv w Hw)). exact Hvis.
  - split.
    + intros w Hw. unfold st1. simpl. exact (Hpf w Hw).
    + split.
      * unfold st1. simpl. exact Hpt.
      * split.
        -- intros w Hinvalid Hvis.
           unfold st1 in Hvis. simpl in Hvis.
           destruct Hvis as [Hvis | Heq].
           ++ exact (Hvi w Hinvalid Hvis).
           ++ subst w. contradiction.
        -- intros w Hinvalid.
           unfold st1. simpl. exact (Hfi w Hinvalid).
Qed.

(* dfs1_visit_decompose: peel visit1 u prelude, landing safeExec over
   repeat_break (dfs_finish_repeat_body g u) ∅ at the post-visit1 state. *)
Lemma dfs1_visit_decompose :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z) (timer_v u: Z)
         (X: unit -> KSt -> Prop),
    gvalid g ->
    (Zlength vis1 = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v) (dfs_finish g u) X ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1) fin_l timer_v)
             (repeat_break (dfs_finish_repeat_body g u) ∅) X.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v u X Hg Hvlen Hub Hsafe.
  rewrite (dfs_finish_unfold_repeat g u Hg) in Hsafe.
  apply (highstepbind_derive (visit1 u)
            (fun _ => repeat_break (dfs_finish_repeat_body g u) ∅)
            (pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v) tt
            (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1) fin_l timer_v)
            (visit1_pre_dfs1_step g radj_col_l radj_row_l vis1 fin_l timer_v u Hvlen Hub)) in Hsafe.
  exact Hsafe.
Qed.

(* ===================================================================== *)
(* Reverse-direction err-imps for dfs_finish_iter / dfs_finish_from       *)
(* (phase-1 analogues of dfs_scc_iter/from_*_err_rev_imp).               *)
(* Used by dfs_finish_from_sim to peel the cursor step FORWARD (i -> i+1).*)
(* ===================================================================== *)

Lemma dfs_finish_iter_skip_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.err) st ->
    (dfs_finish_iter g radj_col_l u hi (i + 1) fuel).(MonadErr.err) st.
Proof.
  intros g radj_col_l u hi i fuel st Hilt Hvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc]. subst s0. exact Hsk2.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. exfalso. apply Hnc. exact Hvis.
Qed.

Lemma dfs_finish_iter_recurse_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l : list Z) (u hi i : Z) (fuel : nat)
         (st : KSt),
    (i < hi)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_iter g radj_col_l u hi i (S fuel)).(MonadErr.err) st ->
    (pre <- get (fun st pre => pre = st);;
     _ <- dfs_finish g (Znth i radj_col_l 0) ;;
     assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                            visited1 st (Znth i radj_col_l 0) /\
                            visited1 pre ⊆ visited1 st);;
      dfs_finish_iter g radj_col_l u hi (i + 1) fuel).(MonadErr.err) st.
Proof.
  intros g radj_col_l u hi i fuel st Hilt Hnvis Herr.
  simpl in Herr. destruct (Z.leb hi i) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - unfold if_else, choice in Herr.
    sets_unfold in Herr.
    destruct Herr as [HL | HR].
    + apply bind_err_iff in HL.
      destruct HL as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hc].
        exfalso. apply Hnvis. exact Hc.
    + apply bind_err_iff in HR.
      destruct HR as [Htest | [x [s0 [Hnm Hsk2]]]].
      * exfalso. unfold test in Htest. sets_unfold in Htest. exact Htest.
      * unfold test in Hnm. simpl in Hnm. destruct Hnm as [Hs2eq Hnc]. subst s0. exact Hsk2.
Qed.

Lemma dfs_finish_from_skip_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st ->
    (dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i = (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_finish_iter_skip_err_rev_imp g radj_col_l u _ i _ st Hilt Hvis Herr).
Qed.

Lemma dfs_finish_from_recurse_err_rev_imp :
  forall (g : AdjGraph) (radj_col_l radj_row_l : list Z) (u i : Z)
         (st : KSt),
    (i < csr_hi u radj_row_l)%Z ->
    ~ visited1 st (Znth i radj_col_l 0) ->
    (dfs_finish_from g radj_col_l radj_row_l u i).(MonadErr.err) st ->
    (pre <- get (fun st pre => pre = st);;
     _ <- dfs_finish g (Znth i radj_col_l 0) ;;
     assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st /\
                            visited1 st (Znth i radj_col_l 0) /\
                            visited1 pre ⊆ visited1 st);;
      dfs_finish_from g radj_col_l radj_row_l u (i + 1)).(MonadErr.err) st.
Proof.
  intros g radj_col_l radj_row_l u i st Hilt Hnvis Herr.
  unfold dfs_finish_from in *.
  assert (Hfuel : Z.to_nat (csr_hi u radj_row_l - i) =
                  S (Z.to_nat (csr_hi u radj_row_l - (i + 1)))).
  { assert (Hsub : csr_hi u radj_row_l - i = (csr_hi u radj_row_l - (i + 1)) + 1) by lia.
    rewrite Hsub, Z2Nat.inj_add by lia.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hfuel in Herr.
  exact (dfs_finish_iter_recurse_err_rev_imp g radj_col_l u _ i _ st Hilt Hnvis Herr).
Qed.

(* dfs_finish_repeat_body_err_from_assertS: if the break-branch closure holds
   at σ and the DFS-finish invariant assertion is false, then the repeat_break
   body errs at σ.  Used by dfs_finish_from_sim BASE to extract the asserted
   invariant from the no-err conjunct of safe σ (repeat_break B e_set) X. *)
Lemma dfs_finish_repeat_body_err_from_assertS :
  forall (g: AdjGraph) (u: Z) (e_set: Z * Z -> Prop) (σ: KSt),
    (forall (e: Z * Z) (v: Z), step_aux g e v u -> e ∈ e_set \/ visited1 σ v) ->
    ~ @DFSFinishInv AdjGraph Z (Z * Z) KG g σ ->
    (dfs_finish_repeat_body g u e_set).(MonadErr.err) σ.
Proof.
  intros g u e_set σ Hclosure Hnotinv.
  unfold dfs_finish_repeat_body, choice. sets_unfold.
  right.
  apply bind_err_iff. right.
  eexists tt. eexists σ. split.
  - unfold test. sets_unfold. split; [ reflexivity | exact Hclosure ].
  - apply bind_err_iff. left. exact Hnotinv.
Qed.

Lemma dfs_finish_repeat_body_err_from_timer_assertS :
  forall (g: AdjGraph) (u: Z) (e_set: Z * Z -> Prop) (σ: KSt),
    (forall (e: Z * Z) (v: Z), step_aux g e v u -> e ∈ e_set \/ visited1 σ v) ->
    @DFSFinishInv AdjGraph Z (Z * Z) KG g σ ->
    timer σ <> @cardV AdjGraph Z (Z * Z) KG g (fun v => finish σ v <> 0%nat) ->
    (dfs_finish_repeat_body g u e_set).(MonadErr.err) σ.
Proof.
  intros g u e_set σ Hclosure Hinv Hneq.
  unfold dfs_finish_repeat_body, choice. sets_unfold.
  right.
  apply bind_err_iff. right.
  eexists tt. eexists σ. split.
  - unfold test. sets_unfold. split; [ reflexivity | exact Hclosure ].
  - apply bind_err_iff. right.
    eexists tt. eexists σ. split.
    + split; [ reflexivity | exact Hinv ].
    + apply bind_err_iff. left. exact Hneq.
Qed.

(* ===================================================================== *)
(* dfs_finish_from_sim: cursor (dfs_finish_from) vs repeat_break          *)
(* simulation (phase-1 entry refinement core).                           *)
(*                                                                        *)
(* Differences from dfs_scc_from_sim (phase-2):                           *)
(* - csr1_faithful: step g v u <-> exists j in [lo u, hi u) with          *)
(*   Znth j radj_col 0 = v (REVERSE graph; u is the target).              *)
(* - break branch (R): assertS timer<=|V| ;; get timer ;; set_finish u t *)
(*   (state-CHANGING: timer++, finish[u]=t).  BASE case lands at sigma'   *)
(*   (= set_finish post-state), not sigma.                                *)
(* - the recursive branch now obtains DFSFinishInv, the recursive target  *)
(*   visit fact, and visited1 monotonicity from the monad-side assertS.   *)
(* - the break branch obtains DFSFinishInv and timer = finished-count     *)
(*   from the strengthened monad-side assertS before set_finish.          *)
(* ===================================================================== *)

Lemma dfs_finish_from_sim :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1_l fin_l: list Z) (u lo hi i: Z)
         (n: nat) (X: unit -> KSt -> Prop) (σ: KSt),
    let B := dfs_finish_repeat_body g u in
    csr_lo u radj_row_l = lo ->
    csr_hi u radj_row_l = hi ->
    csr_wf1 g radj_col_l radj_row_l vis1_l fin_l ->
    csr1_faithful g radj_col_l radj_row_l ->
    (0 <= u < adj_verts g)%Z ->
    Z.to_nat (hi - i) = n ->
    (lo <= i)%Z ->
    forall (e_set: Z * Z -> Prop),
      (forall (e: Z * Z), e_set e ->
         exists k, (lo <= k < i)%Z /\ e = (Znth k radj_col_l 0, u)) ->
      (forall k, (lo <= k < i)%Z -> ~ e_set (Znth k radj_col_l 0, u) ->
         visited1 σ (Znth k radj_col_l 0)) ->
      (forall j, (lo <= j < hi)%Z -> ~ visited1 σ (Znth j radj_col_l 0) ->
         ~ e_set (Znth j radj_col_l 0, u)) ->
      visited1 σ u ->
      safe σ (repeat_break B e_set) X ->
      safe σ (dfs_finish_from g radj_col_l radj_row_l u i) X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l u lo hi i n X σ B Hlo Heqhi Hwf Hfaith Hu Hfuel Hloi
         e_set HA HB HE HD Hsafe.
  revert i X σ Hfuel Hloi e_set HA HB HE HD Hsafe.
  induction n as [|n' IHn].
  - (* BASE: Z.to_nat (hi - i) = 0, hence i >= hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HD Hsafe.
    assert (Hge : (hi <= i)%Z).
    { destruct (Z.le_gt_cases hi i) as [Hle | Hgt]; [ exact Hle | ].
      exfalso.
      assert (Hpos : (0 < hi - i)%Z) by lia.
      destruct (Z.eq_dec (hi - i) 0) as [Heq | Hneq].
      - subst. lia.
      - assert (Hn0 : (Z.to_nat (hi - i) <> 0)%nat).
        { intro Hz. assert (0 <= hi - i)%Z by lia.
          pose proof (Z2Nat.id (hi - i) H) as Hid.
          rewrite Hz in Hid. lia. }
        rewrite Hfuel in Hn0. exfalso. apply Hn0. reflexivity. }
    assert (Hclosure : (forall (e: Z * Z) (v: Z), step_aux g e v u ->
                                    e ∈ e_set \/ visited1 σ v)).
    { intros e v Hstep.
      assert (Hstep_g : reachable_basic.step g v u) by (eapply step_trivial; eassumption).
      destruct Hstep as [Heq [Hvv [Hvu Hiny]]].
      subst e.
      pose proof (Hfaith u v Hu Hvv) as Hiff.
      apply (proj1 Hiff) in Hstep_g as [j [Hjlo Hjv]].
      destruct (classic (e_set (v, u))) as [Hin | Hnin].
      - left. exact Hin.
      - right. rewrite <- Hjv. apply (HB j). lia.
        rewrite Hjv. exact Hnin. }
	    assert (Hinvσ : @DFSFinishInv AdjGraph Z (Z * Z) KG g σ).
	    { destruct Hsafe as [Hnoerr _].
	      destruct (classic (@DFSFinishInv AdjGraph Z (Z * Z) KG g σ)) as [Hinv | Hnotinv].
	      - exact Hinv.
	      - exfalso. apply Hnoerr.
	        pose proof (repeat_break_unfold B) as Hunf.
	        unfold equiv in Hunf. simpl in Hunf.
	        unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
	        specialize (Hunf e_set) as [_ Herrpt].
	        sets_unfold in Herrpt. specialize (Herrpt σ) as [_ Hherr].
	        apply Hherr. apply bind_err_iff. left.
	        apply (dfs_finish_repeat_body_err_from_assertS g u e_set σ Hclosure Hnotinv). }
	    assert (Htimereq : timer σ = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish σ v <> 0%nat)).
	    { destruct Hsafe as [Hnoerr _].
	      destruct (Nat.eq_dec (timer σ)
	        (@cardV AdjGraph Z (Z * Z) KG g (fun v => finish σ v <> 0%nat))) as [Heq | Hneq].
      - exact Heq.
      - exfalso. apply Hnoerr.
        pose proof (repeat_break_unfold B) as Hunf.
        unfold equiv in Hunf. simpl in Hunf.
        unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
        specialize (Hunf e_set) as [_ Herrpt].
        sets_unfold in Herrpt. specialize (Herrpt σ) as [_ Hherr].
	        apply Hherr. apply bind_err_iff. left.
	        apply (dfs_finish_repeat_body_err_from_timer_assertS g u e_set σ Hclosure Hinvσ Hneq). }
    (* sigma' = set_finish post-state: timer sigma' = S (timer sigma),
       finish sigma' u = S (timer sigma), other fields unchanged. *)
    pose (σ' := MkSt (S (timer σ))
                     (fun w => if Z.eqb w u then S (timer σ) else finish σ w)
                     (visited1 σ) (visited2 σ)
                     (scc_id σ) (scc_next σ)).
    assert (Hfsu : finish σ' u = S (timer σ)).
    { unfold σ'. simpl. destruct (Z.eqb u u) eqn:Eu.
      - reflexivity.
      - apply Z.eqb_neq in Eu. exfalso. apply Eu. reflexivity. }
    assert (Hfsv : forall v, v <> u -> finish σ' v = finish σ v).
    { intros v Hvne. unfold σ'. simpl. destruct (Z.eqb v u) eqn:Ev.
      - apply Z.eqb_eq in Ev. exfalso. apply Hvne. exact Ev.
      - reflexivity. }
    assert (Htimer' : timer σ' = S (timer σ)) by (unfold σ'; reflexivity).
    assert (Hvis1' : visited1 σ' = visited1 σ) by (unfold σ'; reflexivity).
    assert (Hvis2' : visited2 σ' = visited2 σ) by (unfold σ'; reflexivity).
    assert (Hsid' : scc_id σ' = scc_id σ) by (unfold σ'; reflexivity).
    assert (Hsnext' : scc_next σ' = scc_next σ) by (unfold σ'; reflexivity).
    assert (Hbodystep : (B e_set).(MonadErr.nrm) σ (@by_break (Z*Z->Prop) unit tt) σ').
    { unfold B, dfs_finish_repeat_body.
      unfold choice. simpl.
      right.
      unfold_monad. simpl.
      eexists tt. eexists σ. split.
	      - split; [ reflexivity | exact Hclosure ].
	      - eexists tt. eexists σ. split.
	        + split; [ reflexivity | exact Hinvσ ].
	        + eexists tt. eexists σ. split.
	          * split; [ reflexivity | exact Htimereq ].
	          * eexists (timer σ). eexists σ. split.
	            -- split; [ reflexivity | reflexivity ].
	            -- eexists tt. eexists σ'. split.
	               ++ split; [ exact Htimer' | ].
	                  split; [ exact Hfsu | ].
	                  split; [ exact Hfsv | ].
	                  split; [ exact Hvis1' | ].
	                  split; [ exact Hvis2' | ].
	                  split; [ exact Hsid' | ].
	                  exact Hsnext'.
	               ++ simpl. split; [ reflexivity | reflexivity ]. }
    assert (Hrbstep : (repeat_break B e_set).(MonadErr.nrm) σ tt σ').
    { eapply repeat_break_break_step_gen. exact Hbodystep. }
    assert (Hxtt : X tt σ') by (eapply wp_spec; eassumption).
    unfold safe in *.
    assert (Hge' : (csr_hi u radj_row_l <= i)%Z) by (rewrite Heqhi; exact Hge).
	    pose proof (wp_progequiv (assertS (fun st => @DFSFinishInv AdjGraph Z (Z * Z) KG g st);;
	                              assertS (fun st => timer st = @cardV AdjGraph Z (Z * Z) KG g (fun v => finish st v <> 0%nat));;
	                              t <- get (fun st t => t = timer st) ;; set_finish u t)
                  (dfs_finish_from g radj_col_l radj_row_l u i) X
                  (dfs_finish_from_exit g radj_col_l radj_row_l u i Hge')) as Hwp.
    sets_unfold in Hwp.
    specialize (Hwp σ) as [Hfwd Hbwd].
    unfold weakestpre in *.
    sets_unfold in Hfwd.
    apply Hfwd.
    sets_unfold.
    split.
    + (* ~err for the asserted invariant branch; get/set_finish.err = ∅. *)
      intro Herr.
	      apply bind_err_iff in Herr.
	      destruct Herr as [Hassert | [a [s2 [Hassertnrm Hfin]]]].
	      * exfalso. apply Hassert. exact Hinvσ.
	      * exfalso. apply bind_err_iff in Hfin.
	        destruct Hfin as [Htimerassert | [a2 [s3 [Htimerassertnrm Hgetfin]]]].
	        -- destruct Hassertnrm as [Hs2 _]. subst s2.
	           apply Htimerassert. exact Htimereq.
	        -- apply bind_err_iff in Hgetfin.
	           destruct Hgetfin as [Hget | [t [s4 [Hgetstep Hfinerr]]]].
	           ++ exact Hget.
	           ++ exact Hfinerr.
	    + intros r σ'' Hexitstep.
	      apply bind_nrm_iff in Hexitstep.
	      destruct Hexitstep as [a [sm0 [Hassertnrm Hrest]]].
	      apply bind_nrm_iff in Hrest.
	      destruct Hrest as [a1 [sm [Htimerassertnrm Hgetsetfin]]].
	      apply bind_nrm_iff in Hgetsetfin.
	      destruct Hgetsetfin as [t [s2 [Hgetstep Hfinstep]]].
      destruct Hgetstep as [HgetP HgetEq].
      (* get keeps state: s2 = sm (HgetEq : sm = s2); bound t = timer sm *)
      subst s2. subst t.
      (* assertS keeps state: sm = σ *)
	      assert (Hsm0σ : sm0 = σ).
	      { destruct Hassertnrm as [Heq _]. symmetry. exact Heq. }
	      subst sm0.
	      assert (Hsmσ : sm = σ).
	      { destruct Htimerassertnrm as [Heq _]. symmetry. exact Heq. }
      subst sm.
      (* set_finish u (timer σ): σ'' = σ' by field equality *)
      assert (Heqσ'' : σ'' = σ').
      { destruct σ'' as [tm fm v1m v2m sm snm] eqn:Eσ''.
        cbv beta iota delta [set_finish custom MonadErr.nrm_nrm] in Hfinstep.
        destruct Hfinstep as [Ht [Hfu [Hfv [Hv1 [Hv2 [Hs Hsn]]]]]].
        unfold σ'.
        f_equal.
        - exact Ht.
        - extensionality w. destruct (Z.eqb w u) eqn:E.
          + apply Z.eqb_eq in E. subst w. exact Hfu.
          + apply Z.eqb_neq in E. exact (Hfv w E).
        - exact Hv1.
        - exact Hv2.
        - exact Hs.
        - exact Hsn. }
      subst σ''. destruct r. exact Hxtt.
  - (* STEP: hi - i = S n', i.e. lo <= i < hi *)
    intros i X σ Hfuel Hloi e_set HA HB HE HD Hsafe.
    assert (Hilt : (i < hi)%Z).
    { assert (Hnonneg : (0 <= hi - i)%Z).
      { destruct (Z.le_gt_cases hi i) as [Hle | Hgt].
        - exfalso. assert (Heqz : hi - i = 0) by lia.
          rewrite Heqz in Hfuel. simpl in Hfuel. discriminate.
        - lia. }
      lia. }
    assert (Hilt' : (i < csr_hi u radj_row_l)%Z) by (rewrite Heqhi; exact Hilt).
    set (v := Znth i radj_col_l 0) in *.
    destruct (classic (visited1 σ v)) as [Hvisv | Hnvisv].
    + (* SKIP: visited1 σ v *)
      assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
      { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
        assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
        rewrite Hsub in Hfuel.
        rewrite Z2Nat.inj_add in Hfuel by lia.
        rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
      assert (Hloi' : (lo <= i + 1)%Z) by lia.
      assert (HA' : forall (e: Z * Z), e_set e ->
                     exists k, (lo <= k < i + 1)%Z /\ e = (Znth k radj_col_l 0, u)).
      { intros e He. destruct (HA e He) as [k [Hk Heq]]. exists k. split; [ lia | exact Heq ]. }
      assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set (Znth k radj_col_l 0, u) ->
                     visited1 σ (Znth k radj_col_l 0)).
      { intros k Hk Hne.
        destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
        - apply (HB k); [ lia | exact Hne ].
        - assert (Hki : k = i) by lia. subst k. exact Hvisv. }
      assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited1 σ (Znth j radj_col_l 0) ->
                     ~ e_set (Znth j radj_col_l 0, u)).
      { exact HE. }
      assert (Hsafe_ih : safe σ (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X).
      { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
                      exact HD | exact Hsafe ]. }
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * intro Herr.
        destruct Hsafe_ih as [Hnoerr _].
        exfalso. apply Hnoerr.
        apply (dfs_finish_from_skip_err_rev_imp g radj_col_l radj_row_l u i σ Hilt' Hvisv).
        exact Herr.
      * intros a s' Hstep.
        destruct Hsafe_ih as [_ Hpost].
        apply Hpost.
        apply (proj1 (dfs_finish_from_skip_step g radj_col_l radj_row_l u i σ a s' Hilt' Hvisv)).
        exact Hstep.
    + (* RECURSE: ~visited1 σ v *)
      assert (Hagvalid : gvalid g) by (destruct Hwf as [Hgv _]; exact Hgv).
      assert (Hvbound : (0 <= v < adj_verts g)%Z).
      { pose proof Hwf as [Hgv0 [Hlenfr [Hlenvis [Hlenfin [Hmof [Hlo0 [Hhilem [Hcolbound [Hlolohi Hmofbound]]]]]]]]].
        assert (Hhilem_u : (csr_hi u radj_row_l <= m_of radj_row_l)%Z) by (apply Hhilem; exact Hu).
        assert (Hlo0u : (0 <= csr_lo u radj_row_l)%Z) by (apply Hlo0; exact Hu).
        assert (Him : (0 <= i < m_of radj_row_l)%Z).
        { split; [ rewrite Hlo in Hlo0u; lia | lia ]. }
        exact (Hcolbound i Him). }
      assert (Hnotinv : ~ e_set (v, u)).
      { apply (HE i). split; [ exact Hloi | exact Hilt ]. exact Hnvisv. }
      assert (Hstep_g : reachable_basic.step g v u).
      { destruct (Hfaith u v Hu Hvbound) as [Hfwd Hbwd].
        apply Hbwd. exists i. split.
        - assert (Hloi' : (csr_lo u radj_row_l <= i)%Z). { rewrite Hlo. exact Hloi. }
          split; [ exact Hloi' | exact Hilt' ].
        - reflexivity. }
      assert (Hstepeq : step_aux g (v, u) v u).
      { destruct Hstep_g as [e Heq].
        destruct Heq as [Heqrefl [Hxv [Hyu Hiny]]].
        simpl in *. subst e. split; [ reflexivity | split; [ exact Hvbound | split;
          [ exact Hu | exact Hiny ] ] ]. }
      set (e_set' := e_set ∪ Sets.singleton (v, u)).
      unfold safe in *.
      unfold weakestpre in *.
      split.
      * (* ~err (dfs_finish_from ... u i) σ *)
        assert (HnoerrBE : ~ (B e_set).(MonadErr.err) σ).
        { assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                   (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                   (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          pose proof Hsafe as Hsafe0. apply Hwpb in Hsafe0.
          sets_unfold in Hsafe0. destruct Hsafe0 as [HnoerrBind _].
          apply bind_noerr_iff in HnoerrBind. destruct HnoerrBind as [Hne _]. exact Hne. }
        intro Herr.
        apply (dfs_finish_from_recurse_err_rev_imp g radj_col_l radj_row_l u i σ Hilt' Hnvisv) in Herr.
        apply bind_err_iff in Herr.
        destruct Herr as [Hgeterr | [pre0 [sget [Hgetnrm Hresterr]]]].
        { exfalso. exact Hgeterr. }
        destruct Hgetnrm as [Hpre0 Hsget]. subst pre0. subst sget.
        apply bind_err_iff in Hresterr.
        destruct Hresterr as [Herrv | [ha [smid [Hnm Hassert_cont_err]]]].
        -- (* dfs_finish g v errs at σ: contradiction with ~err (B e_set) σ. *)
           exfalso. apply HnoerrBE.
           unfold B, dfs_finish_repeat_body, choice. sets_unfold. left.
           apply bind_err_iff. right.
           eexists (v, u). eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists v. eexists σ. split.
           { reflexivity. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnotinv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hnvisv ]. }
           apply bind_err_iff. right.
           eexists tt. eexists σ. split.
           { split; [ reflexivity | exact Hstepeq ]. }
           apply bind_err_iff. right.
           eexists σ. eexists σ. split.
           { split; [ reflexivity | reflexivity ]. }
           apply bind_err_iff. left. exact Herrv.
        -- apply bind_err_iff in Hassert_cont_err.
           destruct Hassert_cont_err as [Hasserterr | [ha2 [sassert [Hassertnrm Hsccerr]]]].
           ++ (* post-recursion assertion fails: contradiction with ~err (B e_set) σ. *)
              exfalso. apply HnoerrBE.
              unfold B, dfs_finish_repeat_body, choice. sets_unfold. left.
              apply bind_err_iff. right.
              eexists (v, u). eexists σ. split.
              { reflexivity. }
              apply bind_err_iff. right.
              eexists v. eexists σ. split.
              { reflexivity. }
              apply bind_err_iff. right.
              eexists tt. eexists σ. split.
              { split; [ reflexivity | exact Hnotinv ]. }
              apply bind_err_iff. right.
              eexists tt. eexists σ. split.
              { split; [ reflexivity | exact Hnvisv ]. }
              apply bind_err_iff. right.
              eexists tt. eexists σ. split.
              { split; [ reflexivity | exact Hstepeq ]. }
              apply bind_err_iff. right.
              eexists σ. eexists σ. split.
              { split; [ reflexivity | reflexivity ]. }
              apply bind_err_iff. right.
              eexists ha. eexists smid. split.
              { exact Hnm. }
              apply bind_err_iff. left. exact Hasserterr.
           ++ destruct Hassertnrm as [Hsassert [Hinv_smid [Hvis_self_smid Hvis_mono_smid]]].
              subst sassert.
              (* dfs_finish_from (i+1) errs at smid *)
           assert (Hbodycont_smid :
                     (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') smid).
           { unfold B, dfs_finish_repeat_body, choice. simpl.
             left. simpl.
             eexists (v, u). eexists σ. split.
             - reflexivity.
             - eexists v. eexists σ. split.
               + reflexivity.
               + eexists tt. eexists σ. split.
                 * split; [ reflexivity | exact Hnotinv ].
                 * eexists tt. eexists σ. split.
                   -- split; [ reflexivity | exact Hnvisv ].
                   -- eexists tt. eexists σ. split.
                      ++ split; [ reflexivity | exact Hstepeq ].
                      ++ eexists σ. eexists σ. split.
                         ** simpl. split; [ reflexivity | reflexivity ].
                         ** eexists ha. eexists smid. split.
                            --- exact Hnm.
                            --- eexists ha2. eexists smid. split.
                                +++ simpl. split; [ reflexivity | split; [ exact Hinv_smid | split; [ exact Hvis_self_smid | exact Hvis_mono_smid ] ] ].
                                +++ simpl. split; [ reflexivity | reflexivity ]. }
           assert (Hsafe_smid : safe smid (repeat_break B e_set') X).
           { unfold safe in *.
             unfold weakestpre in *.
             assert (Hunf : @equiv (program KSt unit) _
                           (repeat_break B e_set)
                           (x <- B e_set ;;
                            match x with
                            | by_continue a' => repeat_break B a'
                            | by_break b' => ret b'
                            end)).
             { pose proof (repeat_break_unfold B) as Hu2.
               unfold equiv in Hu2. simpl in Hu2.
               unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
               specialize (Hu2 e_set) as [Hn Hh].
               constructor; assumption. }
             pose proof (wp_progequiv
                           (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                           (repeat_break B e_set) X Hunf) as Hwp.
             sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
             unfold weakestpre in Hwpb. sets_unfold in Hwpb.
             apply Hwpb in Hsafe.
             sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
             apply bind_noerr_iff in HnoerrBind.
             destruct HnoerrBind as [HnoerrBEset HpostBEset].
             split.
             - intro Herr'.
               assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
                                    | by_continue a' => repeat_break B a'
                                    | by_break b' => ret b' end).(MonadErr.err) smid).
               { simpl. exact Herr'. }
               apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') smid Hbodycont_smid) in Herrmatch.
               exact Herrmatch.
             - intros r0 σf Hrb.
               apply HpostBind.
               assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
               { unfold MonadErr.bind. simpl.
                 eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists smid. split.
                 - exact Hbodycont_smid.
                 - simpl. exact Hrb. }
               exact HnrmMatch. }
           assert (Huneqv : u <> v).
           { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
	           assert (Hcardtimer_smid : (count_pred (visited1 smid) (bijective_listV g) >= timer smid)%nat).
	           { exact (DFSFinishInv_card_timer g smid Hinv_smid). }
           assert (HA'_smid : forall (e: Z * Z), e_set' e ->
                               exists k, (lo <= k < i + 1)%Z /\ e = (Znth k radj_col_l 0, u)).
           { intros e He. sets_unfold in He. destruct He as [He | Heuv].
             - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
             - exists i. split.
               + split; [ exact Hloi | lia ].
               + symmetry. exact Heuv. }
           assert (HB'_smid : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (Znth k radj_col_l 0, u) ->
                               visited1 smid (Znth k radj_col_l 0)).
           { intros k Hk Hne.
             destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
             - assert (HkZnth_neq_v : Znth k radj_col_l 0 <> v).
               { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
               assert (Hne_eset : ~ e_set (Znth k radj_col_l 0, u)).
               { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
               assert (Hklt : (lo <= k < i)%Z) by lia.
               apply Hvis_mono_smid. apply (HB k Hklt Hne_eset).
             - assert (Hki : k = i) by lia. subst k.
               exfalso. apply Hne. sets_unfold. right. reflexivity. }
           assert (HE'_smid : forall j, (lo <= j < hi)%Z -> ~ visited1 smid (Znth j radj_col_l 0) ->
                               ~ e_set' (Znth j radj_col_l 0, u)).
           { intros j Hj Hnvisj.
             destruct (Z.eq_dec (Znth j radj_col_l 0) v) as [Heq | Hneq].
             - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_self_smid).
             - intro Hin. apply Hneq.
               sets_unfold in Hin. destruct Hin as [HinE | Hsin].
               + assert (Hnvis_orig : ~ visited1 σ (Znth j radj_col_l 0)).
                 { intro Hv. apply Hnvisj. apply Hvis_mono_smid. exact Hv. }
                 exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
               + injection Hsin as Heqv. exact (eq_sym Heqv). }
           assert (HD'_smid : visited1 smid u).
           { apply Hvis_mono_smid. exact HD. }
           assert (Hloi_smid : (lo <= i + 1)%Z) by lia.
           assert (Hfuel_smid : Z.to_nat (hi - (i + 1)) = n').
           { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
             assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
             rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
             rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
           assert (Hsafe_ih_smid : safe smid (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X).
           { eapply IHn; [ exact Hfuel_smid | exact Hloi_smid | exact HA'_smid | exact HB'_smid |
                           exact HE'_smid | exact HD'_smid | exact Hsafe_smid ]. }
           destruct Hsafe_ih_smid as [Hnoerr_smid _].
           exfalso. apply Hnoerr_smid. exact Hsccerr.
      * (* forall r σ', nrm (dfs_finish_from ... u i) σ r σ' -> X r σ' *)
	        intros r σ' Hstep.
	        apply (proj1 (dfs_finish_from_recurse_step g radj_col_l radj_row_l u i σ r σ' Hilt' Hnvisv)) in Hstep.
	        apply bind_nrm_iff in Hstep.
	        destruct Hstep as [pre0 [sget [Hgetnrm Hrestnrm]]].
	        destruct Hgetnrm as [Hpre0 Hsget]. subst pre0. subst sget.
	        apply bind_nrm_iff in Hrestnrm.
	        destruct Hrestnrm as [hu [smid [Hdfsstep Hassert_cont_nrm]]].
	        apply bind_nrm_iff in Hassert_cont_nrm.
	        destruct Hassert_cont_nrm as [ha2 [sassert [Hassertnrm Hcontstep]]].
	        destruct Hassertnrm as [Hsassert [Hinv_smid [Hvis_v_self Hvis_mono]]].
	        subst sassert.
	        assert (Hbodycont : (B e_set).(MonadErr.nrm) σ (@by_continue (Z*Z->Prop) unit e_set') smid).
	        { unfold B, dfs_finish_repeat_body, choice. simpl.
	          left. simpl.
	          eexists (v, u). eexists σ. split.
          - reflexivity.
          - eexists v. eexists σ. split.
            + reflexivity.
            + eexists tt. eexists σ. split.
              * split; [ reflexivity | exact Hnotinv ].
              * eexists tt. eexists σ. split.
                -- split; [ reflexivity | exact Hnvisv ].
	                -- eexists tt. eexists σ. split.
	                   ++ split; [ reflexivity | exact Hstepeq ].
	                   ++ eexists σ. eexists σ. split.
	                      ** simpl. split; [ reflexivity | reflexivity ].
	                      ** eexists hu. eexists smid. split.
	                         --- exact Hdfsstep.
	                         --- eexists ha2. eexists smid. split.
	                             +++ simpl. split; [ reflexivity | split; [ exact Hinv_smid | split; [ exact Hvis_v_self | exact Hvis_mono ] ] ].
	                             +++ simpl. split; [ reflexivity | reflexivity ]. }
	        assert (Hsafe'' : safe smid (repeat_break B e_set') X).
	        { unfold safe in *.
	          unfold weakestpre in *.
          assert (Hunf : @equiv (program KSt unit) _
                        (repeat_break B e_set)
                        (x <- B e_set ;;
                         match x with
                         | by_continue a' => repeat_break B a'
                         | by_break b' => ret b'
                         end)).
          { pose proof (repeat_break_unfold B) as Hu2.
            unfold equiv in Hu2. simpl in Hu2.
            unfold Equiv_lift, LiftConstructors.lift_rel2 in Hu2.
            specialize (Hu2 e_set) as [Hn Hh].
            constructor; assumption. }
          pose proof (wp_progequiv
                        (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end)
                        (repeat_break B e_set) X Hunf) as Hwp.
          sets_unfold in Hwp. specialize (Hwp σ) as [_ Hwpb].
          unfold weakestpre in Hwpb. sets_unfold in Hwpb.
          apply Hwpb in Hsafe.
          sets_unfold in Hsafe. destruct Hsafe as [HnoerrBind HpostBind].
          apply bind_noerr_iff in HnoerrBind.
          destruct HnoerrBind as [HnoerrBEset HpostBEset].
          split.
          - intro Herr'.
	            assert (Herrmatch : (match (@by_continue (Z*Z->Prop) unit e_set') with
	                                 | by_continue a' => repeat_break B a'
	                                 | by_break b' => ret b' end).(MonadErr.err) smid).
	            { simpl. exact Herr'. }
	            apply (HpostBEset (@by_continue (Z*Z->Prop) unit e_set') smid Hbodycont) in Herrmatch.
	            exact Herrmatch.
          - intros r0 σf Hrb.
            apply HpostBind.
            assert (HnrmMatch : (x <- B e_set ;; match x with by_continue a' => repeat_break B a' | by_break b' => ret b' end).(MonadErr.nrm) σ r0 σf).
            { unfold MonadErr.bind. simpl.
	              eexists (@by_continue (Z*Z->Prop) unit e_set'). eexists smid. split.
	              - exact Hbodycont.
	              - simpl. exact Hrb. }
	            exact HnrmMatch. }
        assert (Hfuel' : Z.to_nat (hi - (i + 1)) = n').
        { assert (Hsub : hi - i = (hi - (i + 1)) + 1) by lia.
          assert (Hnonneg1 : (0 <= hi - (i + 1))%Z) by lia.
          rewrite Hsub in Hfuel. rewrite Z2Nat.inj_add in Hfuel by lia.
          rewrite Nat.add_1_r in Hfuel. injection Hfuel. auto. }
        assert (Hloi' : (lo <= i + 1)%Z) by lia.
        assert (HA' : forall (e: Z * Z), e_set' e ->
                       exists k, (lo <= k < i + 1)%Z /\ e = (Znth k radj_col_l 0, u)).
        { intros e He. sets_unfold in He. destruct He as [He | Heuv].
          - destruct (HA e He) as [k [Hk Hkeq]]. exists k. split; [ lia | exact Hkeq ].
          - exists i. split.
            + split; [ exact Hloi | lia ].
            + symmetry. exact Heuv. }
        assert (Huneqv : u <> v).
        { intro Heq. apply Hnvisv. rewrite <- Heq. exact HD. }
		        assert (Hcardtimer'' : (count_pred (visited1 smid) (bijective_listV g) >= timer smid)%nat).
		        { exact (DFSFinishInv_card_timer g smid Hinv_smid). }
        assert (HB' : forall k, (lo <= k < i + 1)%Z -> ~ e_set' (Znth k radj_col_l 0, u) ->
	                       visited1 smid (Znth k radj_col_l 0)).
        { intros k Hk Hne.
          destruct (Z.le_gt_cases k (i - 1)) as [Hle | Hgt].
          - assert (HkZnth_neq_v : Znth k radj_col_l 0 <> v).
            { intro Heq. apply Hne. rewrite Heq. sets_unfold. right. reflexivity. }
            assert (Hne_eset : ~ e_set (Znth k radj_col_l 0, u)).
            { intro Hin. apply Hne. sets_unfold. left. exact Hin. }
            pose proof (HB k) as Hkb.
            assert (Hklt : (lo <= k < i)%Z) by lia.
            specialize (Hkb Hklt Hne_eset).
            apply Hvis_mono. exact Hkb.
          - assert (Hki : k = i) by lia. subst k.
            exfalso. apply Hne. sets_unfold. right. reflexivity. }
	        assert (HE' : forall j, (lo <= j < hi)%Z -> ~ visited1 smid (Znth j radj_col_l 0) ->
                       ~ e_set' (Znth j radj_col_l 0, u)).
        { intros j Hj Hnvisj.
          destruct (Z.eq_dec (Znth j radj_col_l 0) v) as [Heq | Hneq].
          - exfalso. rewrite Heq in Hnvisj. exact (Hnvisj Hvis_v_self).
          - intro Hin. apply Hneq.
            sets_unfold in Hin. destruct Hin as [HinE | Hsin].
            + assert (Hnvis_orig : ~ visited1 σ (Znth j radj_col_l 0)).
              { intro Hv. apply Hnvisj. apply Hvis_mono. exact Hv. }
              exfalso. apply (HE j Hj Hnvis_orig). exact HinE.
            + injection Hsin as Heqv. exact (eq_sym Heqv). }
	        assert (HD' : visited1 smid u).
	        { apply Hvis_mono. exact HD. }
	        assert (Hsafe_ih : safe smid (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X).
	        { eapply IHn; [ exact Hfuel' | exact Hloi' | exact HA' | exact HB' | exact HE' |
	                        exact HD' | exact Hsafe'' ]. }
        apply Hsafe_ih. exact Hcontstep.
Qed.

(* ===================================================================== *)
(* dfs1_entry_close + count_pred-count_nonzero bridge.                    *)
(*                                                                        *)
(* dfs1_entry_close composes dfs1_visit_decompose (peel visit1 prelude)   *)
(* with dfs_finish_from_sim at (i = csr_lo u, e_set = empty).  The sim    *)
(* premises HcardV (count_pred(visited1 st)(bijective_listV g) >= timer)  *)
(* and Htimerbd (timer <= length(bijective_listV g)) are discharged from  *)
(* pre_dfs1 via the count_pred-count_nonzero bridge below:                *)
(*   bijective_listV g = listV g = [0,1,...,adj_verts g - 1] (NoDup+all    *)
(*     valid, so valid_NoDup_list retains all), and under pre_dfs1        *)
(*     (visited1 st v <-> Znth v vis1 0 <> 0 for 0<=v<n) the position-   *)
(*     aligned count equals count_nonzero vis1, hence >= Z.to_nat timer_v *)
(*     = timer st by PreH timer_v <= count_nonzero vis1.                  *)
(* ===================================================================== *)

(* valid_NoDup_list P l = l when l is NoDup and every element satisfies P:
   the de-dup filter keeps every element (none filtered, none duplicated). *)
Lemma valid_NoDup_list_all_retained :
  forall {A: Type} (P: A -> Prop) (l: list A),
    NoDup l ->
    (forall x, In x l -> P x) ->
    valid_NoDup_list P l = l.
Proof.
  intros A P l. induction l as [| a l IH]; intros HND Hall; simpl.
  - reflexivity.
  - inversion HND as [| ? l' HNDl Hnia]. subst l'.
    assert (Halll : forall v, In v l -> P v) by (intros v Hv; apply Hall; right; exact Hv).
    assert (HIH : valid_NoDup_list P l = l) by (apply IH; [ exact Hnia | exact Halll ]).
    destruct (excluded_middle_informative (P a /\ ~ In a (valid_NoDup_list P l))) as [Hret | Hbad].
    + destruct Hret as [Ha Hnotin]. rewrite HIH in Hnotin. rewrite HIH. reflexivity.
    + exfalso. apply Hbad. split.
      * apply Hall. left. reflexivity.
      * rewrite HIH. exact HNDl.
Qed.

(* For an AdjGraph with AdjGraphValid g, bijective_listV g is a permutation
   of the ordered vertex list [0, 1, ..., adj_verts g - 1] (= listV g):
   both are NoDup and have the same In-set (vvalid g v = 0<=v<adj_verts g),
   so NoDup_Permutation applies.  (A definitional equality is unavailable
   because the VListBijective instance is opaque.) *)
Lemma AdjGraph_bijective_listV_perm :
  forall (g: AdjGraph),
    AdjGraphValid g ->
    Permutation (bijective_listV g) (map Z.of_nat (seq 0 (Z.to_nat (adj_verts g)))).
Proof.
  intros g Hg.
  assert (Hgv : gvalid g) by exact Hg.
  assert (Hfwd : (Zlength (adj_fwd g) = adj_verts g)%Z) by (exact (proj1 (Hg))).
  assert (Hag : (0 <= adj_verts g)%Z) by (rewrite <- Hfwd; rewrite Zlength_correct; apply Nat2Z.is_nonneg).
  assert (HndB : NoDup (bijective_listV g)).
  { apply bijective_listV_NoDup. exact Hgv. }
  assert (HndS : NoDup (map Z.of_nat (seq 0 (Z.to_nat (adj_verts g))))).
  { apply NoDup_map_NoDup_ForallPairs.
    { intros x y _ _ Heq. apply Nat2Z.inj in Heq. exact Heq. }
    apply seq_NoDup. }
  assert (HinB : forall v, In v (bijective_listV g) <-> vvalid g v).
  { intros v. apply bijective_vertices. exact Hgv. }
  assert (HinS : forall v, In v (map Z.of_nat (seq 0 (Z.to_nat (adj_verts g)))) <-> vvalid g v).
  { intros v. split.
    - intros Hv. apply in_map_iff in Hv. destruct Hv as [k [Hk2 Hk1]].
      apply in_seq in Hk1. subst v. unfold vvalid, adj_vvalid. split; lia.
    - intros Hv. cbv [vvalid adj_vvalid] in Hv. destruct Hv as [Hv1 Hv2].
      apply in_map_iff. exists (Z.to_nat v). split.
      + apply Z2Nat.id. exact Hv1.
      + apply (proj2 (in_seq _ _ _)).
        assert (Hvv : Z.of_nat (Z.to_nat v) = v) by (apply Z2Nat.id; exact Hv1).
        assert (Hag' : Z.of_nat (Z.to_nat (adj_verts g)) = adj_verts g)
          by (apply Z2Nat.id; exact Hag).
        split.
        * apply Nat.le_0_l.
        * rewrite Nat.add_0_l.
          apply (proj2 (Nat2Z.inj_lt (Z.to_nat v) (Z.to_nat (adj_verts g)))).
          rewrite Hvv, Hag'. exact Hv2. }
  apply NoDup_Permutation.
  - exact HndB.
  - exact HndS.
  - intros x. rewrite HinB, HinS. reflexivity.
Qed.

(* count_pred is invariant under Permutation (the count depends only on the
   multiset of elements, not their order). *)
Lemma count_pred_perm :
  forall {A: Type} (P: A -> Prop) (l l': list A),
    Permutation l l' -> count_pred P l = count_pred P l'.
Proof.
  intros A P l l' Hp.
  induction Hp as [| x l l' Hp IHp | x y l | l l' l'' Hp1 IHp1 Hp2 IHp2].
  - reflexivity.
  - simpl. destruct (excluded_middle_informative (P x)); [ f_equal; exact IHp | exact IHp ].
  - simpl.
    destruct (excluded_middle_informative (P y)) eqn:Ey;
    destruct (excluded_middle_informative (P x)) eqn:Ex; reflexivity.
  - simpl. transitivity (count_pred P l'); [ exact IHp1 | exact IHp2 ].
Qed.

(* Position-aligned count: count_pred P over [offset, offset+1, ..., offset+n-1]
   (encoded as map (fun k => offset + Z.of_nat k) (seq 0 n)) aligns positionally
   with Znth over vis1 when Zlength vis1 = Z.of_nat n and P (offset + Z.of_nat k)
   <-> Znth k vis1 0 <> 0 for 0 <= k < n.  Then the count equals
   Z.to_nat (count_nonzero vis1).  Proved by induction on n with a shifted
   offset so the tail premise closes under IH. *)
Lemma count_pred_seq_aligned :
  forall (P: Z -> Prop) (vis1: list Z) (n: nat) (offset: Z),
    Zlength vis1 = Z.of_nat n ->
    (forall k, (0 <= k < Z.of_nat n)%Z ->
                 P (offset + k) <-> Znth k vis1 0 <> 0%Z) ->
    count_pred P (map (fun k => offset + Z.of_nat k) (seq 0 n)) =
    Z.to_nat (count_nonzero vis1).
Proof.
  intros P vis1 n. revert vis1 P.
  induction n as [| n IH ]; intros vis1 P offset Hvlen Halign.
  - destruct vis1 as [| z vs].
    + reflexivity.
    + exfalso. assert (Hc : Zlength (z :: vs) = Z.succ (Zlength vs)) by apply Zlength_cons.
      assert (Hge : (0 <= Zlength vs)%Z) by (rewrite (Zlength_correct vs); apply Nat2Z.is_nonneg).
      rewrite Hc in Hvlen. lia.
  - destruct vis1 as [| z vis1'].
    + rewrite Zlength_correct in Hvlen. simpl in Hvlen. destruct n; [ lia | exfalso; lia ].
    + simpl count_nonzero.
      assert (Hmap_seq1 : map (fun k => offset + Z.of_nat k) (seq 1 n)
                                  = map (fun k => offset + Z.of_nat (S k)) (seq 0 n)).
      { rewrite <- seq_shift. rewrite map_map. reflexivity. }
      assert (Hhead : P offset <-> z <> 0%Z).
      { assert (Heq0 : offset + 0%Z = offset) by lia.
        assert (Hz : Znth 0 (z :: vis1') 0 = z) by (rewrite Znth0_cons; reflexivity).
        rewrite <- Heq0. rewrite <- Hz. apply (Halign 0%Z). lia. }
      assert (Htail_align : forall k, (0 <= k < Z.of_nat n)%Z ->
                              P ((offset + 1) + k) <-> Znth k vis1' 0 <> 0%Z).
      { intros k Hk.
        replace ((offset + 1) + k) with (offset + (k + 1)) by lia.
        replace (Znth k vis1' 0) with (Znth (k + 1) (z :: vis1') 0).
        - apply Halign. lia.
        - rewrite Znth_cons by lia.
          replace (k + 1 - 1) with k by lia. reflexivity. }
      assert (Hlen' : Zlength vis1' = Z.of_nat n).
      { assert (Hc : Zlength (z :: vis1') = Z.succ (Zlength vis1')) by apply Zlength_cons.
        rewrite Hc in Hvlen. rewrite (Zlength_correct vis1') in Hvlen.
        rewrite (Zlength_correct vis1'). simpl Z.of_nat in Hvlen. lia. }
      assert (HIH_tail : count_pred P (map (fun k => offset + Z.of_nat (S k)) (seq 0 n))
                              = Z.to_nat (count_nonzero vis1')).
      { replace (fun k => offset + Z.of_nat (S k)) with (fun k => (offset + 1) + Z.of_nat k).
        - apply IH; [ exact Hlen' | exact Htail_align ].
        - apply functional_extensionality_dep. intros k. simpl. lia. }
      cbn [seq map].
      replace (offset + Z.of_nat 0) with offset by lia.
      rewrite Hmap_seq1.
      cbn [count_pred].
      destruct (excluded_middle_informative (P offset)) as [Hp | Hnp].
      * assert (Hzne : z <> 0%Z) by (apply Hhead; exact Hp).
        assert (Hne : Z.eqb z 0 = false) by (apply Z.eqb_neq; exact Hzne).
        assert (Hif : (if Z.eqb z 0 then 0%Z else 1%Z) = 1%Z) by (rewrite Hne; reflexivity).
        rewrite Hif.
        rewrite HIH_tail.
        replace (1 + count_nonzero vis1')%Z with (Z.succ (count_nonzero vis1')) by lia.
        rewrite Z2Nat.inj_succ by apply count_nonzero_nonneg.
        lia.
      * assert (Hz : z = 0%Z).
        { destruct (Z.eq_dec z 0) as [Heq | Hneq]; [ exact Heq | ].
          exfalso. apply Hnp. apply Hhead. intro Hc. apply Hneq. exact Hc. }
        rewrite Hz.
        replace (if Z.eqb 0 0 then 0%Z else 1%Z) with 0%Z by (rewrite Z.eqb_refl; reflexivity).
        rewrite HIH_tail. rewrite Z.add_0_l. reflexivity.
Qed.

(* Bridge: count_pred (visited1 st) over bijective_listV g equals
   Z.to_nat (count_nonzero vis1), given pre_dfs1 + Zlength vis1 = adj_verts g
   + AdjGraphValid g.  Routes through the Permutation to listV (seq) and the
   position-aligned count. *)
Lemma pre_dfs1_count_pred_bijective_eq :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z)
         (timer_v: Z) (st: KSt),
    AdjGraphValid g ->
    (Zlength vis1 = adj_verts g)%Z ->
    pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v st ->
    count_pred (visited1 st) (bijective_listV g) = Z.to_nat (count_nonzero vis1).
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v st Hgv Hvlen Hpre.
  destruct Hpre as [Hpv [Hpf [Hpt [Hvi Hfi]]]].
  assert (Hfwd : (Zlength (adj_fwd g) = adj_verts g)%Z) by (exact (proj1 Hgv)).
  assert (Hag : (0 <= adj_verts g)%Z)
    by (rewrite <- Hfwd; rewrite Zlength_correct; apply Nat2Z.is_nonneg).
  pose proof (AdjGraph_bijective_listV_perm g Hgv) as Hperm.
  rewrite (count_pred_perm _ _ _ Hperm).
  apply (count_pred_seq_aligned (visited1 st) vis1 (Z.to_nat (adj_verts g)) 0%Z).
  - transitivity (adj_verts g).
    + exact Hvlen.
    + symmetry. apply Z2Nat.id. exact Hag.
  - intros k Hk.
    rewrite (Z2Nat.id (adj_verts g) Hag) in Hk.
    replace (0 + k) with k by lia.
    apply Hpv. exact Hk.
Qed.

Lemma pre_dfs1_finish_count_pred_bijective_eq :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z)
         (timer_v: Z) (st: KSt),
    AdjGraphValid g ->
    (Zlength fin_l = adj_verts g)%Z ->
    pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v st ->
    dfs1_finish_arrays_inv g vis1 fin_l timer_v ->
    count_pred (fun v => finish st v <> 0%nat) (bijective_listV g) =
    Z.to_nat (count_nonzero fin_l).
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v st Hgv Hflen Hpre Hfinv.
  destruct Hpre as [Hpv [Hpf [Hpt [Hvi Hfi]]]].
  destruct Hfinv as [Ht0 [Htcnt [Hunvis0 Hvisbd]]].
  assert (Hfwd : (Zlength (adj_fwd g) = adj_verts g)%Z) by (exact (proj1 Hgv)).
  assert (Hag : (0 <= adj_verts g)%Z)
    by (rewrite <- Hfwd; rewrite Zlength_correct; apply Nat2Z.is_nonneg).
  pose proof (AdjGraph_bijective_listV_perm g Hgv) as Hperm.
  rewrite (count_pred_perm _ _ _ Hperm).
  apply (count_pred_seq_aligned (fun v => finish st v <> 0%nat)
           fin_l (Z.to_nat (adj_verts g)) 0%Z).
  - transitivity (adj_verts g).
    + exact Hflen.
    + symmetry. apply Z2Nat.id. exact Hag.
  - intros k Hk.
    rewrite (Z2Nat.id (adj_verts g) Hag) in Hk.
    replace (0 + k) with k by lia.
    rewrite (Hpf k Hk).
    assert (Hfin_nonneg : (0 <= Znth k fin_l 0)%Z).
    { destruct (Z.eq_dec (Znth k vis1 0) 0) as [Hz | Hnz].
      - rewrite (Hunvis0 k Hk Hz). lia.
      - pose proof (Hvisbd k Hk Hnz) as Hbd. lia. }
    split; intro Hnz.
    + intro Hz. apply Hnz. rewrite Hz. reflexivity.
    + intro Hzero.
      apply Hnz.
      destruct (Znth k fin_l 0); simpl in Hzero; lia.
Qed.

Lemma pre_dfs1_finish_arrays_inv_DFSFinishInv :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1_l fin_l: list Z)
         (timer_v: Z) (st: KSt),
    pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v st ->
    csr_wf1 g radj_col_l radj_row_l vis1_l fin_l ->
    dfs1_finish_arrays_inv g vis1_l fin_l timer_v ->
    @DFSFinishInv AdjGraph Z (Z * Z) KG g st.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v st
         Hpre Hwf Hfinv.
  pose proof Hpre as Hpre_full.
  pose proof Hfinv as Hfinv_full.
  destruct Hwf as [Hgv [Hrow [Hvislen [Hfinlen Hrest]]]].
  destruct Hpre as [Hpv [Hpf [Htimer [Hvis_invalid Hfin_invalid]]]].
  destruct Hfinv as [Ht0 [Htcnt [Hunvis0 Hvisbd]]].
  unfold DFSFinishInv, DFSFinishInvCore, DFSFinishScoped.
  split.
  - split.
    + unfold FinishedCount. rewrite Htimer, Htcnt.
      symmetry.
      exact (pre_dfs1_finish_count_pred_bijective_eq
        g radj_col_l radj_row_l vis1_l fin_l timer_v st
        Hgv Hfinlen Hpre_full Hfinv_full).
    + split.
      * unfold UnvisitedFinishZero. intros v Hnotvis.
    destruct (classic (0 <= v < adj_verts g)%Z) as [Hvvalid | Hvinvalid].
      -- assert (Hvisz : Znth v vis1_l 0 = 0%Z).
         { destruct (Z.eq_dec (Znth v vis1_l 0) 0) as [Hz | Hnz]; [ exact Hz | ].
           exfalso. apply Hnotvis. apply (proj2 (Hpv v Hvvalid)). exact Hnz. }
         rewrite (Hpf v Hvvalid).
         rewrite (Hunvis0 v Hvvalid Hvisz). reflexivity.
      -- apply Hfin_invalid. exact Hvinvalid.
      * split.
        -- rewrite Htimer.
    unfold Kosaraju.cardV.
    assert (Hcount_vis :
              count_pred (visited1 st) (bijective_listV g) =
              Z.to_nat (count_nonzero vis1_l)).
    { apply pre_dfs1_count_pred_bijective_eq
        with (radj_col_l := radj_col_l) (radj_row_l := radj_row_l)
             (fin_l := fin_l) (timer_v := timer_v);
        try exact Hgv; try exact Hvislen.
      unfold pre_dfs1.
      split; [ exact Hpv | split; [ exact Hpf | split; [ exact Htimer | split; [ exact Hvis_invalid | exact Hfin_invalid ] ] ] ]. }
    replace (count_pred (visited1 st) (bijective_listV g))
      with (Z.to_nat (count_nonzero vis1_l)) by (symmetry; exact Hcount_vis).
    assert (Hfin_le_vis :
              (count_pred (fun v => finish st v <> 0%nat) (bijective_listV g) <=
               count_pred (visited1 st) (bijective_listV g))%nat).
    { pose proof
        (count_pred_mono (fun v => finish st v <> 0%nat) (visited1 st)
           (bijective_listV g)) as Hmono.
      assert (Himpl :
                forall v : Z, In v (bijective_listV g) ->
                  finish st v <> 0%nat -> visited1 st v).
      { intros v Hin Hfin_nz.
        pose proof (bijective_vertices g Hgv v) as Hbij.
        assert (Hvvalid : vvalid g v) by (apply Hbij; exact Hin).
        cbv [vvalid adj_vvalid] in Hvvalid.
        destruct (classic (visited1 st v)) as [Hvis | Hnot]; [ exact Hvis | ].
        pose proof (Hpv v Hvvalid) as Hiff.
        assert (Hvisz : Znth v vis1_l 0 = 0%Z).
        { destruct (Z.eq_dec (Znth v vis1_l 0) 0) as [Hz | Hnz]; [ exact Hz | ].
          exfalso. apply Hnot. apply (proj2 Hiff). exact Hnz. }
        rewrite (Hpf v Hvvalid) in Hfin_nz.
        rewrite (Hunvis0 v Hvvalid Hvisz) in Hfin_nz.
        contradiction. }
      specialize (Hmono Himpl). lia. }
    assert (Hcount_fin :
              count_pred (fun v => finish st v <> 0%nat) (bijective_listV g) =
              Z.to_nat (count_nonzero fin_l)).
    { apply pre_dfs1_finish_count_pred_bijective_eq
        with (radj_col_l := radj_col_l) (radj_row_l := radj_row_l)
             (vis1 := vis1_l) (timer_v := timer_v);
        try exact Hgv; try exact Hfinlen.
      - unfold pre_dfs1.
        split; [ exact Hpv | split; [ exact Hpf | split; [ exact Htimer | split; [ exact Hvis_invalid | exact Hfin_invalid ] ] ] ].
      - unfold dfs1_finish_arrays_inv.
        split; [ exact Ht0 | ].
        split; [ exact Htcnt | ].
        split; [ exact Hunvis0 | exact Hvisbd ]. }
    rewrite Htcnt.
    rewrite <- Hcount_fin.
    rewrite <- Hcount_vis.
    exact Hfin_le_vis.
        -- unfold TimerDominates. intros v Hvis.
    destruct (classic (0 <= v < adj_verts g)%Z) as [Hvvalid | Hvinvalid].
      ++ rewrite (Hpf v Hvvalid), Htimer.
         assert (Hvisnz : Znth v vis1_l 0 <> 0%Z).
         { apply (proj1 (Hpv v Hvvalid)). exact Hvis. }
         pose proof (Hvisbd v Hvvalid Hvisnz) as Hbd.
         apply Nat2Z.inj_le.
         repeat rewrite Nat2Z.id.
         rewrite Z2Nat.id by lia.
         rewrite Z2Nat.id by lia.
         lia.
      ++ exfalso. apply (Hvis_invalid v Hvinvalid). exact Hvis.
  - split; assumption.
Qed.

Lemma dfs_finish_phase1_checked_noerr :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u : Z) (entry : KSt),
    pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u entry ->
    ~ MonadErr.err
        (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l timer_v u)
        entry.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u entry Hpre_full Herr.
  pose proof Hpre_full as Hpre_work.
  destruct Hpre_work as [Hpre_dfs Hready].
  destruct Hready as [[Hwf [_ Hfinv]] [_ [_ [Hroot _]]]].
  pose proof (Hroot entry Hpre_dfs) as [Hnot Hvalid].
  assert (Hinv : @DFSFinishInv AdjGraph Z (Z * Z) KG g entry).
  { eapply pre_dfs1_finish_arrays_inv_DFSFinishInv; eauto. }
  assert (Hgv : gvalid g).
  { destruct Hwf as [Hgv _]. exact Hgv. }
  assert (Hgv' : @gvalid AdjGraph (@kos_gvalid AdjGraph Z (Z * Z) KG) g) by exact Hgv.
  pose proof (DFS_finish_phase1_frame_light g Hgv' entry u Hinv Hnot Hvalid)
    as [Hdfs_nrm Hdfs_noerr].
  unfold dfs_finish_phase1_checked in Herr.
  cbv [MonadErr.bind MonadErr.nrm_err get assertS] in Herr.
  destruct Herr as [Herr_get | Herr_rest].
  - exact Herr_get.
  - destruct Herr_rest as [entry0 [s0 [[Hentry0 Hs0] Herr_rest]]].
    subst entry0 s0.
    destruct Herr_rest as [Hassert_fail | Herr_rest].
    + apply Hassert_fail. split; [ reflexivity | exact Hpre_full ].
    + destruct Herr_rest as [r0 [s1 [[Hs1 _] Herr_rest]]].
      destruct r0. subst s1.
      destruct Herr_rest as [Hdfs_err | Herr_rest].
      * exact (Hdfs_noerr entry eq_refl Hdfs_err).
      * destruct Herr_rest as [r1 [s2 [Hdfs_step Hassert_fail]]].
        apply Hassert_fail.
        pose proof (Hdfs_nrm r1 entry s2 eq_refl Hdfs_step) as [Hframe Hvisu].
        unfold dfs1_phase1_result.
        destruct Hframe as [Hinv' [Hsub [Hfin_pres _]]].
        split; [ exact Hinv' | ].
        split; [ exact Hvisu | ].
        split; [ exact Hsub | exact Hfin_pres ].
Qed.

Lemma dfs_finish_phase1_checked_safe_result_state :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u : Z),
    (exists st,
       pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u st) ->
    safeExec
      (pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u)
      (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l timer_v u)
      (result_state
         (pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u)
         (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l timer_v u)).
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u [st Hpre].
  apply safeExec_result_state.
  exists st. split; [ exact Hpre | ].
  eapply dfs_finish_phase1_checked_noerr; exact Hpre.
Qed.

Lemma safe_checked_dfs_finish_bind_from_raw :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u : Z) {A : Type} (k : unit -> program KSt A)
         (X : A -> KSt -> Prop) (entry : KSt),
    pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u entry ->
    safe entry (dfs_finish g u;; k tt) X ->
    safe entry
      (bind (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l
              timer_v u) k) X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u A k X entry Hpre Hraw.
  unfold safe, weakestpre in *.
  destruct Hraw as [Hraw_noerr Hraw_post].
  split.
  - rewrite bind_noerr_iff.
    split.
    + eapply dfs_finish_phase1_checked_noerr; exact Hpre.
    + intros [] st Hchecked_nrm.
      apply bind_noerr_iff in Hraw_noerr as [_ Hraw_k_noerr].
      eapply Hraw_k_noerr.
      eapply dfs_finish_phase1_checked_nrm_raw; exact Hchecked_nrm.
  - intros a st Hchecked_bind_nrm.
    cbv [MonadErr.bind MonadErr.nrm_nrm] in Hchecked_bind_nrm.
    destruct Hchecked_bind_nrm as [[] [mid [Hchecked_nrm Hk_nrm]]].
    apply Hraw_post.
    cbv [MonadErr.bind MonadErr.nrm_nrm].
    exists tt, mid.
    split; [ | exact Hk_nrm ].
    eapply dfs_finish_phase1_checked_nrm_raw; exact Hchecked_nrm.
Qed.

Lemma dfs_finish_schedule_checked_step_safeExec :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u n : Z) (X : unit -> KSt -> Prop),
    0 <= u ->
    u < n ->
    dfs1_phase1_ready g radj_col_l radj_row_l vis1_l fin_l timer_v u ->
    safeExec
      (pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish_schedule g u (n - u))
      X ->
    safeExec
      (pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u)
      (bind (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l
              timer_v u)
            (dfs_finish_scheduleK g (u + 1) ((n - u) - 1)))
      X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u n X
    Hu Hlt Hready Hsafe.
  assert (Hrawsafe :
    safeExec
      (pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish g u;;
       dfs_finish_schedule g (u + 1) ((n - u) - 1))
      X).
  {
    replace (n - u) with (((n - u) - 1) + 1) in Hsafe by lia.
    rewrite dfs_finish_schedule_step in Hsafe by lia.
    unfold if_else in Hsafe.
    apply safeExec_choice_r in Hsafe.
    eapply safeExec_testst_bind in Hsafe; [ exact Hsafe | ].
    intros st Hpre.
    destruct Hready as [_ [_ [_ [Hroot _]]]].
    exact (proj1 (Hroot st Hpre)).
  }
  unfold safeExec in *.
  destruct Hrawsafe as [st [Hpre Hraw]].
  exists st.
  split; [ exact (conj Hpre Hready) | ].
  change (dfs_finish_scheduleK g (u + 1) ((n - u) - 1) tt)
    with (dfs_finish_schedule g (u + 1) ((n - u) - 1)).
  eapply safe_checked_dfs_finish_bind_from_raw;
    [ exact (conj Hpre Hready) | exact Hraw ].
Qed.

Lemma dfs_finish_schedule_unvisited_step_safeExec_sequence :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u n : Z) (X : unit -> KSt -> Prop),
    0 <= u ->
    u < n ->
    adj_verts g = n ->
    Znth u vis1_l 0 = 0 ->
    safeExec
      (pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish_schedule g u (n - u))
      X ->
    safeExec
      (pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (bind (dfs_finish g u)
            (dfs_finish_scheduleK g (u + 1) ((n - u) - 1)))
      X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u n X
    Hu Hlt Hverts Hvis0 Hsafe.
  replace (n - u) with (((n - u) - 1) + 1) in Hsafe by lia.
  rewrite dfs_finish_schedule_step in Hsafe by lia.
  unfold if_else in Hsafe.
  apply safeExec_choice_r in Hsafe.
  eapply safeExec_testst_bind in Hsafe; [ exact Hsafe | ].
  intros st Hpre.
  destruct Hpre as [Hpv _].
  intro Hvis.
  apply (proj1 (Hpv u ltac:(rewrite Hverts; lia))) in Hvis.
  congruence.
Qed.

Lemma dfs_finish_schedule_skip_safeExec :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u n : Z) (X : unit -> KSt -> Prop),
    0 <= u ->
    u < n ->
    adj_verts g = n ->
    Znth u vis1_l 0 <> 0 ->
    safeExec
      (pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish_schedule g u (n - u))
      X ->
    safeExec
      (pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish_schedule g (u + 1) (n - (u + 1)))
      X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u n X
    Hu Hlt Hverts Hvis Hsafe.
  replace (n - (u + 1)) with ((n - u) - 1) by lia.
  replace (n - u) with (((n - u) - 1) + 1) in Hsafe by lia.
  rewrite dfs_finish_schedule_step in Hsafe by lia.
  unfold if_else in Hsafe.
  apply safeExec_choice_l in Hsafe.
  eapply safeExec_testst_bind in Hsafe; [ exact Hsafe | ].
  intros st Hpre.
  destruct Hpre as [Hpv _].
  apply (proj2 (Hpv u ltac:(rewrite Hverts; lia))).
  exact Hvis.
Qed.

Lemma dfs_finish_schedule_skip_safeExec_sequence :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l : list Z)
         (timer_v u n : Z) (X : unit -> KSt -> Prop),
    0 <= u ->
    u < n ->
    adj_verts g = n ->
    Znth u vis1_l 0 <> 0 ->
    safeExec
      (pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish_schedule g u (n - u))
      X ->
    safeExec
      (pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish_schedule g (u + 1) (n - (u + 1)))
      X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l timer_v u n X
    Hu Hlt Hverts Hvis Hsafe.
  replace (n - (u + 1)) with ((n - u) - 1) by lia.
  replace (n - u) with (((n - u) - 1) + 1) in Hsafe by lia.
  rewrite dfs_finish_schedule_step in Hsafe by lia.
  unfold if_else in Hsafe.
  apply safeExec_choice_l in Hsafe.
  eapply safeExec_testst_bind in Hsafe; [ exact Hsafe | ].
  intros st Hpre.
  destruct Hpre as [Hpv _].
  apply (proj2 (Hpv u ltac:(rewrite Hverts; lia))).
  exact Hvis.
Qed.

Lemma dfs1_finish_arrays_inv_visit1 :
  forall (g: AdjGraph) (vis1_l fin_l: list Z) (timer_v u: Z),
    (0 <= u < adj_verts g)%Z ->
    (Zlength vis1_l = adj_verts g)%Z ->
    dfs1_finish_arrays_inv g vis1_l fin_l timer_v ->
    Znth u vis1_l 0 = 0%Z ->
    dfs1_finish_arrays_inv g (replace_Znth u 1 vis1_l) fin_l timer_v.
Proof.
  intros g vis1_l fin_l timer_v u Hub Hvlen Hinv Hvisu0.
  destruct Hinv as [Ht0 [Htcnt [Hunvis0 Hvisbd]]].
  unfold dfs1_finish_arrays_inv.
  split; [ exact Ht0 | ].
  split; [ exact Htcnt | ].
  split.
  - intros w Hw Hvisw0.
    assert (Hwidx : (0 <= w < Zlength vis1_l)%Z) by (rewrite Hvlen; exact Hw).
    destruct (Z.eq_dec w u) as [Heq | Hne].
    + subst w.
      rewrite (Znth_replace_eq vis1_l u 1 0 Hwidx) in Hvisw0.
      lia.
    + rewrite (Znth_replace_neq vis1_l w u 1 0 Hwidx (proj1 Hub) Hne) in Hvisw0.
      apply Hunvis0; assumption.
  - intros w Hw Hvisw.
    assert (Hwidx : (0 <= w < Zlength vis1_l)%Z) by (rewrite Hvlen; exact Hw).
    destruct (Z.eq_dec w u) as [Heq | Hne].
    + subst w. rewrite (Hunvis0 u Hub Hvisu0). lia.
    + rewrite (Znth_replace_neq vis1_l w u 1 0 Hwidx (proj1 Hub) Hne) in Hvisw.
      apply Hvisbd; assumption.
Qed.

Lemma dfs1_finish_arrays_inv_set_finish :
  forall (g: AdjGraph) (vis1_l fin_l: list Z) (timer_v u: Z),
    (0 <= u < adj_verts g)%Z ->
    (Zlength fin_l = adj_verts g)%Z ->
    dfs1_finish_arrays_inv g vis1_l fin_l timer_v ->
    Znth u fin_l 0 = 0%Z ->
    Znth u vis1_l 0 <> 0%Z ->
    dfs1_finish_arrays_inv g vis1_l (replace_Znth u (timer_v + 1) fin_l) (timer_v + 1).
Proof.
  intros g vis1_l fin_l timer_v u Hub Hflen Hinv Hfinu0 Hvisu.
  destruct Hinv as [Ht0 [Htcnt [Hunvis0 Hvisbd]]].
  assert (Huidx : (0 <= u < Zlength fin_l)%Z) by (rewrite Hflen; exact Hub).
  unfold dfs1_finish_arrays_inv.
  split; [ lia | ].
  split.
  - rewrite count_nonzero_replace_Znth by exact Huidx.
    rewrite Hfinu0.
    rewrite Z.eqb_refl.
    assert (Hnz : Z.eqb (timer_v + 1) 0 = false).
    { apply Z.eqb_neq. lia. }
    rewrite Hnz.
    lia.
  - split.
    + intros w Hw Hvisw0.
      assert (Hwidx : (0 <= w < Zlength fin_l)%Z) by (rewrite Hflen; exact Hw).
      destruct (Z.eq_dec w u) as [Heq | Hne].
      * subst w. contradiction.
      * rewrite (Znth_replace_neq fin_l w u (timer_v + 1) 0 Hwidx (proj1 Huidx) Hne).
        apply Hunvis0; assumption.
    + intros w Hw Hvisw.
      assert (Hwidx : (0 <= w < Zlength fin_l)%Z) by (rewrite Hflen; exact Hw).
      destruct (Z.eq_dec w u) as [Heq | Hne].
      * subst w. rewrite (Znth_replace_eq fin_l u (timer_v + 1) 0 Huidx). lia.
      * rewrite (Znth_replace_neq fin_l w u (timer_v + 1) 0 Hwidx (proj1 Huidx) Hne).
        pose proof (Hvisbd w Hw Hvisw) as Hbd. lia.
Qed.

(* Bridge the timer bound: timer st = Z.to_nat timer_v <= length (bijective_listV g).
   Uses count_nonzero_le_Zlength + Zlength vis1 = adj_verts g + the Permutation
   (length is Permutation-invariant). *)
Lemma pre_dfs1_timer_le_bijective_length :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z)
         (timer_v: Z) (st: KSt),
    AdjGraphValid g ->
    (Zlength vis1 = adj_verts g)%Z ->
    pre_dfs1 g radj_col_l radj_row_l vis1 fin_l timer_v st ->
    (timer_v <= count_nonzero vis1)%Z ->
    (timer st <= length (bijective_listV g))%nat.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v st Hgv Hvlen Hpre Htbound.
  destruct Hpre as [Hpv [Hpf [Hpt [Hvi Hfi]]]].
  pose proof (AdjGraph_bijective_listV_perm g Hgv) as Hperm.
  rewrite (Permutation_length Hperm).
  rewrite length_map. rewrite length_seq.
  rewrite Hpt.
  assert (Hag : (0 <= adj_verts g)%Z) by (rewrite <- (proj1 Hgv); rewrite Zlength_correct; apply Nat2Z.is_nonneg).
  destruct (Z_le_dec 0 timer_v) as [Htv | Htvneg].
  - apply (proj1 (Z2Nat.inj_le timer_v (adj_verts g) Htv Hag)).
    pose proof (count_nonzero_le_Zlength vis1) as Hle.
    lia.
  - assert (Hz : Z.to_nat timer_v = 0%nat).
    { destruct timer_v; simpl; try reflexivity; lia. }
    rewrite Hz. lia.
Qed.

(* ===================================================================== *)
(* dfs1_entry_close: phase-1 entry refinement (mirror of dfs2_entry_close).
   Given safeExec (pre_dfs1 vis1 fin timer_v) (dfs_finish g u) X, the
   cursor-indexed continuation dfs_finish_from g radj_col radj_row u lo
   refines dfs_finish g u at the entry cursor (i = csr_lo u radj_row_l,
   e_set = empty), under the post-visit1 precondition (vis1[u] := 1).
   Composes dfs1_visit_decompose (peel visit1 u prelude, Qed) with
   dfs_finish_from_sim (cursor vs repeat_break at i = lo, e_set = empty).
   Phase-1 invariant and timer facts are discharged inside
   dfs_finish_from_sim from the strengthened monad assertions.
   ===================================================================== *)
Lemma dfs1_entry_close :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1_l fin_l: list Z) (u timer_v: Z)
         (X: unit -> KSt -> Prop),
    csr_wf1 g radj_col_l radj_row_l vis1_l fin_l ->
    csr1_faithful g radj_col_l radj_row_l ->
    (0 <= u < adj_verts g)%Z ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l vis1_l fin_l timer_v) (dfs_finish g u) X ->
    safeExec (pre_dfs1 g radj_col_l radj_row_l (replace_Znth u 1 vis1_l) fin_l timer_v)
             (dfs_finish_from g radj_col_l radj_row_l u (csr_lo u radj_row_l)) X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l u timer_v X Hwf Hfaith Hub Hsafe.
  (* Extract csr_wf1 conjuncts; re-conjoin Hwf for dfs_finish_from_sim. *)
  destruct Hwf as [Hgv [Hlenrow [Hlenvis [Hlenfin [Hmof [Hlolo [Hhihi [Hneigh [Hlolohi Hmcap]]]]]]]]].
  assert (Hwf' : csr_wf1 g radj_col_l radj_row_l vis1_l fin_l).
  { unfold csr_wf1. repeat (split; [ assumption | ]); try assumption. }
  (* Peel visit1 u prelude; land safeExec over repeat_break B ∅ at σ'. *)
  pose proof (dfs1_visit_decompose g radj_col_l radj_row_l vis1_l fin_l timer_v u X
                Hgv Hlenvis Hub Hsafe) as Hdec.
  destruct Hdec as [σ' [Hpreσ' Hsafeσ']].
  (* pre_dfs1 conjuncts (Hpreσ' kept intact for the final safeExec wrap). *)
  pose proof (proj1 Hpreσ') as Hvis.
  (* visited1 σ' u: Znth u (replace_Znth u 1 vis1_l) 0 = 1 <> 0 via Znth_replace_eq. *)
  assert (Huvis : (0 <= u < Zlength vis1_l)%Z) by (rewrite Hlenvis; exact Hub).
  assert (Hvisu : visited1 σ' u).
  { apply (proj2 (Hvis u Hub)).
    rewrite (Znth_replace_eq vis1_l u 1 0 Huvis). discriminate. }
  (* Apply dfs_finish_from_sim at the entry cursor (i = csr_lo u, e_set = ∅, σ'). *)
  set (lo := csr_lo u radj_row_l) in *.
  set (hi := csr_hi u radj_row_l) in *.
  assert (Hlo_eq : csr_lo u radj_row_l = lo) by reflexivity.
  assert (Hhi_eq : csr_hi u radj_row_l = hi) by reflexivity.
  assert (Hloi : (lo <= lo)%Z) by lia.
  assert (Hlohi : (0 <= hi - lo)%Z).
  { pose proof (Hlolohi u Hub) as Hlh. unfold lo, hi in *. lia. }
  set (n := Z.to_nat (hi - lo)).
  assert (Hfuel : Z.to_nat (hi - lo) = n) by reflexivity.
  (* Invariants at entry (i = lo, e_set = ∅): A vacuous (empty set),
     B vacuous (empty range lo<=k<lo), E trivial (~ empty-set membership). *)
  assert (HA : forall (e: Z * Z), (fun _ => False) e ->
                exists k, (lo <= k < lo)%Z /\ e = (Znth k radj_col_l 0, u)).
  { intros e Hf. exfalso. exact Hf. }
  assert (HB : forall k, (lo <= k < lo)%Z -> ~ (fun _ => False) (Znth k radj_col_l 0, u) ->
                 visited1 σ' (Znth k radj_col_l 0)).
  { intros k [Hk1 Hk2] _. lia. }
  assert (HE : forall j, (lo <= j < hi)%Z -> ~ visited1 σ' (Znth j radj_col_l 0) ->
                 ~ (fun _ => False) (Znth j radj_col_l 0, u)).
  { intros j Hj Hnv Hf. exact Hf. }
  (* Apply the cursor-vs-repeat_break simulation. *)
  assert (Hsafe_ih : safe σ' (dfs_finish_from g radj_col_l radj_row_l u lo) X).
  { eapply dfs_finish_from_sim;
      [ exact Hlo_eq | exact Hhi_eq | exact Hwf' | exact Hfaith | exact Hub |
        exact Hfuel | exact Hloi | exact HA | exact HB | exact HE |
        exact Hvisu | exact Hsafeσ' ]. }
  (* Wrap back to safeExec at σ'. *)
  exists σ'. split; [ exact Hpreσ' | exact Hsafe_ih ].
Qed.

Definition csr_layout
  (g : AdjGraph) (col_l row_l : list Z) : Prop :=
  Zlength row_l = adj_verts g + 1 /\
  m_of row_l = Zlength col_l /\
  csr_lo 0 row_l = 0 /\
  (forall u, 0 <= u < adj_verts g ->
     0 <= csr_lo u row_l /\
     csr_lo u row_l <= csr_hi u row_l /\
     csr_hi u row_l <= m_of row_l) /\
  (forall u, 0 <= u < adj_verts g - 1 ->
     csr_hi u row_l <= csr_hi (u + 1) row_l) /\
  (forall j, 0 <= j < m_of row_l ->
     0 <= Znth j col_l 0 < adj_verts g).

Definition transpose_spec
  (g : AdjGraph) (fadj_col_l fadj_row_l radj_col_l radj_row_l : list Z)
  (n : Z) : Prop :=
  adj_verts g = n /\
  AdjGraphValid g /\
  m_of fadj_row_l = m_of radj_row_l /\
  csr2_faithful g fadj_col_l fadj_row_l /\
  csr_layout g radj_col_l radj_row_l /\
  csr1_faithful g radj_col_l radj_row_l.

Lemma transpose_spec_m_of :
  forall g fadj_col_l fadj_row_l radj_col_l radj_row_l n,
    transpose_spec g fadj_col_l fadj_row_l radj_col_l radj_row_l n ->
    m_of fadj_row_l = m_of radj_row_l.
Proof.
  intros g fadj_col_l fadj_row_l radj_col_l radj_row_l n Hspec.
  unfold transpose_spec in Hspec.
  tauto.
Qed.

Lemma transpose_spec_csr1_faithful :
  forall g fadj_col_l fadj_row_l radj_col_l radj_row_l n,
    transpose_spec g fadj_col_l fadj_row_l radj_col_l radj_row_l n ->
    csr1_faithful g radj_col_l radj_row_l.
Proof.
  intros g fadj_col_l fadj_row_l radj_col_l radj_row_l n Hspec.
  unfold transpose_spec in Hspec.
  tauto.
Qed.

Lemma csr_wf1_of_transpose_spec :
  forall g fadj_col_l fadj_row_l radj_col_l radj_row_l vis1_l fin_l n,
    transpose_spec g fadj_col_l fadj_row_l radj_col_l radj_row_l n ->
    csr_wf2_core g fadj_col_l fadj_row_l ->
    Zlength vis1_l = n ->
    Zlength fin_l = n ->
    csr_wf1 g radj_col_l radj_row_l vis1_l fin_l.
Proof.
  intros g fadj_col_l fadj_row_l radj_col_l radj_row_l vis1_l fin_l n
    Hspec Hcore Hvis Hfin.
  unfold transpose_spec in Hspec.
  destruct Hspec as [Hverts [Hvalid [Hmof [_ [Hlayout _]]]]].
  unfold csr_layout in Hlayout.
  destruct Hlayout as [Hrow_len [Hcol_len [Hlo0 [Hbounds [Hroword Hcol]]]]].
  unfold csr_wf2_core in Hcore.
  destruct Hcore as [_ [_ [Hfcol_len [_ [_ [_ [_ Hcap]]]]]]].
  unfold csr_wf1.
  split; [exact Hvalid |].
  split; [exact Hrow_len |].
  split; [rewrite Hverts; exact Hvis |].
  split; [rewrite Hverts; exact Hfin |].
  split; [exact Hcol_len |].
  split.
  - intros u Hu.
    exact (proj1 (Hbounds u Hu)).
  - split.
    + intros u Hu.
      exact (proj2 (proj2 (Hbounds u Hu))).
    + split; [exact Hcol |].
      split.
      * intros u Hu.
        exact (proj1 (proj2 (Hbounds u Hu))).
      * rewrite <- Hmof.
        exact Hcap.
Qed.

Lemma pre_dfs1_sequence_initial_init :
  forall g radj_col_l radj_row_l vis1_l fin_l n,
    adj_verts g = n ->
    0 <= n ->
    Zlength vis1_l = n ->
    Zlength fin_l = n ->
    (forall v, 0 <= v < n -> Znth v vis1_l 0 = 0) ->
    pre_dfs1_sequence_initial g radj_col_l radj_row_l vis1_l fin_l n
      (@Kosaraju.init_st Z).
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l n Hverts Hn Hvis Hfin Hzero.
  unfold pre_dfs1_sequence_initial, pre_dfs1_sequence, fin_sequence_rep.
  split; [reflexivity |].
  split.
  - split.
    + intros v Hv.
      unfold Kosaraju.init_st; simpl.
      rewrite Hzero by lia.
      split; [contradiction | congruence].
    + split.
      * unfold Kosaraju.init_st; simpl. intros v _ Hfalse. exact Hfalse.
      * split; [lia |].
        split.
        -- rewrite Hverts. exact Hfin.
        -- split.
           ++ unfold Kosaraju.init_st; simpl. reflexivity.
           ++ split.
              ** intros t Ht. lia.
              ** split.
                 --- intros v Hv Hfin_nonzero.
                     unfold Kosaraju.init_st in Hfin_nonzero; simpl in Hfin_nonzero.
                     contradiction.
                 --- intros v Hinvalid.
                     unfold Kosaraju.init_st; simpl. reflexivity.
  - split; [exact Hvis | exact Hzero].
Qed.

Lemma phase1_sequence_refinement_init :
  forall g fadj_col_l fadj_row_l radj_col_l radj_row_l vis1_l fin_l n,
    transpose_spec g fadj_col_l fadj_row_l radj_col_l radj_row_l n ->
    csr_wf2_core g fadj_col_l fadj_row_l ->
    Zlength vis1_l = n ->
    Zlength fin_l = n ->
    (forall v, 0 <= v < n -> Znth v vis1_l 0 = 0) ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l
      vis1_l fin_l vis1_l fin_l 0 n 0.
Proof.
  intros g fadj_col_l fadj_row_l radj_col_l radj_row_l vis1_l fin_l n
    Hspec Hcore Hvis Hfin Hzero Hn.
  pose proof (csr_wf1_of_transpose_spec g fadj_col_l fadj_row_l
    radj_col_l radj_row_l vis1_l fin_l n Hspec Hcore Hvis Hfin) as Hwf1.
  pose proof (transpose_spec_csr1_faithful g fadj_col_l fadj_row_l
    radj_col_l radj_row_l n Hspec) as Hfaith.
  unfold transpose_spec in Hspec.
  destruct Hspec as [Hverts [Hvalid _]].
  unfold phase1_sequence_refinement.
  split.
  - unfold dfs1_sequence_state_ready.
    split; [exact Hwf1 |].
    split; [exact Hfaith | lia].
  - split.
    + pose proof (count_nonzero_nonneg vis1_l).
      lia.
    + unfold safeExec, safe, result_state.
      exists (@Kosaraju.init_st Z).
      split.
      * destruct (pre_dfs1_sequence_initial_init g radj_col_l radj_row_l
          vis1_l fin_l n Hverts Hn Hvis Hfin Hzero) as [_ [Hpre _]].
        exact Hpre.
      * pose proof (dfs_finish_schedule_phase1_order g n Hvalid Hverts Hn) as Hhoare.
        destruct Hhoare as [_ Hnoerr].
        split.
        -- intro Herr.
           replace (n - 0) with n in Herr by lia.
           exact (Hnoerr (@Kosaraju.init_st Z) eq_refl Herr).
        -- intros [] st' Hnrm.
           exists (@Kosaraju.init_st Z).
           replace (n - 0) with n in Hnrm by lia.
           split; [ | exact Hnrm ].
           apply pre_dfs1_sequence_initial_init; assumption.
Qed.

Definition fin_values_in_int_range (fin_l : list Z) (n : Z) : Prop :=
  forall v, 0 <= v < n -> 0 <= Znth v fin_l 0 <= INT_MAX.

(* This is the phase-1 refinement boundary carried by the C outer loop.
   The residual program is not an implementation mirror: it relates the
   current C arrays to the one whole monadic finish schedule rooted at the
   initial C state.  At cursor [n] the residual is [ret], so its result
   state is precisely the current C array representation of Phase1_Order. *)
Definition phase1_residual_refinement (g : AdjGraph)
  (radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l : list Z)
  (timer_v n u : Z) : Prop :=
  fin_values_in_int_range fin_l n /\
  fin_order_prefix fin_l vis_l timer_v n /\
  dfs1_phase1_state_ready g radj_col_l radj_row_l vis_l fin_l timer_v /\
  safeExec (pre_dfs1 g radj_col_l radj_row_l vis_l fin_l timer_v)
    (dfs_finish_schedule g u (n - u))
    (result_state
      (pre_dfs1_initial g radj_col_l radj_row_l vis0_l fin0_l n)
      (dfs_finish_schedule g 0 n)).

(* Sequence-valued phase-1 finish state.  Unlike the legacy finish-time
   relation above, [fin_l] stores each newly finished vertex at the next
   timer position; phase 2 consumes this sequence from right to left. *)
Definition order_init_prefix (n k : Z) (order_l : list Z) : Prop :=
  n <= Zlength order_l /\
  forall i, 0 <= i < k -> Znth i order_l 0 = i.

Definition order_entries_in_range (n : Z) (order_l : list Z) : Prop :=
  forall i, 0 <= i < n -> 0 <= Znth i order_l 0 < n.

Definition list_prefix_no_dup (n : Z) (l : list Z) : Prop :=
  forall i j,
    0 <= i < n ->
    0 <= j < n ->
    Znth i l 0 = Znth j l 0 ->
    i = j.

Definition fin_sequence_covers_range (n : Z) (fin_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    exists i, 0 <= i < n /\ Znth i fin_l 0 = v.

Definition base_order (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

Definition order_covers_range (n : Z) (order_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    exists i, 0 <= i < n /\ Znth i order_l 0 = v.

Definition order_spec (fin_l order_l : list Z) (n : Z) : Prop :=
  fin_values_in_int_range fin_l n /\
  order_entries_in_range n order_l.

Fixpoint fin_upperbound (fin_l : list Z) (x : Z) (l : list Z) : Prop :=
  match l with
  | nil => True
  | y :: l' => Znth x fin_l 0 >= Znth y fin_l 0 /\ fin_upperbound fin_l x l'
  end.

Fixpoint fin_nonincreasing_aux (fin_l : list Z) (l : list Z) (x : Z) : Prop :=
  match l with
  | nil => True
  | y :: l' =>
      Znth x fin_l 0 >= Znth y fin_l 0 /\
      fin_nonincreasing_aux fin_l l' y
  end.

Definition fin_nonincreasing (fin_l l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: l' => fin_nonincreasing_aux fin_l l' x
  end.

Definition fin_prefix_suffix_sorted
    (fin_l l1 l2 : list Z) : Prop :=
  forall x, In x l1 -> fin_upperbound fin_l x l2.

Fixpoint last_val (default : Z) (l : list Z) : Z :=
  match l with
  | nil => default
  | x :: l' => last_val x l'
  end.

Lemma last_val_in :
  forall x l, In (last_val x l) (x :: l).
Proof.
  intros x l.
  induction l as [|y l IH] in x |- *; simpl.
  - left; reflexivity.
  - right; apply IH.
Qed.

Lemma fin_nonincreasing_aux_snoc :
  forall fin_l l start x,
    fin_nonincreasing_aux fin_l l start ->
    Znth (last_val start l) fin_l 0 >= Znth x fin_l 0 ->
    fin_nonincreasing_aux fin_l (l ++ [x]) start.
Proof.
  induction l as [|y l IH]; intros start x Hinc Hlast; simpl in *.
  - split; [exact Hlast | exact I].
  - destruct Hinc as [Hle Hinc].
    split; [exact Hle |].
    apply IH; assumption.
Qed.

Lemma fin_nonincreasing_snoc :
  forall fin_l l x,
    fin_nonincreasing fin_l l ->
    match l with
    | nil => True
    | y :: l' => Znth (last_val y l') fin_l 0 >= Znth x fin_l 0
    end ->
    fin_nonincreasing fin_l (l ++ [x]).
Proof.
  intros fin_l l x Hinc Hlast.
  destruct l as [|y l].
  - simpl; exact I.
  - simpl in *.
    apply fin_nonincreasing_aux_snoc; assumption.
Qed.

Lemma fin_prefix_suffix_sorted_last :
  forall fin_l l1 x l2,
    fin_prefix_suffix_sorted fin_l l1 (x :: l2) ->
    match l1 with
    | nil => True
    | y :: l' => Znth (last_val y l') fin_l 0 >= Znth x fin_l 0
    end.
Proof.
  intros fin_l l1 x l2 Hsorted.
  destruct l1 as [|y l']; simpl; auto.
  unfold fin_prefix_suffix_sorted in Hsorted.
  specialize (Hsorted (last_val y l')).
  assert (Hin : In (last_val y l') (y :: l')) by apply last_val_in.
  specialize (Hsorted Hin).
  simpl in Hsorted.
  tauto.
Qed.

Lemma fin_upperbound_app_cons :
  forall fin_l x l y,
    fin_upperbound fin_l x l ->
    Znth x fin_l 0 >= Znth y fin_l 0 ->
    fin_upperbound fin_l x (l ++ [y]).
Proof.
  intros fin_l x l.
  induction l as [|z l IH]; intros y Hbound Hy; simpl in *.
  - split; [exact Hy | exact I].
  - destruct Hbound as [Hxz Hbound].
    split; [exact Hxz |].
    apply IH; assumption.
Qed.

Lemma fin_upperbound_trans :
  forall fin_l x y l,
    Znth x fin_l 0 >= Znth y fin_l 0 ->
    fin_upperbound fin_l y l ->
    fin_upperbound fin_l x l.
Proof.
  intros fin_l x y l Hxy.
  induction l as [|z l IH]; intros Hbound; simpl in *; auto.
  destruct Hbound as [Hyz Hbound].
  split; [lia | auto].
Qed.

Lemma fin_prefix_suffix_sorted_snoc :
  forall fin_l l1 x l2,
    fin_prefix_suffix_sorted fin_l l1 (x :: l2) ->
    fin_upperbound fin_l x l2 ->
    fin_prefix_suffix_sorted fin_l (l1 ++ [x]) l2.
Proof.
  intros fin_l l1 x l2 Hsorted Hbound.
  unfold fin_prefix_suffix_sorted in *.
  intros y Hy.
  apply in_app_or in Hy.
  destruct Hy as [Hy | Hy].
  - specialize (Hsorted y Hy).
    simpl in Hsorted.
    tauto.
  - simpl in Hy.
    destruct Hy as [Hy | Hy]; [subst; exact Hbound | contradiction].
Qed.

Lemma fin_upperbound_index :
  forall fin_l x l j,
    fin_upperbound fin_l x l ->
    0 <= j < Zlength l ->
    Znth x fin_l 0 >= Znth (Znth j l 0) fin_l 0.
Proof.
  intros fin_l x l.
  induction l as [|y l IH]; intros j Hbound Hj.
  - rewrite Zlength_nil in Hj; lia.
  - simpl in Hbound.
    destruct Hbound as [Hxy Hbound].
    destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
    + subst j. rewrite Znth0_cons. exact Hxy.
    + rewrite Znth_cons by lia.
      apply IH; [exact Hbound |].
      rewrite Zlength_cons in Hj.
      lia.
Qed.

Lemma fin_nonincreasing_aux_upperbound_start :
  forall fin_l l start,
    fin_nonincreasing_aux fin_l l start ->
    fin_upperbound fin_l start l.
Proof.
  intros fin_l l.
  induction l as [|y l IH]; intros start Hinc; simpl in *; auto.
  destruct Hinc as [Hstart Htail].
  split; [exact Hstart |].
  eapply fin_upperbound_trans.
  - exact Hstart.
  - apply IH. exact Htail.
Qed.

Lemma fin_nonincreasing_index :
  forall fin_l l i j,
    fin_nonincreasing fin_l l ->
    0 <= i /\ i < j /\ j < Zlength l ->
    Znth (Znth i l 0) fin_l 0 >= Znth (Znth j l 0) fin_l 0.
Proof.
  intros fin_l l.
  induction l as [|x l IH]; intros i j Hinc [Hi [Hij Hj]].
  - rewrite Zlength_nil in Hj; lia.
  - destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + subst i.
      rewrite Znth0_cons.
      rewrite Znth_cons by lia.
      simpl in Hinc.
      pose proof (fin_nonincreasing_aux_upperbound_start fin_l l x Hinc) as Hupper.
      apply fin_upperbound_index; [exact Hupper |].
      rewrite Zlength_cons in Hj.
      lia.
    + rewrite !Znth_cons by lia.
      apply IH.
      * destruct l as [|y l']; simpl in *; [lia | tauto].
      * rewrite Zlength_cons in Hj.
        lia.
Qed.

Definition phase2_order_spec (fin_l order_l : list Z) (n : Z) : Prop :=
  Zlength fin_l = n /\
  fin_values_in_int_range fin_l n /\
  list_prefix_no_dup n fin_l /\
  fin_sequence_covers_range n fin_l /\
  (forall i, 0 <= i < n -> Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) /\
  order_entries_in_range n order_l /\
  order_covers_range n order_l /\
  list_prefix_no_dup n order_l.

Definition phase2_sequence_order_spec
    (fin_l order_l : list Z) (n : Z) : Prop :=
  Zlength fin_l = n /\
  Zlength order_l = n /\
  order_l = rev fin_l.

Lemma phase2_order_spec_from_loop :
  forall fin_l order_l n,
    Zlength fin_l = n ->
    fin_values_in_int_range fin_l n ->
    list_prefix_no_dup n fin_l ->
    fin_sequence_covers_range n fin_l ->
    (forall i, 0 <= i < n -> Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) ->
    order_entries_in_range n order_l ->
    order_covers_range n order_l ->
    list_prefix_no_dup n order_l ->
    phase2_order_spec fin_l order_l n.
Proof.
  intros fin_l order_l n Hfin_len Hfin Hnodup Hcover Hrev Hrange
    Horder_cover Horder_nodup.
  unfold phase2_order_spec.
  split; [exact Hfin_len |].
  split; [exact Hfin |].
  split; [exact Hnodup |].
  split; [exact Hcover |].
  split; [exact Hrev |].
  split; [exact Hrange |].
  split; [exact Horder_cover | exact Horder_nodup].
Qed.

Lemma base_order_Znth :
  forall n i,
    0 <= i < n ->
    Znth i (base_order n) 0 = i.
Proof.
  intros n i Hi.
  unfold base_order, Znth.
  apply (@nth_error_nth Z
    (map Z.of_nat (seq 0 (Z.to_nat n))) (Z.to_nat i) i 0).
  rewrite nth_error_map, nth_error_seq.
  replace (Nat.ltb (Z.to_nat i) (Z.to_nat n)) with true.
  - simpl. f_equal. rewrite Z2Nat.id by lia. lia.
  - symmetry. apply Nat.ltb_lt. lia.
Qed.

Lemma order_init_prefix_full_base_order :
  forall n order_l,
    0 <= n ->
    Zlength order_l = n ->
    order_init_prefix n n order_l ->
    order_l = base_order n.
Proof.
  intros n order_l Hn Hlen Hinit.
  apply (proj2 (list_eq_ext order_l (base_order n) 0)).
  split.
  - rewrite Hlen.
    unfold base_order.
    rewrite Zlength_correct, length_map, length_seq.
    lia.
  - intros i Hi.
    unfold order_init_prefix in Hinit.
    destruct Hinit as [_ Hprefix].
    rewrite Hprefix by lia.
    rewrite base_order_Znth by lia.
    reflexivity.
Qed.

Lemma phase2_order_spec_order_spec :
  forall fin_l order_l n,
    phase2_order_spec fin_l order_l n ->
    order_spec fin_l order_l n.
Proof.
  intros fin_l order_l n Hspec.
  unfold phase2_order_spec in Hspec.
  destruct Hspec as [_ [Hfin [_ [_ [_ [Hrange _]]]]]].
  split; [exact Hfin |].
  exact Hrange.
Qed.

Lemma phase2_order_spec_covers_range :
  forall fin_l order_l n,
    phase2_order_spec fin_l order_l n ->
    order_covers_range n order_l.
Proof.
  intros fin_l order_l n Hspec v Hv.
  unfold phase2_order_spec in Hspec.
  destruct Hspec as [_ [_ [_ [_ [_ [_ [Hcover _]]]]]]].
  apply Hcover; exact Hv.
Qed.

Lemma order_init_prefix_covers_range :
  forall n order_l,
    order_init_prefix n n order_l ->
    order_covers_range n order_l.
Proof.
  intros n order_l Hinit v Hv.
  unfold order_init_prefix in Hinit.
  destruct Hinit as [_ Hprefix].
  exists v.
  split; [exact Hv | apply Hprefix; exact Hv].
Qed.

Lemma order_covers_range_all_marked :
  forall n order_l vis_l,
    order_covers_range n order_l ->
    (forall i, 0 <= i < n -> Znth (Znth i order_l 0) vis_l 0 <> 0) ->
    forall v, 0 <= v < n -> Znth v vis_l 0 <> 0.
Proof.
  intros n order_l vis_l Hcover Hmarked v Hv.
  destruct (Hcover v Hv) as [i [Hi Horder]].
  rewrite <- Horder.
  apply Hmarked; exact Hi.
Qed.

Definition all_order_prefix_marked (n k : Z) (order_l vis_l : list Z) : Prop :=
  forall i, 0 <= i < k -> Znth (Znth i order_l 0) vis_l 0 <> 0.

Definition mutually_reachable (g : AdjGraph) (u v : Z) : Prop :=
  reachable g u v /\ reachable g v u.

Definition finish_sequence_position_before
    (fin_l : list Z) (n root c : Z) : Prop :=
  exists root_pos c_pos,
    (0 <= root_pos < n)%Z /\
    (0 <= c_pos < n)%Z /\
    Znth root_pos fin_l 0 = root /\
    Znth c_pos fin_l 0 = c /\
    root_pos < c_pos.

Definition phase1_order_graph
    (g : AdjGraph) (fin_l : list Z) (n : Z) : Prop :=
  forall root v,
    0 <= root < n ->
    0 <= v < n ->
    reachable g root v ->
    ~ reachable g v root ->
    exists c,
      0 <= c < n /\
      mutually_reachable g v c /\
      finish_sequence_position_before fin_l n root c.

Definition phase1_finished_visited (st : KSt) : Prop :=
  forall v, @Kosaraju.visited1 Z st v -> @Kosaraju.finish Z st v <> 0%nat.

Lemma count_pred_all_true :
  forall {A : Type} (P : A -> Prop) (l : list A),
    (forall x, In x l -> P x) ->
    @count_pred A P l = length l.
Proof.
  intros A P l Hall.
  induction l as [|x xs IH]; simpl; [reflexivity|].
  destruct (excluded_middle_informative (P x)) as [_ | Hnot].
  - f_equal. apply IH. intros y Hy. apply Hall. right; exact Hy.
  - exfalso. apply Hnot. apply Hall. left; reflexivity.
Qed.

Lemma dfs_finish_preserves_phase1_finished_visited :
  forall g s0 u,
    AdjGraphValid g ->
    @Kosaraju.Phase1_R AdjGraph Z (Z * Z) KG g s0 ->
    phase1_finished_visited s0 ->
    ~ @Kosaraju.visited1 Z s0 u ->
    adj_vvalid g u ->
    Hoare (fun st => st = s0) (dfs_finish g u)
      (fun _ s' => phase1_finished_visited s').
Proof.
  intros g s0 u Hvalid HR Hfinished Hnot_u Hvalid_u.
  unfold dfs_finish.
  destruct HR as [Hclosed [Hinv _]].
  eapply Hoare_imp_post.
  - eapply (@DFS_finish_phase1_plus AdjGraph Z (Z * Z) KG g Hvalid);
      eauto.
  - intros _ s' [Hframe [_ Hstrict]].
    unfold phase1_finished_visited in *.
    destruct Hframe as [_ [Hsub [Hfin_old _]]].
    intros v Hvis.
    destruct (classic (@Kosaraju.visited1 Z s0 v)) as [Hvis_old | Hvis_new].
    + rewrite (Hfin_old v Hvis_old).
      apply Hfinished; exact Hvis_old.
    + specialize (Hstrict v Hvis Hvis_new).
      lia.
Qed.

Lemma kosaraju_finish_schedule_phase1_done_aux :
  forall g (root_at : nat -> Z) start fuel s0,
    AdjGraphValid g ->
    (forall i, (start <= i < start + fuel)%nat ->
      adj_vvalid g (root_at i)) ->
    @Kosaraju.Phase1_R AdjGraph Z (Z * Z) KG g s0 ->
    phase1_finished_visited s0 ->
    Hoare (fun st => st = s0)
      (@kosaraju_finish_schedule AdjGraph Z (Z * Z) KG g root_at start fuel)
      (fun _ s' =>
        @Kosaraju.Phase1_R AdjGraph Z (Z * Z) KG g s' /\
        phase1_finished_visited s' /\
        @Kosaraju.visited1 Z s0 ⊆ @Kosaraju.visited1 Z s' /\
        forall i, (start <= i < start + fuel)%nat ->
          @Kosaraju.visited1 Z s' (root_at i)).
Proof.
  intros g root_at start fuel.
  revert start.
  induction fuel as [|fuel IH]; intros start s0 Hvalid Hvalid_roots HR Hfinished.
  - rewrite kosaraju_finish_schedule_done.
    apply Hoare_ret. intros s' Hs'. subst s'.
    split; [exact HR |].
    split; [exact Hfinished |].
    split; [intros x Hx; exact Hx |].
    intros i Hi. lia.
  - rewrite kosaraju_finish_schedule_step.
    unfold if_else.
    apply Hoare_choice.
    + eapply Hoare_bind.
      * apply Hoare_assumeS.
      * intros [].
        apply Hoare_normalize.
        intros s_skip [Hs_skip Hroot_done].
        subst s_skip.
        eapply Hoare_imp_post.
        -- eapply IH.
           ++ exact Hvalid.
           ++ intros i Hi. apply Hvalid_roots. lia.
           ++ exact HR.
           ++ exact Hfinished.
        -- intros _ s' [HR' [Hfinished' [Hsub Hdone]]].
           split; [exact HR' |].
           split; [exact Hfinished' |].
           split; [exact Hsub |].
           intros i Hi.
           destruct (Nat.eq_dec i start) as [-> | Hne].
           ++ apply Hsub. exact Hroot_done.
           ++ apply Hdone. lia.
    + eapply Hoare_bind.
      * apply Hoare_assumeS.
      * intros [].
        apply Hoare_normalize.
        intros s_dfs [Hs_dfs Hroot_not].
        subst s_dfs.
        eapply Hoare_bind.
        -- apply Hoare_conj.
           ++ eapply (@DFS_finish_preserves_Phase1_R AdjGraph Z (Z * Z) KG g Hvalid).
              ** exact HR.
              ** exact Hroot_not.
              ** change (adj_vvalid g (root_at start)).
                 apply Hvalid_roots. lia.
           ++ eapply dfs_finish_preserves_phase1_finished_visited.
              ** exact Hvalid.
              ** exact HR.
              ** exact Hfinished.
              ** exact Hroot_not.
              ** apply Hvalid_roots. lia.
        -- intros [].
           apply Hoare_normalize.
           intros s1 [[HR1 [Hsub01 Hroot_vis]] Hfinished1].
           eapply Hoare_imp_post.
           ++ eapply IH.
              ** exact Hvalid.
              ** intros i Hi. apply Hvalid_roots. lia.
              ** exact HR1.
              ** exact Hfinished1.
           ++ intros _ s' [HR' [Hfinished' [Hsub1 Hdone]]].
              split; [exact HR' |].
              split; [exact Hfinished' |].
              split.
              ** intros x Hx. apply Hsub1. apply Hsub01. exact Hx.
              ** intros i Hi.
                 destruct (Nat.eq_dec i start) as [-> | Hne].
                 --- apply Hsub1. exact Hroot_vis.
                 --- apply Hdone. lia.
Qed.

Lemma dfs_finish_schedule_phase1_done_R :
  forall g n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    Hoare (fun st => st = @Kosaraju.init_st Z)
      (dfs_finish_schedule g 0 n)
      (fun _ st =>
        @Kosaraju.Phase1_R AdjGraph Z (Z * Z) KG g st /\
        (forall v, 0 <= v < n -> @Kosaraju.visited1 Z st v) /\
        phase1_finished_visited st).
Proof.
  intros g n Hvalid Hverts Hn.
  unfold dfs_finish_schedule.
  change (Z.to_nat 0) with 0%nat.
  eapply Hoare_imp_post.
  - eapply kosaraju_finish_schedule_phase1_done_aux.
    + exact Hvalid.
    + intros i Hi.
      change (adj_vvalid g (Z.of_nat i)).
      unfold adj_vvalid.
      rewrite Hverts.
      rewrite Nat.add_0_l in Hi.
      split; [apply Nat2Z.is_nonneg |].
      rewrite <- (Z2Nat.id n) by lia.
      apply (proj1 (Nat2Z.inj_lt i (Z.to_nat n))).
      exact (proj2 Hi).
    + unfold Kosaraju.Phase1_R.
      split.
      * unfold Kosaraju.ReachRevClosed, Kosaraju.init_st.
        intros v w Hfalse _. contradiction.
      * split.
        -- apply DFSFinishInv_init.
        -- unfold Kosaraju.init_st.
           intros a b Hfalse _ _ _. contradiction.
    + unfold phase1_finished_visited, Kosaraju.init_st.
      intros v Hfalse. contradiction.
  - intros _ st [HR [Hfinished [_ Hdone]]].
    split; [exact HR |].
    split; [| exact Hfinished].
    intros v Hv.
    specialize (Hdone (Z.to_nat v)).
    rewrite Nat.add_0_l in Hdone.
    rewrite Z2Nat.id in Hdone by lia.
    apply Hdone.
    split.
    + apply (proj1 (Z2Nat.inj_le 0 v ltac:(lia) ltac:(lia))); lia.
    + apply (proj1 (Z2Nat.inj_lt v n ltac:(lia) ltac:(lia))); lia.
Qed.

Lemma phase1_sequence_refinement_done_state :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    exists st,
      pre_dfs1_sequence g radj_col_l radj_row_l vis_l fin_l timer_v st /\
      @Kosaraju.Phase1_R AdjGraph Z (Z * Z) KG g st /\
      (forall v, 0 <= v < n -> @Kosaraju.visited1 Z st v) /\
      phase1_finished_visited st.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href.
  unfold phase1_sequence_refinement in Href.
  destruct Href as [_ [_ Hsafe]].
  unfold safeExec, safe, result_state in Hsafe.
  destruct Hsafe as [st [Hpre [_ Hpost]]].
  assert (Hret : MonadErr.nrm (dfs_finish_schedule g n (n - n)) st tt st).
  { replace (n - n) with 0 by lia.
    rewrite dfs_finish_schedule_done.
    cbv [MonadErr.ret MonadErr.nrm_nrm].
    exact (conj eq_refl eq_refl). }
  specialize (Hpost tt st Hret).
  destruct Hpost as [st0 [Hinit Hfull]].
  destruct Hinit as [Hst0 _].
  subst st0.
  pose proof (dfs_finish_schedule_phase1_done_R g n Hvalid Hverts Hn)
    as Hdone.
  destruct Hdone as [Hdone _].
  specialize (Hdone tt (@Kosaraju.init_st Z) st eq_refl Hfull).
  destruct Hdone as [HR [Hall Hfinished]].
  exists st.
  split; [exact Hpre |].
  split; [exact HR |].
  split; [exact Hall | exact Hfinished].
Qed.

Lemma phase1_sequence_refinement_done_timer :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    timer_v = n.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href.
  destruct (phase1_sequence_refinement_done_state
    g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href) as
    [st [Hpre [HR [Hall Hfinished]]]].
  destruct Hpre as [_ [_ Hseq]].
  unfold fin_sequence_rep in Hseq.
  destruct Hseq as [Htbounds [_ [Htimer _]]].
  destruct HR as [_ [Hinv _]].
  pose proof (@DFSFinishInv_finished_count AdjGraph Z (Z * Z) KG g st Hinv)
    as Hfc.
  unfold Kosaraju.FinishedCount, Kosaraju.cardV in Hfc.
  change (@Kosaraju.timer Z st =
    count_pred (fun v : Z => @Kosaraju.finish Z st v <> 0%nat)
      (bijective_listV g)) in Hfc.
  rewrite Htimer in Hfc.
  assert (Hcount :
    count_pred (fun v : Z => @Kosaraju.finish Z st v <> 0%nat)
      (bijective_listV g) = length (bijective_listV g)).
  {
    apply count_pred_all_true.
    intros v Hin.
    pose proof (bijective_vertices g Hvalid v) as Hbij.
    assert (Hvvalid : vvalid g v) by (apply Hbij; exact Hin).
    change (adj_vvalid g v) in Hvvalid.
    unfold adj_vvalid in Hvvalid.
    apply Hfinished.
    apply Hall.
    rewrite <- Hverts.
    exact Hvvalid.
  }
  rewrite Hcount in Hfc.
  pose proof (AdjGraph_bijective_listV_perm g Hvalid) as Hperm.
  apply Permutation_length in Hperm.
  unfold base_order in Hperm.
  rewrite Hperm, length_map, length_seq in Hfc.
  apply Z2Nat.inj; lia.
Qed.

Lemma fin_sequence_rep_prefix_no_dup :
  forall g fin_l timer_v st,
    fin_sequence_rep g fin_l timer_v st ->
    list_prefix_no_dup timer_v fin_l.
Proof.
  intros g fin_l timer_v st Hseq i j Hi Hj Heq.
  unfold fin_sequence_rep in Hseq.
  destruct Hseq as [_ [_ [_ [Hentry _]]]].
  destruct (Hentry i Hi) as [_ Hfinish_i].
  destruct (Hentry j Hj) as [_ Hfinish_j].
  assert (Heq_nat : S (Z.to_nat i) = S (Z.to_nat j)).
  {
    rewrite <- Hfinish_i.
    rewrite <- Hfinish_j.
    rewrite Heq.
    reflexivity.
  }
  injection Heq_nat as Heq_nat.
  apply Z2Nat.inj; lia.
Qed.

Lemma phase1_sequence_refinement_done_fin_prefix_no_dup :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    list_prefix_no_dup n fin_l.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href.
  destruct (phase1_sequence_refinement_done_state
    g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href) as [st [Hpre _]].
  assert (Htimer : timer_v = n).
  { eapply phase1_sequence_refinement_done_timer; eauto. }
  subst timer_v.
  destruct Hpre as [_ [_ Hseq]].
  eapply fin_sequence_rep_prefix_no_dup; eauto.
Qed.

Lemma phase1_sequence_refinement_done_fin_range :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    forall i, 0 <= i < n -> 0 <= Znth i fin_l 0 < n.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href i Hi.
  destruct (phase1_sequence_refinement_done_state
    g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href) as [st [Hpre _]].
  assert (Htimer : timer_v = n).
  { eapply phase1_sequence_refinement_done_timer; eauto. }
  destruct Hpre as [_ [_ Hseq]].
  unfold fin_sequence_rep in Hseq.
  destruct Hseq as [_ [_ [_ [Hentry _]]]].
  rewrite <- Htimer in Hi.
  destruct (Hentry i Hi) as [Hrange _].
  rewrite Hverts in Hrange.
  exact Hrange.
Qed.

Lemma phase1_sequence_refinement_done_fin_values :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    n <= INT_MAX ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    fin_values_in_int_range fin_l n.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Hint Href i Hi.
  pose proof (phase1_sequence_refinement_done_fin_range
    g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href i Hi) as Hrange.
  lia.
Qed.

Lemma phase1_sequence_refinement_done_fin_covers_range :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    fin_sequence_covers_range n fin_l.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href v Hv.
  destruct (phase1_sequence_refinement_done_state
    g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href) as
    [st [Hpre [_ [Hall Hfinished]]]].
  assert (Htimer : timer_v = n).
  { eapply phase1_sequence_refinement_done_timer; eauto. }
  destruct Hpre as [_ [_ Hseq]].
  unfold fin_sequence_rep in Hseq.
  destruct Hseq as [_ [_ [_ [_ [Hcomplete _]]]]].
  assert (Hvvalid : 0 <= v < adj_verts g) by (rewrite Hverts; exact Hv).
  assert (Hdone : @Kosaraju.finish Z st v <> 0%nat).
  { apply Hfinished. apply Hall. exact Hv. }
  destruct (Hcomplete v Hvvalid Hdone) as [t [Ht Hfin]].
  exists t.
  split; [rewrite <- Htimer; exact Ht | exact Hfin].
Qed.

Lemma phase1_sequence_refinement_done_all_vis1 :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    forall v, 0 <= v < n -> Znth v vis_l 0 <> 0.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href v Hv.
  destruct (phase1_sequence_refinement_done_state
    g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href) as [st [Hpre [_ [Hall _]]]].
  destruct Hpre as [Hvis _].
  apply (proj1 (Hvis v ltac:(rewrite Hverts; exact Hv))).
  apply Hall. exact Hv.
Qed.

Lemma phase1_sequence_refinement_done_order_graph :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    phase1_order_graph g fin_l n.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href root v Hroot Hv Hreach Hnot.
  destruct (phase1_sequence_refinement_done_state
    g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
    Hvalid Hverts Hn Href) as
    [st [Hpre [HR [Hall Hfinished]]]].
  assert (Htimer : timer_v = n).
  { eapply phase1_sequence_refinement_done_timer; eauto. }
  destruct Hpre as [_ [_ Hseq]].
  unfold fin_sequence_rep in Hseq.
  destruct Hseq as [_ [_ [_ [Hentry [Hcomplete _]]]]].
  destruct HR as [_ [_ Hphase]].
  assert (Hreach_rev : @Kosaraju.reachable_rev AdjGraph Z (Z * Z) KG g v root).
  { unfold Kosaraju.reachable_rev, SCC.reachable_rev. exact Hreach. }
  assert (Hnot_rev : ~ @Kosaraju.reachable_rev AdjGraph Z (Z * Z) KG g root v).
  { unfold Kosaraju.reachable_rev, SCC.reachable_rev. exact Hnot. }
  destruct (Hphase v root (Hall v Hv) (Hall root Hroot)
    Hreach_rev Hnot_rev) as [c [Hmut Hlt]].
  assert (Hcvalid : 0 <= c < n).
  { destruct (Z.eq_dec c v) as [-> | Hneq]; [exact Hv |].
    destruct Hmut as [Hvc _].
    assert (Hvneqc : v <> c) by (intro Heq; apply Hneq; symmetry; exact Heq).
    pose proof (reachable_basic.reachable_vvalid (g:=g) v c Hvneqc Hvc)
      as [_ Hcvalid].
    change (adj_vvalid g c) in Hcvalid.
    unfold adj_vvalid in Hcvalid.
    rewrite Hverts in Hcvalid. exact Hcvalid. }
  assert (Hroot_done : @Kosaraju.finish Z st root <> 0%nat).
  { apply Hfinished. apply Hall. exact Hroot. }
  assert (Hc_done : @Kosaraju.finish Z st c <> 0%nat).
  { apply Hfinished. apply Hall. exact Hcvalid. }
  assert (Hroot_valid : 0 <= root < adj_verts g) by (rewrite Hverts; exact Hroot).
  assert (Hc_valid : 0 <= c < adj_verts g) by (rewrite Hverts; exact Hcvalid).
  destruct (Hcomplete root Hroot_valid Hroot_done) as [root_pos [Hrpos Hroot_pos]].
  destruct (Hcomplete c Hc_valid Hc_done) as [c_pos [Hcpos Hc_pos]].
  destruct (Hentry root_pos Hrpos) as [_ Hroot_finish].
  destruct (Hentry c_pos Hcpos) as [_ Hc_finish].
  rewrite Hroot_pos in Hroot_finish.
  rewrite Hc_pos in Hc_finish.
  exists c.
  split; [exact Hcvalid |].
  split.
  - unfold mutually_reachable.
    unfold Kosaraju.mutually_reachable, SCC.mutually_reachable in Hmut.
    exact Hmut.
  - unfold finish_sequence_position_before.
    exists root_pos, c_pos.
    split; [rewrite <- Htimer; exact Hrpos |].
    split; [rewrite <- Htimer; exact Hcpos |].
    split; [exact Hroot_pos |].
    split; [exact Hc_pos |].
    assert (Hnat_lt : (Z.to_nat root_pos < Z.to_nat c_pos)%nat) by lia.
    apply (proj2 (Z2Nat.inj_lt root_pos c_pos ltac:(lia) ltac:(lia))).
    exact Hnat_lt.
Qed.

Lemma phase2_order_entries_from_reverse :
  forall fin_l order_l n,
    (forall i, 0 <= i < n -> 0 <= Znth i fin_l 0 < n) ->
    (forall i, 0 <= i < n -> Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) ->
    order_entries_in_range n order_l.
Proof.
  intros fin_l order_l n Hfin_range Hrev i Hi.
  rewrite Hrev by exact Hi.
  apply Hfin_range. lia.
Qed.

Lemma phase2_order_covers_from_reverse :
  forall fin_l order_l n,
    fin_sequence_covers_range n fin_l ->
    (forall i, 0 <= i < n -> Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) ->
    order_covers_range n order_l.
Proof.
  intros fin_l order_l n Hfin_cover Hrev v Hv.
  destruct (Hfin_cover v Hv) as [t [Ht Hfin]].
  exists (n - 1 - t).
  split; [lia |].
  rewrite Hrev by lia.
  replace (n - 1 - (n - 1 - t)) with t by lia.
  exact Hfin.
Qed.

Lemma phase2_order_no_dup_from_reverse :
  forall fin_l order_l n,
    list_prefix_no_dup n fin_l ->
    (forall i, 0 <= i < n -> Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) ->
    list_prefix_no_dup n order_l.
Proof.
  intros fin_l order_l n Hfin_nodup Hrev i j Hi Hj Heq.
  assert (Hpos_eq : n - 1 - i = n - 1 - j).
  {
    eapply Hfin_nodup; try lia.
    rewrite <- !Hrev by lia.
    exact Heq.
  }
  lia.
Qed.

Lemma phase2_order_spec_from_phase1_done :
  forall g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v order_l n,
    AdjGraphValid g ->
    adj_verts g = n ->
    0 <= n ->
    n <= INT_MAX ->
    phase1_sequence_refinement g radj_col_l radj_row_l vis_l fin_l
      vis0_l fin0_l timer_v n n ->
    (forall i, 0 <= i < n ->
      Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) ->
    phase2_order_spec fin_l order_l n.
Proof.
  intros g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v order_l n
    Hvalid Hverts Hn Hint Href Hrev.
  assert (Hfin_values : fin_values_in_int_range fin_l n).
  { eapply phase1_sequence_refinement_done_fin_values; eauto. }
  assert (Hfin_range :
    forall i, 0 <= i < n -> 0 <= Znth i fin_l 0 < n).
  { eapply phase1_sequence_refinement_done_fin_range; eauto. }
  assert (Hfin_nodup : list_prefix_no_dup n fin_l).
  { eapply phase1_sequence_refinement_done_fin_prefix_no_dup; eauto. }
  assert (Hfin_cover : fin_sequence_covers_range n fin_l).
  { eapply phase1_sequence_refinement_done_fin_covers_range; eauto. }
  unfold phase2_order_spec.
  split.
  - destruct (phase1_sequence_refinement_done_state
      g radj_col_l radj_row_l vis_l fin_l vis0_l fin0_l timer_v n
      Hvalid Hverts Hn Href) as [st [Hpre _]].
    destruct Hpre as [_ [_ Hseq]].
    unfold fin_sequence_rep in Hseq.
    destruct Hseq as [_ [Hlen _]].
    rewrite Hverts in Hlen.
    exact Hlen.
  - split; [exact Hfin_values |].
    split; [exact Hfin_nodup |].
    split; [exact Hfin_cover |].
    split; [exact Hrev |].
    split.
    + eapply phase2_order_entries_from_reverse; eauto.
    + split.
      * eapply phase2_order_covers_from_reverse; eauto.
      * eapply phase2_order_no_dup_from_reverse; eauto.
Qed.

Definition sid_correct_on_marked
    (g : AdjGraph) (n : Z) (vis_l sid_l : list Z) : Prop :=
  (forall u, 0 <= u < n ->
      Znth u vis_l 0 <> 0 ->
    forall v, 0 <= v < n ->
      Znth v vis_l 0 <> 0 ->
      ((Znth u sid_l 0 = Znth v sid_l 0 -> reachable g u v /\ reachable g v u) /\
       (reachable g u v /\ reachable g v u -> Znth u sid_l 0 = Znth v sid_l 0))) /\
  (forall u, 0 <= u < n ->
      Znth u vis_l 0 <> 0 ->
      0 <= Znth u sid_l 0 < n /\
      Znth (Znth u sid_l 0) vis_l 0 <> 0 /\
      Znth (Znth u sid_l 0) sid_l 0 = Znth u sid_l 0).

Definition sid_labels_in_order_prefix
    (n k : Z) (order_l vis_l sid_l : list Z) : Prop :=
  forall v, 0 <= v < n ->
    Znth v vis_l 0 <> 0 ->
    exists i, 0 <= i < k /\ Znth v sid_l 0 = Znth i order_l 0.

Definition phase2_prefix_complete
    (g : AdjGraph) (n k : Z) (order_l vis_l : list Z) : Prop :=
  forall i w,
    0 <= i < k ->
    0 <= w < n ->
    mutually_reachable g (Znth i order_l 0) w ->
    Znth w vis_l 0 <> 0.

Definition dfs2_phase2_post
    (g : AdjGraph) (n : Z)
    (vis_l sid_l vis_l_ sid_l_ : list Z) (root : Z) : Prop :=
  (forall w, 0 <= w < n ->
     Znth w vis_l 0 <> 0 ->
     Znth w vis_l_ 0 <> 0 /\ Znth w sid_l_ 0 = Znth w sid_l 0) /\
  (forall w, 0 <= w < n ->
     Znth w vis_l_ 0 <> 0 ->
     Znth w vis_l 0 = 0 ->
     Znth w sid_l_ 0 = root /\ mutually_reachable g root w) /\
  (forall w, 0 <= w < n ->
     mutually_reachable g root w ->
     Znth w vis_l_ 0 <> 0).

Lemma csr_wf2_sid_replace_Znth :
  forall g fc fr vis sid root value,
    csr_wf2 g fc fr vis sid ->
    0 <= root < adj_verts g ->
    csr_wf2 g fc fr vis (replace_Znth root value sid).
Proof.
  intros g fc fr vis sid root value Hwf Hroot.
  unfold csr_wf2 in *.
  destruct Hwf as [Hvalid [Hrow [Hvis [Hsid [Hm [Hlo [Hhi [Hcol [Hroword Hcap]]]]]]]]].
  split; [exact Hvalid|].
  split; [exact Hrow|].
  split; [exact Hvis|].
  split; [rewrite Zlength_replace_Znth; exact Hsid|].
  split; [exact Hm|].
  split; [exact Hlo|].
  split; [exact Hhi|].
  split; [exact Hcol|].
  split; [exact Hroword|exact Hcap].
Qed.

Lemma csr_wf2_vis_sid_replace_Znth :
  forall g fc fr vis sid u vis_value sid_value,
    csr_wf2 g fc fr vis sid ->
    0 <= u < adj_verts g ->
    csr_wf2 g fc fr
      (replace_Znth u vis_value vis)
      (replace_Znth u sid_value sid).
Proof.
  intros g fc fr vis sid u vis_value sid_value Hwf Hu.
  unfold csr_wf2 in *.
  destruct Hwf as
    [Hvalid [Hrow [Hvis [Hsid [Hm [Hlo [Hhi [Hcol [Hroword Hcap]]]]]]]]].
  split; [exact Hvalid|].
  split; [exact Hrow|].
  split; [rewrite Zlength_replace_Znth; exact Hvis|].
  split; [rewrite Zlength_replace_Znth; exact Hsid|].
  split; [exact Hm|].
  split; [exact Hlo|].
  split; [exact Hhi|].
  split; [exact Hcol|].
  split; [exact Hroword|exact Hcap].
Qed.

Lemma sid_labels_in_order_prefix_unvisited_sid_update :
  forall n k order_l vis_l sid_l root value,
    Zlength sid_l = n ->
    0 <= root < n ->
    Znth root vis_l 0 = 0 ->
    sid_labels_in_order_prefix n k order_l vis_l sid_l ->
    sid_labels_in_order_prefix n k order_l vis_l (replace_Znth root value sid_l).
Proof.
  unfold sid_labels_in_order_prefix.
  intros n k order_l vis_l sid_l root value Hsid_len Hroot Hroot_zero Hlabels v Hv Hvis.
  destruct (Hlabels v Hv Hvis) as [i [Hi Hsid]].
  exists i. split; [exact Hi|].
  destruct (Z.eq_dec v root) as [-> | Hne].
  - congruence.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hsid_len; lia).
    exact Hsid.
Qed.

Lemma sid_correct_on_marked_unvisited_sid_update :
  forall g n vis_l sid_l root value,
    Zlength sid_l = n ->
    0 <= root < n ->
    Znth root vis_l 0 = 0 ->
    sid_correct_on_marked g n vis_l sid_l ->
    sid_correct_on_marked g n vis_l (replace_Znth root value sid_l).
Proof.
  intros g n vis_l sid_l root value Hsid_len Hroot Hroot_zero Hsid.
  unfold sid_correct_on_marked in *.
  destruct Hsid as [Hpair Hrep].
  split.
  - intros u Hu Huvis v Hv Hvvis.
    assert (Hu_ne : u <> root) by (intro H; subst u; congruence).
    assert (Hv_ne : v <> root) by (intro H; subst v; congruence).
    rewrite Znth_replace_Znth_Diff by (try rewrite Hsid_len; lia).
    rewrite Znth_replace_Znth_Diff by (try rewrite Hsid_len; lia).
    apply Hpair; assumption.
  - intros u Hu Huvis.
    assert (Hu_ne : u <> root) by (intro H; subst u; congruence).
    rewrite Znth_replace_Znth_Diff by (try rewrite Hsid_len; lia).
    destruct (Hrep u Hu Huvis) as [Hrng [Hrvis Hrself]].
    assert (Hr_ne : Znth u sid_l 0 <> root).
    { intro H; subst root; congruence. }
    split; [exact Hrng|].
    split; [exact Hrvis|].
    rewrite Znth_replace_Znth_Diff by (try rewrite Hsid_len; lia).
    exact Hrself.
Qed.

Lemma all_order_prefix_marked_step :
  forall n k order_l vis_l root,
    all_order_prefix_marked n k order_l vis_l ->
    root = Znth k order_l 0 ->
    Znth root vis_l 0 <> 0 ->
    all_order_prefix_marked n (k + 1) order_l vis_l.
Proof.
  intros n k order_l vis_l root Hprefix Hroot Hroot_vis i Hi.
  destruct (Z.eq_dec i k) as [Hik | Hik].
  - subst i. rewrite <- Hroot. exact Hroot_vis.
  - apply Hprefix. lia.
Qed.

Lemma all_order_prefix_marked_zero :
  forall n order_l vis_l,
    all_order_prefix_marked n 0 order_l vis_l.
Proof.
  unfold all_order_prefix_marked.
  intros n order_l vis_l i Hi.
  lia.
Qed.

Lemma phase2_prefix_complete_zero :
  forall g n order_l vis_l,
    phase2_prefix_complete g n 0 order_l vis_l.
Proof.
  unfold phase2_prefix_complete.
  intros g n order_l vis_l i w Hi _ _.
  lia.
Qed.

Lemma mutually_reachable_sym_local :
  forall g u v,
    mutually_reachable g u v ->
    mutually_reachable g v u.
Proof.
  unfold mutually_reachable.
  intros g u v [Huv Hvu].
  split; assumption.
Qed.

Lemma mutually_reachable_trans_local :
  forall g u v w,
    mutually_reachable g u v ->
    mutually_reachable g v w ->
    mutually_reachable g u w.
Proof.
  unfold mutually_reachable.
  intros g u v w [Huv Hvu] [Hvw Hwv].
  split.
  - eapply reachable_trans; eauto.
  - eapply reachable_trans; eauto.
Qed.

Lemma phase2_order_index_before :
  forall fin_l order_l n k j root c,
    phase2_order_spec fin_l order_l n ->
    0 <= k < n ->
    0 <= j < n ->
    root = Znth k order_l 0 ->
    c = Znth j order_l 0 ->
    finish_sequence_position_before fin_l n root c ->
    j < k.
Proof.
  intros fin_l order_l n k j root c Hord Hk Hj Hroot Hc Hbefore.
  unfold phase2_order_spec in Hord.
  destruct Hord as
    [Hfin_len [Hfin_values [Hfin_nodup [Hfin_cover
    [Hrev [Hrange [Hcover Horder_nodup]]]]]]].
  unfold finish_sequence_position_before in Hbefore.
  destruct Hbefore as
    [root_pos [c_pos
    [Hroot_pos_range [Hc_pos_range [Hroot_pos [Hc_pos Hpos_lt]]]]]].
  assert (Hroot_eq_pos : root_pos = n - 1 - k).
  {
    apply Hfin_nodup; try lia.
    rewrite Hroot_pos, Hroot.
    rewrite Hrev by exact Hk.
    reflexivity.
  }
  assert (Hc_eq_pos : c_pos = n - 1 - j).
  {
    apply Hfin_nodup; try lia.
    rewrite Hc_pos, Hc.
    rewrite Hrev by exact Hj.
    reflexivity.
  }
  lia.
Qed.

Lemma phase2_order_entry_range :
  forall fin_l order_l n i,
    phase2_order_spec fin_l order_l n ->
    0 <= i < n ->
    0 <= Znth i order_l 0 < n.
Proof.
  intros fin_l order_l n i Horder Hi.
  unfold phase2_order_spec in Horder.
  destruct Horder as [_ [_ [_ [_ [_ [Hrange _]]]]]].
  apply Hrange; exact Hi.
Qed.

Lemma phase2_unvisited_reachable_mutual :
  forall g fin_l order_l vis_l n k root v,
    phase1_order_graph g fin_l n ->
    phase2_order_spec fin_l order_l n ->
    all_order_prefix_marked n k order_l vis_l ->
    phase2_prefix_complete g n k order_l vis_l ->
    0 <= k < n ->
    root = Znth k order_l 0 ->
    0 <= v < n ->
    Znth v vis_l 0 = 0 ->
    reachable g root v ->
    mutually_reachable g root v.
Proof.
  intros g fin_l order_l vis_l n k root v
    Hphase Horder _Hmarked Hcomplete
    Hk Hroot Hv Hvis_zero Hreach.
  destruct (classic (reachable g v root)) as [Hback | Hnback].
  - split; assumption.
  - assert (Hroot_range : 0 <= root < n).
    { subst root. eapply phase2_order_entry_range; eassumption. }
    destruct (Hphase root v Hroot_range Hv Hreach Hnback) as
      (c & Hc_range & Hvc & Hbefore).
    pose proof (phase2_order_spec_covers_range fin_l order_l n Horder c Hc_range)
      as (j & Hj & Horder_j).
    assert (Hj_lt_k : j < k).
    {
      refine (phase2_order_index_before fin_l order_l n k j root c
        Horder Hk Hj Hroot _ Hbefore).
      symmetry; exact Horder_j.
    }
    assert (Hvis_v : Znth v vis_l 0 <> 0).
    {
      rewrite <- Horder_j in Hvc.
      eapply Hcomplete with (i := j); [ | exact Hv | ].
      - lia.
      - apply mutually_reachable_sym_local. exact Hvc.
    }
    congruence.
Qed.

Lemma phase2_prefix_complete_step_from_dfs2 :
  forall g n k order_l vis_l1 sid_l1 vis_l_ sid_l_ root,
    phase2_prefix_complete g n k order_l vis_l1 ->
    dfs2_phase2_post g n vis_l1 sid_l1 vis_l_ sid_l_ root ->
    root = Znth k order_l 0 ->
    0 <= k ->
    phase2_prefix_complete g n (k + 1) order_l vis_l_.
Proof.
  intros g n k order_l vis_l1 sid_l1 vis_l_ sid_l_ root
    Hprefix Hpost Hroot Hk.
  destruct Hpost as [Hold [_ Hroot_complete]].
  unfold phase2_prefix_complete in *.
  intros i w Hi Hw Hmut.
  destruct (Z.eq_dec i k) as [Hik | Hik].
  - subst i.
    rewrite <- Hroot in Hmut.
    apply Hroot_complete; assumption.
  - apply Hold.
    + exact Hw.
    + apply Hprefix with (i := i); try assumption.
      lia.
Qed.

Lemma sid_labels_in_order_prefix_step_from_dfs2 :
  forall g n k order_l vis_l sid_l vis_l_ sid_l_ root,
    sid_labels_in_order_prefix n k order_l vis_l sid_l ->
    dfs2_phase2_post g n vis_l sid_l vis_l_ sid_l_ root ->
    root = Znth k order_l 0 ->
    0 <= k ->
    sid_labels_in_order_prefix n (k + 1) order_l vis_l_ sid_l_.
Proof.
  unfold sid_labels_in_order_prefix.
  intros g n k order_l vis_l sid_l vis_l_ sid_l_ root
    Hlabels Hpost Hroot Hk v Hv Hvis_new.
  destruct Hpost as [Hold [Hnew _]].
  destruct (classic (Znth v vis_l 0 <> 0)) as [Hvis_old | Hnot_old].
  - destruct (Hlabels v Hv Hvis_old) as [i [Hi Hsid]].
    destruct (Hold v Hv Hvis_old) as [_ Hsid_keep].
    exists i. split; [lia |].
    rewrite Hsid_keep. exact Hsid.
  - assert (Hvis_zero : Znth v vis_l 0 = 0) by lia.
    destruct (Hnew v Hv Hvis_new Hvis_zero) as [Hsid_new _].
    exists k. split; [lia |].
    rewrite Hsid_new. exact Hroot.
Qed.

Lemma phase2_prefix_complete_step_from_marked :
  forall g n k order_l fin_l vis_l sid_l root,
    phase2_order_spec fin_l order_l n ->
    all_order_prefix_marked n k order_l vis_l ->
    phase2_prefix_complete g n k order_l vis_l ->
    sid_correct_on_marked g n vis_l sid_l ->
    sid_labels_in_order_prefix n k order_l vis_l sid_l ->
    root = Znth k order_l 0 ->
    0 <= k < n ->
    Znth root vis_l 0 <> 0 ->
    phase2_prefix_complete g n (k + 1) order_l vis_l.
Proof.
  intros g n k order_l fin_l vis_l sid_l root
    Horder Hmarked Hcomplete Hsid Hlabels Hroot Hk Hroot_vis.
  destruct Hsid as [Hsid_pair Hsid_rep].
  unfold phase2_prefix_complete in *.
  intros i w Hi Hw Hmut.
  destruct (Z.eq_dec i k) as [Hik | Hik].
  - subst i.
    subst root.
    destruct (Hlabels (Znth k order_l 0)) as [j [Hj Hroot_label]].
    + eapply phase2_order_entry_range; [exact Horder | exact Hk].
    + exact Hroot_vis.
    + assert (Hj_vis : Znth (Znth j order_l 0) vis_l 0 <> 0)
        by (apply Hmarked; exact Hj).
      assert (Hroot_range : 0 <= Znth k order_l 0 < n)
        by (eapply phase2_order_entry_range; [exact Horder | exact Hk]).
      assert (Hj_range : 0 <= Znth j order_l 0 < n)
        by (eapply phase2_order_entry_range; [exact Horder | lia]).
      pose proof (Hsid_pair (Znth k order_l 0) Hroot_range Hroot_vis
        (Znth j order_l 0) Hj_range Hj_vis) as [Hto _].
      destruct (Hsid_rep (Znth k order_l 0) Hroot_range Hroot_vis)
        as [_ [_ Hroot_rep]].
      assert (Hroot_j : mutually_reachable g (Znth k order_l 0) (Znth j order_l 0)).
      { apply Hto. rewrite <- Hroot_label. symmetry. exact Hroot_rep. }
      apply Hcomplete with (i := j); try assumption.
      eapply mutually_reachable_trans_local.
      * apply mutually_reachable_sym_local. exact Hroot_j.
      * exact Hmut.
  - apply Hcomplete with (i := i); try assumption; lia.
Qed.

Lemma phase2_prefix_complete_premark :
  forall g n k order_l vis_l root,
    phase2_prefix_complete g n k order_l vis_l ->
    Zlength vis_l = n ->
    0 <= root < n ->
    Znth root vis_l 0 = 0 ->
    phase2_prefix_complete g n k order_l (replace_Znth root 1 vis_l).
Proof.
  intros g n k order_l vis_l root Hprefix Hlen Hroot Hroot_zero.
  unfold phase2_prefix_complete in *.
  intros i w Hi Hw Hmut.
  destruct (Z.eq_dec w root) as [-> | Hne].
  - pose proof (Hprefix i root Hi Hroot Hmut) as Hroot_vis.
    congruence.
  - assert (Hroot_len : 0 <= root < Zlength vis_l) by (rewrite Hlen; exact Hroot).
    assert (Hw_len : 0 <= w < Zlength vis_l) by (rewrite Hlen; exact Hw).
    rewrite Znth_replace_Znth_Diff by (try exact Hroot_len; try exact Hw_len; lia).
    eapply Hprefix; eassumption.
Qed.

Lemma sid_correct_on_marked_empty :
  forall g n vis_l sid_l,
    (forall u, 0 <= u < n -> Znth u vis_l 0 = 0) ->
    sid_correct_on_marked g n vis_l sid_l.
Proof.
  unfold sid_correct_on_marked.
  intros g n vis_l sid_l Hzero.
  split.
  - intros u Hu Hvis.
    rewrite Hzero in Hvis by exact Hu.
    contradiction.
  - intros u Hu Hvis.
    rewrite Hzero in Hvis by exact Hu.
    contradiction.
Qed.

Lemma sid_labels_in_order_prefix_empty :
  forall n order_l vis_l sid_l,
    (forall u, 0 <= u < n -> Znth u vis_l 0 = 0) ->
    sid_labels_in_order_prefix n 0 order_l vis_l sid_l.
Proof.
  unfold sid_labels_in_order_prefix.
  intros n order_l vis_l sid_l Hzero v Hv Hvis.
  rewrite Hzero in Hvis by exact Hv.
  contradiction.
Qed.

Lemma NoDup_map_Z_of_nat_seq :
  forall start len,
    NoDup (map Z.of_nat (seq start len)).
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [x [Hx Hin_seq]].
      apply in_seq in Hin_seq.
      lia.
    + apply IH.
Qed.

Lemma phase2_order_spec_NoDup :
  forall fin_l order_l n,
    phase2_order_spec fin_l order_l n ->
    list_prefix_no_dup n order_l.
Proof.
  intros fin_l order_l n Hspec.
  unfold phase2_order_spec in Hspec.
  destruct Hspec as [_ [_ [_ [_ [_ [_ [_ Hnodup]]]]]]].
  exact Hnodup.
Qed.

Lemma phase2_order_spec_prefix_label_neq_current :
  forall fin_l order_l vis_l sid_l n k root v,
    phase2_order_spec fin_l order_l n ->
    sid_labels_in_order_prefix n k order_l vis_l sid_l ->
    root = Znth k order_l 0 ->
    0 <= k < n ->
    0 <= v < n ->
    Znth v vis_l 0 <> 0 ->
    Znth v sid_l 0 <> root.
Proof.
  intros fin_l order_l vis_l sid_l n k root v Hspec Hlabels Hroot Hk Hv Hvis Heq.
  destruct (Hlabels v Hv Hvis) as [i [Hi Hsid]].
  subst root.
  assert (Hnodup : list_prefix_no_dup n order_l)
    by (eapply phase2_order_spec_NoDup; eauto).
  assert (Hik : i <> k) by lia.
  apply Hik.
  refine (Hnodup i k _ _ _).
  - lia.
  - lia.
  - rewrite <- Hsid.
    exact Heq.
Qed.

Lemma sid_correct_on_marked_step_from_dfs2 :
  forall g n k order_l fin_l vis_l sid_l vis_l_ sid_l_ root,
    phase2_order_spec fin_l order_l n ->
    all_order_prefix_marked n k order_l vis_l ->
    phase2_prefix_complete g n k order_l vis_l ->
    sid_correct_on_marked g n vis_l sid_l ->
    sid_labels_in_order_prefix n k order_l vis_l sid_l ->
    dfs2_phase2_post g n vis_l sid_l vis_l_ sid_l_ root ->
    root = Znth k order_l 0 ->
    0 <= k < n ->
    Znth root vis_l 0 = 0 ->
    sid_correct_on_marked g n vis_l_ sid_l_.
Proof.
  intros g n k order_l fin_l vis_l sid_l vis_l_ sid_l_ root
    Horder Hmarked Hcomplete Hsid_old Hlabels Hpost Hroot Hk Hroot_zero.
  destruct Hpost as [Hold [Hnew Hroot_complete]].
  destruct Hsid_old as [Hsid_pair Hsid_rep].
  assert (Hroot_range : 0 <= root < n).
  { subst root. eapply phase2_order_entry_range; [exact Horder | exact Hk]. }
  unfold sid_correct_on_marked in *.
  split.
  - intros u Hu Hu_vis v Hv Hv_vis.
  destruct (classic (Znth u vis_l 0 <> 0)) as [Hu_old | Hu_new];
  destruct (classic (Znth v vis_l 0 <> 0)) as [Hv_old | Hv_new].
  + destruct (Hold u Hu Hu_old) as [_ Hu_sid].
    destruct (Hold v Hv Hv_old) as [_ Hv_sid].
    rewrite Hu_sid, Hv_sid.
    apply Hsid_pair; assumption.
  + destruct (Hold u Hu Hu_old) as [_ Hu_sid].
    assert (Hv_zero : Znth v vis_l 0 = 0) by lia.
    destruct (Hnew v Hv Hv_vis Hv_zero) as [Hv_sid Hv_mut_root].
    rewrite Hu_sid, Hv_sid.
    split.
    * intro Heq.
      exfalso.
      eapply (phase2_order_spec_prefix_label_neq_current
        fin_l order_l vis_l sid_l n k root u); eauto.
    * intro Hmut_uv.
      exfalso.
      destruct (Hlabels u Hu Hu_old) as [i [Hi Hu_label]].
      assert (Hi_vis : Znth (Znth i order_l 0) vis_l 0 <> 0)
        by (apply Hmarked; exact Hi).
      pose proof (Hsid_pair u Hu Hu_old (Znth i order_l 0)) as Hsid_i.
      assert (Hi_range : 0 <= Znth i order_l 0 < n).
      { eapply phase2_order_entry_range; [exact Horder | lia]. }
      specialize (Hsid_i Hi_range Hi_vis).
      destruct Hsid_i as [Hsid_i_to _].
      destruct (Hsid_rep u Hu Hu_old) as [_ [_ Hu_rep]].
      assert (Hui : mutually_reachable g u (Znth i order_l 0)).
      { apply Hsid_i_to. rewrite <- Hu_label. symmetry. exact Hu_rep. }
      assert (Hi_root : mutually_reachable g (Znth i order_l 0) root).
      {
        eapply mutually_reachable_trans_local.
        - apply mutually_reachable_sym_local. exact Hui.
        - eapply mutually_reachable_trans_local.
          + exact Hmut_uv.
          + apply mutually_reachable_sym_local. exact Hv_mut_root.
      }
      pose proof (Hcomplete i root Hi Hroot_range Hi_root) as Hroot_vis.
      congruence.
  + assert (Hu_zero : Znth u vis_l 0 = 0) by lia.
    destruct (Hnew u Hu Hu_vis Hu_zero) as [Hu_sid Hu_mut_root].
    destruct (Hold v Hv Hv_old) as [_ Hv_sid].
    rewrite Hu_sid, Hv_sid.
    split.
    * intro Heq.
      exfalso.
      eapply (phase2_order_spec_prefix_label_neq_current
        fin_l order_l vis_l sid_l n k root v); eauto.
    * intro Hmut_uv.
      exfalso.
      destruct (Hlabels v Hv Hv_old) as [i [Hi Hv_label]].
      assert (Hi_vis : Znth (Znth i order_l 0) vis_l 0 <> 0)
        by (apply Hmarked; exact Hi).
      pose proof (Hsid_pair v Hv Hv_old (Znth i order_l 0)) as Hsid_i.
      assert (Hi_range : 0 <= Znth i order_l 0 < n).
      { eapply phase2_order_entry_range; [exact Horder | lia]. }
      specialize (Hsid_i Hi_range Hi_vis).
      destruct Hsid_i as [Hsid_i_to _].
      destruct (Hsid_rep v Hv Hv_old) as [_ [_ Hv_rep]].
      assert (Hvi : mutually_reachable g v (Znth i order_l 0)).
      { apply Hsid_i_to. rewrite <- Hv_label. symmetry. exact Hv_rep. }
      assert (Hi_root : mutually_reachable g (Znth i order_l 0) root).
      {
        eapply mutually_reachable_trans_local.
        - apply mutually_reachable_sym_local. exact Hvi.
        - eapply mutually_reachable_trans_local.
          + apply mutually_reachable_sym_local. exact Hmut_uv.
          + apply mutually_reachable_sym_local. exact Hu_mut_root.
      }
      pose proof (Hcomplete i root Hi Hroot_range Hi_root) as Hroot_vis.
      congruence.
  + assert (Hu_zero : Znth u vis_l 0 = 0) by lia.
    assert (Hv_zero : Znth v vis_l 0 = 0) by lia.
    destruct (Hnew u Hu Hu_vis Hu_zero) as [Hu_sid Hu_mut_root].
    destruct (Hnew v Hv Hv_vis Hv_zero) as [Hv_sid Hv_mut_root].
    rewrite Hu_sid, Hv_sid.
    split.
    * intros _.
      eapply mutually_reachable_trans_local.
      -- apply mutually_reachable_sym_local. exact Hu_mut_root.
      -- exact Hv_mut_root.
    * intros _. reflexivity.
  - intros u Hu Hu_vis.
    destruct (classic (Znth u vis_l 0 <> 0)) as [Hu_old | Hu_new].
    + destruct (Hold u Hu Hu_old) as [_ Hu_sid].
      destruct (Hsid_rep u Hu Hu_old) as [Hrng [Hrvis Hrself]].
      destruct (Hold (Znth u sid_l 0) Hrng Hrvis) as [Hrvis' Hrsid].
      rewrite Hu_sid.
      split; [exact Hrng |].
      split; [exact Hrvis' |].
      rewrite Hrsid. exact Hrself.
    + assert (Hu_zero : Znth u vis_l 0 = 0) by lia.
      destruct (Hnew u Hu Hu_vis Hu_zero) as [Hu_sid _].
      rewrite Hu_sid.
      assert (Hroot_mut : mutually_reachable g root root).
      { unfold mutually_reachable, reachable; split; reflexivity. }
      pose proof (Hroot_complete root Hroot_range Hroot_mut) as Hroot_vis.
      destruct (classic (Znth root vis_l 0 <> 0)) as [Hroot_old | Hroot_new].
      * exfalso. congruence.
      * assert (Hroot_zero' : Znth root vis_l 0 = 0) by lia.
        destruct (Hnew root Hroot_range Hroot_vis Hroot_zero') as [Hroot_sid _].
        split; [exact Hroot_range |].
        split; [exact Hroot_vis |].
        exact Hroot_sid.
Qed.

Definition dfs2_phase2_state
    (fin_l vis_l sid_l : list Z) (n : Z) : KSt :=
  @Kosaraju.MkSt Z 0%nat
    (fun v =>
       if Z_lt_ge_dec v 0 then 0%nat
       else if Z_lt_ge_dec v n then Z.to_nat (Znth v fin_l 0)
       else 0%nat)
    (fun _ => True)
    (fun v => 0 <= v < n /\ Znth v vis_l 0 <> 0)
    (fun v => Z.to_nat (Znth v sid_l 0))
    (Z.to_nat n).

(* The top-level phase-2 representation relation is deliberately separate
   from the cursor-local [pre_dfs2].  It records the C arrays and the fixed
   phase-1 timer/finish relation, then carries the remaining scheduled SCC
   program from C loop index [k].  This is the same residual-safeExec shape
   used by the DFS examples; prefix predicates remain available for local C
   updates, but are no longer the sole abstraction boundary. *)
Definition phase2_array_representation
    (g : AdjGraph) (fin_l order_l vis1_l vis2_l sid_l : list Z)
    (timer_v n : Z) : Prop :=
  Zlength fin_l = n /\
  Zlength order_l = n /\
  Zlength vis1_l = n /\
  Zlength vis2_l = n /\
  Zlength sid_l = n /\
  (0 <= timer_v <= n)%Z /\
  phase2_sequence_order_spec fin_l order_l n /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 <> 0%Z) /\
  pre_dfs2 g nil nil vis2_l sid_l 0
    (dfs2_phase2_state fin_l vis2_l sid_l n).

Definition phase2_residual_refinement
    (g : AdjGraph) (fin_l order_l vis1_l vis2_l sid_l : list Z)
    (timer_v n k : Z) : Prop :=
  phase2_array_representation g fin_l order_l vis1_l vis2_l sid_l timer_v n /\
  0 <= k <= n /\
  exists X : unit -> KSt -> Prop,
    safeExec (fun st => st = dfs2_phase2_state fin_l vis2_l sid_l n)
      (phase2_c_schedule g
        (fun i => Znth (Z.of_nat i) order_l 0)
        (Z.to_nat k) (Z.to_nat (n - k))) X.

Lemma phase2_prefix_forward_closed_state :
  forall g fin_l order_l vis_l sid_l n k,
    AdjGraphValid g ->
    adj_verts g = n ->
    phase1_order_graph g fin_l n ->
    phase2_order_spec fin_l order_l n ->
    0 <= k <= n ->
    all_order_prefix_marked n k order_l vis_l ->
    phase2_prefix_complete g n k order_l vis_l ->
    sid_correct_on_marked g n vis_l sid_l ->
    sid_labels_in_order_prefix n k order_l vis_l sid_l ->
    @Kosaraju.ForwardReachClosed AdjGraph Z (Z * Z) KG g
      (dfs2_phase2_state fin_l vis_l sid_l n).
Proof.
  intros g fin_l order_l vis_l sid_l n k
    Hvalid Hverts Hphase Horder Hk Hmarked Hcomplete Hsid Hlabels.
  unfold Kosaraju.ForwardReachClosed, dfs2_phase2_state; simpl.
  intros v w [Hvvalid0 Hvis] Hreach.
  destruct (Z.eq_dec v w) as [-> | Hneq]; [split; assumption|].
  assert (Hvvalid_wvalid : graph_basic.vvalid g v /\ graph_basic.vvalid g w).
  {
    eapply reachable_basic.reachable_vvalid; eauto.
  }
  destruct Hvvalid_wvalid as [Hvvalid Hwvalid].
  change (adj_vvalid g v) in Hvvalid.
  change (adj_vvalid g w) in Hwvalid.
  unfold adj_vvalid in *.
  rewrite Hverts in Hvvalid, Hwvalid.
  destruct (classic (Znth w vis_l 0 <> 0)) as [Hvisw | Hnotw].
  { split; assumption. }
  assert (Hwzero : Znth w vis_l 0 = 0) by lia.
  destruct Hsid as [Hsid_pair Hsid_rep].
  destruct (Hsid_rep v Hvvalid Hvis) as [Hrng [Hrvis Hrsid]].
  pose proof (Hsid_pair v Hvvalid Hvis (Znth v sid_l 0) Hrng Hrvis)
    as [Hsame_to _].
  assert (Hv_rep : mutually_reachable g v (Znth v sid_l 0)).
  { apply Hsame_to. symmetry. exact Hrsid. }
  destruct (Hlabels (Znth v sid_l 0) Hrng Hrvis) as [i [Hi Hsid_label]].
  assert (Hrep_order : Znth v sid_l 0 = Znth i order_l 0).
  { rewrite <- Hsid_label. symmetry. exact Hrsid. }
  assert (Hrep_w_reach : reachable g (Znth i order_l 0) w).
  {
    rewrite <- Hrep_order.
    eapply reachable_trans.
    - exact (proj2 Hv_rep).
    - exact Hreach.
  }
  assert (Hmarked_i : all_order_prefix_marked n i order_l vis_l).
  { intros j Hj. apply Hmarked. lia. }
  assert (Hcomplete_i : phase2_prefix_complete g n i order_l vis_l).
  { intros j x Hj Hx Hmut. apply (Hcomplete j x); [lia | exact Hx | exact Hmut]. }
  assert (Hrep_w_mut : mutually_reachable g (Znth i order_l 0) w).
  {
    eapply (phase2_unvisited_reachable_mutual
      g fin_l order_l vis_l n i (Znth i order_l 0) w);
      eauto; try lia; try reflexivity.
  }
  split; [exact Hwvalid|].
  eapply Hcomplete; eauto.
Qed.

Lemma sid_correct_on_marked_final :
  forall g n order_l vis_l sid_l,
    order_covers_range n order_l ->
    all_order_prefix_marked n n order_l vis_l ->
    sid_correct_on_marked g n vis_l sid_l ->
    forall u, 0 <= u < n ->
      forall v, 0 <= v < n ->
        ((Znth u sid_l 0 = Znth v sid_l 0 -> reachable g u v /\ reachable g v u) /\
         (reachable g u v /\ reachable g v u -> Znth u sid_l 0 = Znth v sid_l 0)).
Proof.
  intros g n order_l vis_l sid_l Hcover Hprefix Hsid u Hu v Hv.
  destruct Hsid as [Hsid _].
  apply Hsid; try assumption.
  - eapply order_covers_range_all_marked; eauto.
  - eapply order_covers_range_all_marked; eauto.
Qed.

Lemma sid_correct_on_marked_final_mutually :
  forall g n order_l vis_l sid_l,
    order_covers_range n order_l ->
    all_order_prefix_marked n n order_l vis_l ->
    sid_correct_on_marked g n vis_l sid_l ->
    forall u, 0 <= u < n ->
      forall v, 0 <= v < n ->
        ((Znth u sid_l 0 = Znth v sid_l 0 -> mutually_reachable g u v) /\
         (mutually_reachable g u v -> Znth u sid_l 0 = Znth v sid_l 0)).
Proof.
  intros g n order_l vis_l sid_l Hcover Hprefix Hsid u Hu v Hv.
  pose proof (sid_correct_on_marked_final g n order_l vis_l sid_l
                Hcover Hprefix Hsid u Hu v Hv) as [Hto Hfrom].
  split; [exact Hto | exact Hfrom].
Qed.

Definition phase2_sequence_residual_refinement
    (g : AdjGraph) (fin_l order_l vis1_l vis2_l sid_l : list Z)
    (timer_v n k : Z) : Prop :=
  Zlength fin_l = n /\
  Zlength order_l = n /\
  Zlength vis1_l = n /\
  Zlength vis2_l = n /\
  Zlength sid_l = n /\
  (0 <= timer_v <= n)%Z /\
  (forall i, (0 <= i < n)%Z ->
     Znth i order_l 0 = Znth (n - 1 - i) fin_l 0) /\
  (forall i, (0 <= i < n)%Z ->
     (0 <= Znth i order_l 0 < n)%Z) /\
  (forall v, (0 <= v < n)%Z -> Znth v vis1_l 0 <> 0%Z) /\
  (0 <= k <= n)%Z /\
  phase1_order_graph g fin_l n /\
  phase2_order_spec fin_l order_l n /\
  all_order_prefix_marked n k order_l vis2_l /\
  phase2_prefix_complete g n k order_l vis2_l /\
  sid_correct_on_marked g n vis2_l sid_l /\
  sid_labels_in_order_prefix n k order_l vis2_l sid_l /\
  (k = n ->
    forall u, (0 <= u < n)%Z ->
    forall v, (0 <= v < n)%Z ->
      ((Znth u sid_l 0 = Znth v sid_l 0 -> mutually_reachable g u v) /\
       (mutually_reachable g u v -> Znth u sid_l 0 = Znth v sid_l 0))).

Lemma phase2_sequence_residual_step_from_dfs2 :
  forall g fadj_col_l fadj_row_l fin_l order_l vis1_l
         vis_l sid_before_l sid_l vis_l_ sid_l_ timer_v n k root,
    phase2_sequence_residual_refinement
      g fin_l order_l vis1_l vis_l sid_before_l timer_v n k ->
    csr_wf2 g fadj_col_l fadj_row_l vis_l_ sid_l_ ->
    adj_verts g = n ->
    sid_l = replace_Znth root root sid_before_l ->
    dfs2_phase2_post g n vis_l sid_l vis_l_ sid_l_ root ->
    root = Znth k order_l 0 ->
    0 <= root < n ->
    Znth root vis_l 0 = 0 ->
    0 <= k < n ->
    phase2_sequence_residual_refinement
      g fin_l order_l vis1_l vis_l_ sid_l_ timer_v n (k + 1).
Proof.
  intros g fadj_col_l fadj_row_l fin_l order_l vis1_l
    vis_l sid_before_l sid_l vis_l_ sid_l_ timer_v n k root
    Hres Hwf_out Hverts Hsid_l Hpost Hroot_eq Hroot_range Hroot_zero Hk.
  unfold phase2_sequence_residual_refinement in *.
  destruct Hres as
    [Hfin_len [Horder_len [Hvis1_len [Hvis_len [Hsid_before_len
    [Htimer [Hrev [Hrange [Hall_vis1 [Hk_old [Hphase1 [Horder
    [Hmarked [Hcomplete [Hsid_old [Hlabels_old Hfinal_old]]]]]]]]]]]]]]]].
  unfold csr_wf2 in Hwf_out.
  destruct Hwf_out as
    [_ [_ [Hvis_out_len [Hsid_out_len _]]]].
  assert (Hsid_premark :
    sid_correct_on_marked g n vis_l sid_l).
  {
    subst sid_l.
    eapply sid_correct_on_marked_unvisited_sid_update; eauto.
  }
  assert (Hlabels_premark :
    sid_labels_in_order_prefix n k order_l vis_l sid_l).
  {
    subst sid_l.
    eapply sid_labels_in_order_prefix_unvisited_sid_update; eauto.
  }
  assert (Hroot_vis_out : Znth root vis_l_ 0 <> 0).
  {
    destruct Hpost as [_ [_ Hroot_complete]].
    apply Hroot_complete; [exact Hroot_range |].
    unfold mutually_reachable, reachable.
    split; reflexivity.
  }
  assert (Hmarked_new :
    all_order_prefix_marked n (k + 1) order_l vis_l_).
  {
    unfold all_order_prefix_marked in *.
    intros i Hi.
    destruct (Z.eq_dec i k) as [Hik | Hik].
    - subst i. rewrite <- Hroot_eq. exact Hroot_vis_out.
    - destruct Hpost as [Hold _].
      destruct (Hold (Znth i order_l 0)
        (ltac:(apply Hrange; lia))
        (ltac:(apply Hmarked; lia))) as [Hvis_new _].
      exact Hvis_new.
  }
  assert (Hcomplete_new :
    phase2_prefix_complete g n (k + 1) order_l vis_l_).
  {
    eapply phase2_prefix_complete_step_from_dfs2
      with (vis_l1 := vis_l) (sid_l1 := sid_l) (root := root);
      eauto; lia.
  }
  assert (Hsid_new :
    sid_correct_on_marked g n vis_l_ sid_l_).
  {
    eapply sid_correct_on_marked_step_from_dfs2
      with (k := k) (order_l := order_l) (fin_l := fin_l)
           (vis_l := vis_l) (sid_l := sid_l) (root := root);
      eauto.
  }
  assert (Hlabels_new :
    sid_labels_in_order_prefix n (k + 1) order_l vis_l_ sid_l_).
  {
    eapply sid_labels_in_order_prefix_step_from_dfs2
      with (vis_l := vis_l) (sid_l := sid_l) (root := root);
      eauto; lia.
  }
  split; [exact Hfin_len |].
  split; [exact Horder_len |].
  split; [exact Hvis1_len |].
  split; [rewrite Hvis_out_len; exact Hverts |].
  split; [rewrite Hsid_out_len; exact Hverts |].
  split; [exact Htimer |].
  split; [exact Hrev |].
  split; [exact Hrange |].
  split; [exact Hall_vis1 |].
  split; [lia |].
  split; [exact Hphase1 |].
  split; [exact Horder |].
  split; [exact Hmarked_new |].
  split; [exact Hcomplete_new |].
  split; [exact Hsid_new |].
  split; [exact Hlabels_new |].
  intros Hkn u Hu v Hv.
  assert (Hmarked_final : all_order_prefix_marked n n order_l vis_l_).
  {
    replace n with (k + 1) by lia.
    exact Hmarked_new.
  }
  pose proof (phase2_order_spec_covers_range fin_l order_l n Horder)
    as Hcover.
  exact (sid_correct_on_marked_final_mutually
      g n order_l vis_l_ sid_l_ Hcover Hmarked_final Hsid_new u Hu v Hv).
Qed.

Lemma phase2_sequence_residual_step_from_marked :
  forall g fin_l order_l vis1_l vis_l sid_l timer_v n k root,
    phase2_sequence_residual_refinement
      g fin_l order_l vis1_l vis_l sid_l timer_v n k ->
    root = Znth k order_l 0 ->
    0 <= root < n ->
    Znth root vis_l 0 <> 0 ->
    0 <= k < n ->
    phase2_sequence_residual_refinement
      g fin_l order_l vis1_l vis_l sid_l timer_v n (k + 1).
Proof.
  intros g fin_l order_l vis1_l vis_l sid_l timer_v n k root
    Hres Hroot Hroot_range Hroot_vis Hk.
  unfold phase2_sequence_residual_refinement in *.
  destruct Hres as
    [Hfin_len [Horder_len [Hvis1_len [Hvis_len [Hsid_len
    [Htimer [Hrev [Hrange [Hall_vis1 [Hk_old [Hphase1 [Horder
    [Hmarked [Hcomplete [Hsid [Hlabels Hfinal_old]]]]]]]]]]]]]]]].
  assert (Hmarked_new :
    all_order_prefix_marked n (k + 1) order_l vis_l).
  {
    eapply all_order_prefix_marked_step; eauto.
  }
  assert (Hcomplete_new :
    phase2_prefix_complete g n (k + 1) order_l vis_l).
  {
    eapply phase2_prefix_complete_step_from_marked; eauto.
  }
  assert (Hlabels_new :
    sid_labels_in_order_prefix n (k + 1) order_l vis_l sid_l).
  {
    unfold sid_labels_in_order_prefix in *.
    intros v Hv Hvis.
    destruct (Hlabels v Hv Hvis) as [i [Hi Heq]].
    exists i. split; [lia | exact Heq].
  }
  split; [exact Hfin_len |].
  split; [exact Horder_len |].
  split; [exact Hvis1_len |].
  split; [exact Hvis_len |].
  split; [exact Hsid_len |].
  split; [exact Htimer |].
  split; [exact Hrev |].
  split; [exact Hrange |].
  split; [exact Hall_vis1 |].
  split; [lia |].
  split; [exact Hphase1 |].
  split; [exact Horder |].
  split; [exact Hmarked_new |].
  split; [exact Hcomplete_new |].
  split; [exact Hsid |].
  split; [exact Hlabels_new |].
  intros Hkn u Hu v Hv.
  assert (Hmarked_final : all_order_prefix_marked n n order_l vis_l).
  {
    replace n with (k + 1) by lia.
    exact Hmarked_new.
  }
  pose proof (phase2_order_spec_covers_range fin_l order_l n Horder)
    as Hcover.
  exact (sid_correct_on_marked_final_mutually
    g n order_l vis_l sid_l Hcover Hmarked_final Hsid u Hu v Hv).
Qed.

Lemma safeExec_from_Hoare_eq_state :
  forall {A : Type} (P : KSt -> Prop) (c : program KSt A)
         (X : A -> KSt -> Prop) (st : KSt),
    P st ->
    Hoare (fun st' => st' = st) c X ->
    safeExec P c X.
Proof.
  intros A P c X st Hpre [Hnrm Herr].
  exists st.
  split; [exact Hpre |].
  unfold safe, weakestpre.
  split.
  - intro Hc_err. exact (Herr st eq_refl Hc_err).
  - intros a st' Hc_nrm.
    exact (Hnrm a st st' eq_refl Hc_nrm).
Qed.

Lemma safeExec_return_unit_elim :
  forall (P : KSt -> Prop) (X : unit -> KSt -> Prop),
    safeExec P (return tt) X ->
    exists st, P st /\ X tt st.
Proof.
  intros P X [st [Hpre Hsafe]].
  exists st.
  split; [exact Hpre |].
  unfold safe in Hsafe.
  rewrite wp_ret in Hsafe.
  exact Hsafe.
Qed.

Definition dfs2_phase2_state_post
    (g : AdjGraph) (fin_l vis_l sid_l : list Z)
    (n root : Z) (st' : KSt) : Prop :=
  let st0 := dfs2_phase2_state fin_l vis_l sid_l n in
  (forall v,
      visited2 st' v ->
      ~ visited2 st0 v ->
      mutually_reachable g root v) /\
  (forall v,
      mutually_reachable g root v ->
      ~ visited2 st0 v ->
      visited2 st' v).

Lemma pre_dfs2_phase2_state :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l fin_l vis_l sid_l : list Z)
         (root_v n : Z),
    adj_verts g = n ->
    pre_dfs2 g fadj_col_l fadj_row_l vis_l sid_l root_v
      (dfs2_phase2_state fin_l vis_l sid_l n).
Proof.
  intros g fadj_col_l fadj_row_l fin_l vis_l sid_l root_v n Hverts.
  unfold pre_dfs2, dfs2_phase2_state.
  simpl.
  split.
  - intros u Hu.
    rewrite Hverts in Hu.
    tauto.
  - intros u Hu.
    reflexivity.
Qed.

Lemma dfs2_phase2_safeExec_state_post :
  forall g fadj_col_l fadj_row_l fin_l order_l vis1_l
         vis_l sid_before_l sid_l timer_v n k root u,
    phase2_sequence_residual_refinement
      g fin_l order_l vis1_l vis_l sid_before_l timer_v n k ->
    AdjGraphValid g ->
    adj_verts g = n ->
    sid_l = replace_Znth root root sid_before_l ->
    root = Znth k order_l 0 ->
    u = root ->
    0 <= root < n ->
    Znth root vis_l 0 = 0 ->
    0 <= k < n ->
    safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis_l sid_l root)
      (dfs_scc g root u)
      (fun _ st' => dfs2_phase2_state_post g fin_l vis_l sid_l n root st').
Proof.
  intros g fadj_col_l fadj_row_l fin_l order_l vis1_l
    vis_l sid_before_l sid_l timer_v n k root u
    Hres Hvalid Hverts Hsid_l Hroot_eq Hu_root Hroot_range Hroot_zero Hk.
  subst u.
  unfold phase2_sequence_residual_refinement in Hres.
  destruct Hres as
    [Hfin_len [Horder_len [Hvis1_len [Hvis_len [Hsid_before_len
    [Htimer [Hrev [Hrange [Hall_vis1 [Hk_old [Hphase1 [Horder
    [Hmarked [Hcomplete [Hsid_old [Hlabels_old Hfinal_old]]]]]]]]]]]]]]]].
  assert (Hsid_premark :
    sid_correct_on_marked g n vis_l sid_l).
  {
    subst sid_l.
    eapply sid_correct_on_marked_unvisited_sid_update; eauto.
  }
  assert (Hlabels_premark :
    sid_labels_in_order_prefix n k order_l vis_l sid_l).
  {
    subst sid_l.
    eapply sid_labels_in_order_prefix_unvisited_sid_update; eauto.
  }
  pose (st0 := dfs2_phase2_state fin_l vis_l sid_l n).
  assert (Hpre : pre_dfs2 g fadj_col_l fadj_row_l vis_l sid_l root st0).
  {
    subst st0. apply pre_dfs2_phase2_state. exact Hverts.
  }
  eapply safeExec_from_Hoare_eq_state with (st := st0);
    [exact Hpre |].
  unfold dfs_scc.
  assert (Hclosed :
    @Kosaraju.ForwardReachClosed AdjGraph Z (Z * Z) KG g st0).
  {
    subst st0.
    eapply phase2_prefix_forward_closed_state; eauto; lia.
  }
  assert (Hnot_root : ~ Kosaraju.visited2 st0 root).
  {
    subst st0.
    unfold dfs2_phase2_state.
    simpl.
    intro Hroot_vis.
    destruct Hroot_vis as [_ Hnz].
    congruence.
  }
  eapply Hoare_imp_post.
  - apply Hoare_conj.
    + apply DFS_scc_reachable_from_u.
    + apply DFS_scc_reachable_visited_closed; assumption.
  - intros _ st' [Hreach_out Hvisit_out].
    unfold dfs2_phase2_state_post.
    fold st0.
    split.
    + intros v Hvis_new Hnot_old.
      destruct (Hreach_out v Hvis_new) as [Hvis_old | Hreach_root_v].
      * exfalso. exact (Hnot_old Hvis_old).
      * assert (Hv_range : 0 <= v < n).
        {
          destruct (Z.eq_dec v root) as [-> | Hne]; [exact Hroot_range|].
          assert (Hroot_ne_v : root <> v)
            by (intro Heq; apply Hne; symmetry; exact Heq).
          pose proof (reachable_basic.reachable_vvalid
            (g:=g) root v Hroot_ne_v Hreach_root_v) as [_ Hvvalid].
          change (adj_vvalid g v) in Hvvalid.
          unfold adj_vvalid in Hvvalid.
          rewrite Hverts in Hvvalid.
          exact Hvvalid.
        }
        assert (Hv_zero : Znth v vis_l 0 = 0).
        {
          destruct (Z.eq_dec (Znth v vis_l 0) 0) as [Hz | Hnz]; [exact Hz|].
          exfalso. apply Hnot_old.
          subst st0.
          unfold dfs2_phase2_state. simpl.
          split; [exact Hv_range | exact Hnz].
        }
        eapply phase2_unvisited_reachable_mutual; eauto.
    + intros v Hmut Hnot_old.
      apply Hvisit_out.
      * exact (proj1 Hmut).
      * exact Hnot_old.
Qed.

Lemma dfs2_phase2_post_from_state_post :
  forall g fadj_col_l fadj_row_l fin_l vis_l sid_l vis_l_ sid_l_
         n root root_v st',
    adj_verts g = n ->
    0 <= root < n ->
    Znth root sid_l 0 = root ->
    pre_dfs2 g fadj_col_l fadj_row_l vis_l_ sid_l_ root_v st' ->
    dfs2_phase2_state_post g fin_l vis_l sid_l n root st' ->
    (forall w, 0 <= w < n ->
       Znth w vis_l 0 <> 0 -> Znth w vis_l_ 0 <> 0) ->
    (forall w, 0 <= w < n ->
       Znth w vis_l 0 <> 0 -> Znth w sid_l_ 0 = Znth w sid_l 0) ->
    (forall w, 0 <= w < n ->
       Znth w vis_l_ 0 <> 0 ->
       Znth w vis_l 0 = 0 ->
       Znth w sid_l_ 0 = Znth root sid_l 0) ->
    dfs2_phase2_post g n vis_l sid_l vis_l_ sid_l_ root.
Proof.
  intros g fadj_col_l fadj_row_l fin_l vis_l sid_l vis_l_ sid_l_
    n root root_v st' Hverts Hroot Hroot_sid Hpre_out Hstate_post
    Hvis_keep Hsid_keep Hsid_new.
  unfold dfs2_phase2_post.
  split.
  - intros w Hw Hvis_old.
    split.
    + apply Hvis_keep; assumption.
    + apply Hsid_keep; assumption.
  - split.
    + intros w Hw Hvis_out Hvis_zero.
      split.
      * rewrite <- Hroot_sid. apply Hsid_new; assumption.
      * unfold dfs2_phase2_state_post in Hstate_post.
        destruct Hstate_post as [Hmut _].
        apply Hmut.
        -- destruct Hpre_out as [Hvis_map _].
           apply (proj2 (Hvis_map w ltac:(rewrite Hverts; exact Hw))).
           exact Hvis_out.
        -- unfold dfs2_phase2_state.
           simpl.
           intro Hst_old.
           destruct Hst_old as [_ Hst_old_vis].
           congruence.
    + intros w Hw Hmut_root.
      destruct (classic (Znth w vis_l 0 <> 0)) as [Hvis_old | Hnot_old].
      * apply Hvis_keep; assumption.
      * assert (Hvis_zero : Znth w vis_l 0 = 0) by lia.
        destruct Hpre_out as [Hvis_map _].
        apply (proj1 (Hvis_map w ltac:(rewrite Hverts; exact Hw))).
        unfold dfs2_phase2_state_post in Hstate_post.
        destruct Hstate_post as [_ Hvisit].
        apply Hvisit; [exact Hmut_root |].
        unfold dfs2_phase2_state.
        simpl.
        intro Hst_old.
        destruct Hst_old as [_ Hst_old_vis].
        congruence.
Qed.

Lemma dfs2_phase2_post_and_residual_from_return :
  forall g fadj_col_l fadj_row_l fin_l order_l vis1_l
         vis_l sid_before_l sid_l vis_l_ sid_l_ timer_v n k root root_v,
    phase2_sequence_residual_refinement
      g fin_l order_l vis1_l vis_l sid_before_l timer_v n k ->
    csr_wf2 g fadj_col_l fadj_row_l vis_l_ sid_l_ ->
    adj_verts g = n ->
    sid_l = replace_Znth root root sid_before_l ->
    root = Znth k order_l 0 ->
    0 <= root < n ->
    Znth root vis_l 0 = 0 ->
    0 <= k < n ->
    Znth root sid_l 0 = root ->
    safeExec (pre_dfs2 g fadj_col_l fadj_row_l vis_l_ sid_l_ root_v)
      (return tt)
      (fun _ st' => dfs2_phase2_state_post g fin_l vis_l sid_l n root st') ->
    (forall w, 0 <= w < n ->
       Znth w vis_l 0 <> 0 -> Znth w vis_l_ 0 <> 0) ->
    (forall w, 0 <= w < n ->
       Znth w vis_l 0 <> 0 -> Znth w sid_l_ 0 = Znth w sid_l 0) ->
    (forall w, 0 <= w < n ->
       Znth w vis_l_ 0 <> 0 ->
       Znth w vis_l 0 = 0 ->
       Znth w sid_l_ 0 = Znth root sid_l 0) ->
    dfs2_phase2_post g n vis_l sid_l vis_l_ sid_l_ root /\
    phase2_sequence_residual_refinement
      g fin_l order_l vis1_l vis_l_ sid_l_ timer_v n (k + 1).
Proof.
  intros g fadj_col_l fadj_row_l fin_l order_l vis1_l
    vis_l sid_before_l sid_l vis_l_ sid_l_ timer_v n k root root_v
    Hres Hwf_out Hverts Hsid_l Hroot_eq Hroot_range Hroot_zero Hk
    Hroot_sid Hret Hvis_keep Hsid_keep Hsid_new.
  destruct (safeExec_return_unit_elim _ _ Hret) as [st' [Hpre_out Hstate_post]].
  assert (Hpost :
    dfs2_phase2_post g n vis_l sid_l vis_l_ sid_l_ root).
  {
    eapply dfs2_phase2_post_from_state_post; eauto.
  }
  split; [exact Hpost |].
  eapply phase2_sequence_residual_step_from_dfs2; eauto.
Qed.

Definition dfs1_timer_surplus_preserved
  (vis1_l vis1_l_ : list Z) (timer_v timer_v_ : Z) : Prop :=
  forall spare,
    0 <= spare ->
    timer_v + spare <= count_nonzero vis1_l ->
    timer_v_ + spare <= count_nonzero vis1_l_.

Definition dfs1_active_timer_surplus
  (vis1_l vis1_m : list Z) (timer_v timer_m : Z) : Prop :=
  forall spare,
    0 <= spare ->
    timer_v + spare <= count_nonzero vis1_l ->
    timer_m + spare + 1 <= count_nonzero vis1_m.

Definition dfs1_high_level_post
  (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l vis1_l_ fin_l_ : list Z)
  (u timer_v timer_v_ n : Z) : Prop :=
  adj_verts g = n /\
  csr_wf1 g radj_col_l radj_row_l vis1_l_ fin_l_ /\
  csr1_faithful g radj_col_l radj_row_l /\
  dfs1_phase1_ready g radj_col_l radj_row_l vis1_l fin_l timer_v u /\
  dfs1_phase1_state_ready g radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ /\
  0 <= u < n /\
  0 <= timer_v <= timer_v_ /\
  timer_v <= count_nonzero vis1_l /\
  timer_v_ <= count_nonzero vis1_l_ /\
  dfs1_timer_surplus_preserved vis1_l vis1_l_ timer_v timer_v_ /\
  fin_values_in_int_range fin_l n /\
  fin_values_in_int_range fin_l_ n /\
  Znth u vis1_l_ 0 <> 0 /\
  (forall w, 0 <= w < n ->
     Znth w vis1_l 0 <> 0 -> Znth w vis1_l_ 0 <> 0) /\
  (forall w, 0 <= w < n ->
     Znth w vis1_l 0 <> 0 -> Znth w fin_l_ 0 = Znth w fin_l 0).

Lemma fin_nat_eq_to_z_eq_in_range :
  forall a b,
    0 <= a ->
    0 <= b ->
    Z.to_nat a = Z.to_nat b ->
    a = b.
Proof.
  intros a b Ha Hb Hnat.
  rewrite <- (Z2Nat.id a Ha).
  rewrite <- (Z2Nat.id b Hb).
  rewrite Hnat.
  reflexivity.
Qed.

Lemma dfs1_phase1_result_high_level_post :
  forall (g : AdjGraph) (radj_col_l radj_row_l vis1_l fin_l vis1_l_ fin_l_ : list Z)
         (u timer_v timer_v_ n : Z),
    adj_verts g = n ->
    dfs1_phase1_ready g radj_col_l radj_row_l vis1_l fin_l timer_v u ->
    csr1_faithful g radj_col_l radj_row_l ->
    fin_values_in_int_range fin_l n ->
    fin_values_in_int_range fin_l_ n ->
    dfs1_phase1_state_ready g radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_ ->
    safeExec
      (pre_dfs1 g radj_col_l radj_row_l vis1_l_ fin_l_ timer_v_)
      (MonadErr.ret tt)
      (result_state
         (pre_dfs1_phase1 g radj_col_l radj_row_l vis1_l fin_l timer_v u)
         (dfs_finish_phase1_checked g radj_col_l radj_row_l vis1_l fin_l timer_v u)) ->
    0 <= u < n ->
    0 <= timer_v ->
    timer_v <= count_nonzero vis1_l ->
    0 <= timer_v_ ->
    timer_v_ <= count_nonzero vis1_l_ ->
    timer_v <= timer_v_ ->
    dfs1_timer_surplus_preserved vis1_l vis1_l_ timer_v timer_v_ ->
    (forall w, (0 <= w /\ w < n) /\ Znth w vis1_l 0 <> 0 ->
       Znth w fin_l_ 0 = Znth w fin_l 0) ->
    dfs1_high_level_post g radj_col_l radj_row_l vis1_l fin_l vis1_l_ fin_l_
      u timer_v timer_v_ n.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l vis1_l_ fin_l_
         u timer_v timer_v_ n Hadj Hready Hfaith Hfin Hfin' Hstate Hret
         Hurange Htimer_nonneg Htimer_count Htimer'_nonneg Htimer'_count
         Htimer_mono Hsurplus Hfin_old.
  unfold safeExec, safe, result_state in Hret.
  destruct Hret as [st_final [Hpre_final [_ Hpost_return]]].
  pose proof (Hpost_return tt st_final (conj eq_refl eq_refl)) as Hresult_state.
  destruct Hresult_state as [st_entry [Hpre_entry Hnrm]].
  destruct Hpre_final as [Hfinal_vis [Hfinal_fin [Hfinal_timer [Hfinal_invalid_vis Hfinal_invalid_fin]]]].
  destruct Hpre_entry as [Hpre_entry_dfs _].
  destruct Hpre_entry_dfs as [Hentry_vis [Hentry_fin [Hentry_timer [Hentry_invalid_vis Hentry_invalid_fin]]]].
  pose proof (dfs_finish_phase1_checked_nrm_result
    g radj_col_l radj_row_l vis1_l fin_l timer_v u st_entry st_final Hnrm)
    as Hphase_result.
  destruct Hphase_result as [_ [Huvisited [Hvisited_sub Hfinish_pres]]].
  unfold dfs1_high_level_post.
  split; [ exact Hadj | ].
  split; [ exact (proj1 Hstate) | ].
  split; [ exact Hfaith | ].
  split; [ exact Hready | ].
  split; [ exact Hstate | ].
  split; [ exact Hurange | ].
  split; [ lia | ].
  split; [ exact Htimer_count | ].
  split; [ exact Htimer'_count | ].
  split; [ exact Hsurplus | ].
  split; [ exact Hfin | ].
  split; [ exact Hfin' | ].
  split.
  - apply (proj1 (Hfinal_vis u ltac:(rewrite Hadj; exact Hurange))).
    exact Huvisited.
  - split.
    + intros w Hw Hvis_old.
      apply (proj1 (Hfinal_vis w ltac:(rewrite Hadj; exact Hw))).
      apply Hvisited_sub.
      apply (proj2 (Hentry_vis w ltac:(rewrite Hadj; exact Hw))).
      exact Hvis_old.
    + intros w Hw Hvis_old.
      apply Hfin_old.
      split; [ exact Hw | exact Hvis_old ].
Qed.

Definition dfs2_high_level_post
  (g : AdjGraph) (fadj_col_l fadj_row_l vis2_l sid_l vis2_l_ sid_l_ : list Z)
  (root u n : Z) : Prop :=
  adj_verts g = n /\
  csr_wf2 g fadj_col_l fadj_row_l vis2_l_ sid_l_ /\
  csr2_faithful g fadj_col_l fadj_row_l /\
  0 <= root < n /\
  0 <= u < n /\
  Znth u vis2_l_ 0 <> 0 /\
  (forall w, 0 <= w < n ->
     Znth w vis2_l 0 <> 0 -> Znth w vis2_l_ 0 <> 0).

(* The C-level dfs2 contract keeps the phase-2 continuation as [safeExec]
   and exposes these array facts separately.  This bridge is the pure
   refinement boundary used to discharge the high-level contract without
   changing that residual schedule. *)
Lemma dfs2_low_level_to_high_level :
  forall (g : AdjGraph) (fadj_col_l fadj_row_l vis2_l sid_l vis2_l_ sid_l_ : list Z)
         (root u n : Z),
    csr_wf2 g fadj_col_l fadj_row_l vis2_l_ sid_l_ ->
    csr2_faithful g fadj_col_l fadj_row_l ->
    adj_verts g = n ->
    0 <= root < n ->
    0 <= u < n ->
    Znth u vis2_l_ 0 <> 0 ->
    (forall w, 0 <= w < n ->
       Znth w vis2_l 0 <> 0 -> Znth w vis2_l_ 0 <> 0) ->
    dfs2_high_level_post g fadj_col_l fadj_row_l vis2_l sid_l vis2_l_ sid_l_
      root u n.
Proof.
  intros g fadj_col_l fadj_row_l vis2_l sid_l vis2_l_ sid_l_ root u n
    Hwf Hfaith Hverts Hroot Hu Huvis Hmono.
  destruct Hroot as [Hrootlo Hroothi].
  destruct Hu as [Hulo Huhi].
  unfold dfs2_high_level_post.
  exact (conj Hverts
    (conj Hwf
      (conj Hfaith
        (conj (conj Hrootlo Hroothi)
          (conj (conj Hulo Huhi) (conj Huvis Hmono)))))).
Qed.

(* Consolidated append-only helpers from group_00__dfs1-active. *)
Lemma visit1_pre_dfs1_sequence_step__dfs1_active :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z) (timer_v u: Z),
    (Zlength vis1 = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    pre_dfs1_sequence g radj_col_l radj_row_l vis1 fin_l timer_v -@ visit1 u -⥅
      (pre_dfs1_sequence g radj_col_l radj_row_l
        (replace_Znth u 1 vis1) fin_l timer_v) ♯ tt.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v u Hvlen Hub st0 Hpre.
  destruct Hpre as [Hpv [Hvi Hfin]].
  assert (HLu : (0 <= u < Zlength vis1)%Z) by (rewrite Hvlen; exact Hub).
  pose (st1 := MkSt (timer st0) (finish st0)
                     (fun w => visited1 st0 w \/ w = u)
                     (visited2 st0) (scc_id st0) (scc_next st0)).
  assert (Hnrm : (visit1 u).(MonadErr.nrm) st0 tt st1).
  { unfold visit1. simpl. split.
    - unfold st1. simpl. sets_unfold. intros w. split; intros Hw;
        destruct Hw as [Hw | Hw]; [left | subst w; right | left | subst w; right];
        try assumption; reflexivity.
    - unfold st1. simpl. repeat split; reflexivity. }
  exists st1. split; [exact Hnrm |].
  unfold pre_dfs1_sequence. split.
  - intros w Hw.
    assert (HLw : (0 <= w < Zlength vis1)%Z) by (rewrite Hvlen; exact Hw).
    unfold st1. simpl. split; intros Hvis.
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w.
        rewrite (Znth_replace_eq vis1 u 1 0 HLu). lia.
      * apply Z.eqb_neq in E.
        rewrite (Znth_replace_neq vis1 w u 1 0 HLw (proj1 HLu) E).
        destruct Hvis as [Hvis | Heq]; [apply (proj1 (Hpv w Hw)); exact Hvis | contradiction].
    + destruct (Z.eqb w u) eqn:E.
      * apply Z.eqb_eq in E. subst w. right. reflexivity.
      * apply Z.eqb_neq in E.
        rewrite (Znth_replace_neq vis1 w u 1 0 HLw (proj1 HLu) E) in Hvis.
        left. apply (proj2 (Hpv w Hw)). exact Hvis.
  - split.
    + intros w Hw Hvis. unfold st1 in Hvis. simpl in Hvis.
      destruct Hvis as [Hvis | Heq]; [eapply Hvi; eauto | subst w; contradiction].
    + unfold fin_sequence_rep in *. unfold st1. simpl. exact Hfin.
Qed.

Lemma dfs1_visit_sequence_decompose__dfs1_active :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1 fin_l: list Z) (timer_v u: Z)
         (X: unit -> KSt -> Prop),
    gvalid g ->
    (Zlength vis1 = adj_verts g)%Z ->
    (0 <= u < adj_verts g)%Z ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1 fin_l timer_v)
      (dfs_finish g u) X ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l
                (replace_Znth u 1 vis1) fin_l timer_v)
      (repeat_break (dfs_finish_repeat_body g u) ∅) X.
Proof.
  intros g radj_col_l radj_row_l vis1 fin_l timer_v u X Hg Hvlen Hub Hsafe.
  rewrite (dfs_finish_unfold_repeat g u Hg) in Hsafe.
  apply (highstepbind_derive (visit1 u)
           (fun _ => repeat_break (dfs_finish_repeat_body g u) ∅)
           (pre_dfs1_sequence g radj_col_l radj_row_l vis1 fin_l timer_v) tt
           (pre_dfs1_sequence g radj_col_l radj_row_l
             (replace_Znth u 1 vis1) fin_l timer_v)
           (visit1_pre_dfs1_sequence_step__dfs1_active
             g radj_col_l radj_row_l vis1 fin_l timer_v u Hvlen Hub)) in Hsafe.
  exact Hsafe.
Qed.

Lemma dfs1_entry_sequence_close__dfs1_active :
  forall (g: AdjGraph) (radj_col_l radj_row_l vis1_l fin_l: list Z) (u timer_v: Z)
         (X: unit -> KSt -> Prop),
    csr_wf1 g radj_col_l radj_row_l vis1_l fin_l ->
    csr1_faithful g radj_col_l radj_row_l ->
    (0 <= u < adj_verts g)%Z ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1_l fin_l timer_v)
      (dfs_finish g u) X ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l
                (replace_Znth u 1 vis1_l) fin_l timer_v)
      (dfs_finish_from g radj_col_l radj_row_l u (csr_lo u radj_row_l)) X.
Proof.
  intros g radj_col_l radj_row_l vis1_l fin_l u timer_v X Hwf Hfaith Hub Hsafe.
  destruct Hwf as [Hgv [Hlenrow [Hlenvis [Hlenfin [Hmof
    [Hlolo [Hhihi [Hneigh [Hlolohi Hmcap]]]]]]]]].
  assert (Hwf' : csr_wf1 g radj_col_l radj_row_l vis1_l fin_l).
  { unfold csr_wf1. repeat (split; [assumption |]); try assumption. }
  pose proof (dfs1_visit_sequence_decompose__dfs1_active
    g radj_col_l radj_row_l vis1_l fin_l timer_v u X
    Hgv Hlenvis Hub Hsafe) as Hdec.
  destruct Hdec as [sigma [Hpre Hsafe_repeat]].
  pose proof (proj1 Hpre) as Hvis.
  assert (Huvis : (0 <= u < Zlength vis1_l)%Z) by (rewrite Hlenvis; exact Hub).
  assert (Hvisu : visited1 sigma u).
  { apply (proj2 (Hvis u Hub)).
    rewrite (Znth_replace_eq vis1_l u 1 0 Huvis). discriminate. }
  set (lo := csr_lo u radj_row_l) in *.
  set (hi := csr_hi u radj_row_l) in *.
  assert (Hlo_eq : csr_lo u radj_row_l = lo) by reflexivity.
  assert (Hhi_eq : csr_hi u radj_row_l = hi) by reflexivity.
  assert (Hloi : (lo <= lo)%Z) by lia.
  assert (Hlohi : (0 <= hi - lo)%Z).
  { pose proof (Hlolohi u Hub) as Hlh. unfold lo, hi in *. lia. }
  set (n := Z.to_nat (hi - lo)).
  assert (Hfuel : Z.to_nat (hi - lo) = n) by reflexivity.
  assert (HA : forall e : Z * Z, (fun _ => False) e ->
    exists k, (lo <= k < lo)%Z /\ e = (Znth k radj_col_l 0, u)).
  { intros e Hfalse. contradiction. }
  assert (HB : forall k, (lo <= k < lo)%Z ->
    ~ (fun _ => False) (Znth k radj_col_l 0, u) ->
    visited1 sigma (Znth k radj_col_l 0)).
  { intros k Hrange _. lia. }
  assert (HE : forall j, (lo <= j < hi)%Z ->
    ~ visited1 sigma (Znth j radj_col_l 0) ->
    ~ (fun _ => False) (Znth j radj_col_l 0, u)).
  { intros j Hj Hnv Hfalse. exact Hfalse. }
  assert (Hsafe_cursor : safe sigma
    (dfs_finish_from g radj_col_l radj_row_l u lo) X).
  { eapply dfs_finish_from_sim;
      [exact Hlo_eq | exact Hhi_eq | exact Hwf' | exact Hfaith | exact Hub |
       exact Hfuel | exact Hloi | exact HA | exact HB | exact HE |
       exact Hvisu | exact Hsafe_repeat]. }
  exists sigma. split; assumption.
Qed.

Lemma dfs1_skip_sequence_close__dfs1_active :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_v: Z) (X: unit -> KSt -> Prop),
    (i < csr_hi u radj_row_l)%Z ->
    (0 <= Znth i radj_col_l 0 < adj_verts g)%Z ->
    Znth (Znth i radj_col_l 0) vis1_m 0 <> 0%Z ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1_m fin_m timer_v)
      (dfs_finish_from g radj_col_l radj_row_l u i) X ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1_m fin_m timer_v)
      (dfs_finish_from g radj_col_l radj_row_l u (i + 1)) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_v X
    Hilt Hrange Hvisited Hfrom.
  destruct Hfrom as [sigma [Hpre Hsafe]].
  destruct Hpre as [Hpv [Hinvalid Hfin]].
  assert (Hvis : visited1 sigma (Znth i radj_col_l 0)).
  { apply (proj2 (Hpv (Znth i radj_col_l 0) Hrange)). exact Hvisited. }
  unfold safeExec. exists sigma. split.
  - exact (conj Hpv (conj Hinvalid Hfin)).
  - unfold safe, weakestpre. split.
    + intros Herr. destruct Hsafe as [Hnoerr _]. apply Hnoerr.
      eapply dfs_finish_from_skip_err_imp; eauto.
    + intros a st' Hnrm. destruct Hsafe as [_ Hpost]. apply Hpost.
      apply (proj2 (dfs_finish_from_skip_step
        g radj_col_l radj_row_l u i sigma a st' Hilt Hvis)). exact Hnrm.
Qed.

Lemma dfs1_recurse_sequence_close__dfs1_active :
  forall (g: AdjGraph) (radj_col_l radj_row_l: list Z) (u i: Z)
         (vis1_m fin_m: list Z) (timer_v: Z) (X: unit -> KSt -> Prop),
    (i < csr_hi u radj_row_l)%Z ->
    (0 <= Znth i radj_col_l 0 < adj_verts g)%Z ->
    Znth (Znth i radj_col_l 0) vis1_m 0 = 0%Z ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1_m fin_m timer_v)
      (dfs_finish_from g radj_col_l radj_row_l u i) X ->
    safeExec (pre_dfs1_sequence g radj_col_l radj_row_l vis1_m fin_m timer_v)
      (bind (dfs_finish g (Znth i radj_col_l 0))
            (dfs_finish_fromK g radj_col_l radj_row_l u (i + 1))) X.
Proof.
  intros g radj_col_l radj_row_l u i vis1_m fin_m timer_v X
    Hilt Hrange Hvis0 Hfrom.
  destruct Hfrom as [sigma [Hpre Hsafe_parent]].
  destruct Hpre as [Hpv [Hinvalid Hfin]].
  set (v := Znth i radj_col_l 0) in *.
  assert (Hnvisv : ~ visited1 sigma v).
  { intro Hvis.
    assert (Hnz : Znth v vis1_m 0 <> 0%Z).
    { apply (proj1 (Hpv v Hrange)). exact Hvis. }
    lia. }
  unfold safeExec. exists sigma. split.
  - exact (conj Hpv (conj Hinvalid Hfin)).
  - unfold safe, weakestpre in *.
    destruct Hsafe_parent as [Hnoerr_parent Hpost_parent].
    split.
    + intro Herr_plain.
      apply Hnoerr_parent.
      apply (dfs_finish_from_recurse_err_imp
        g radj_col_l radj_row_l u i sigma Hilt Hnvisv).
      unfold dfs_finish_fromK in Herr_plain.
      apply bind_err_iff in Herr_plain.
      destruct Herr_plain as [Hdfserr | [r [smid [Hdfsnrm Hconterr]]]].
      * apply bind_err_iff. right.
        exists sigma. exists sigma. split.
        { split; [reflexivity | reflexivity]. }
        apply bind_err_iff. left. exact Hdfserr.
      * apply bind_err_iff. right.
        exists sigma. exists sigma. split.
        { split; [reflexivity | reflexivity]. }
        apply bind_err_iff. right.
        exists r. exists smid. split; [exact Hdfsnrm |].
        apply bind_err_iff.
        destruct (classic (@DFSFinishInv AdjGraph Z (Z * Z) KG g smid /\
                           visited1 smid v /\
                           visited1 sigma ⊆ visited1 smid)) as [Hassert | Hnotassert].
        -- right. exists tt. exists smid. split.
           ++ split; [reflexivity | exact Hassert].
           ++ exact Hconterr.
        -- left. exact Hnotassert.
    + intros r s' Hnrm_plain.
      apply Hpost_parent.
      apply (proj2 (dfs_finish_from_recurse_step
        g radj_col_l radj_row_l u i sigma r s' Hilt Hnvisv)).
      unfold dfs_finish_fromK in Hnrm_plain.
      apply bind_nrm_iff in Hnrm_plain.
      destruct Hnrm_plain as [rv [smid [Hdfsnrm Hcontnrm]]].
      assert (Hassert : @DFSFinishInv AdjGraph Z (Z * Z) KG g smid /\
                        visited1 smid v /\
                        visited1 sigma ⊆ visited1 smid).
      { destruct (classic (@DFSFinishInv AdjGraph Z (Z * Z) KG g smid /\
                           visited1 smid v /\
                           visited1 sigma ⊆ visited1 smid)) as [Hassert | Hnotassert].
        - exact Hassert.
        - exfalso. apply Hnoerr_parent.
          apply (dfs_finish_from_recurse_err_imp
            g radj_col_l radj_row_l u i sigma Hilt Hnvisv).
          apply bind_err_iff. right.
          exists sigma. exists sigma. split.
          { split; [reflexivity | reflexivity]. }
          apply bind_err_iff. right.
          exists rv. exists smid. split; [exact Hdfsnrm |].
          apply bind_err_iff. left. exact Hnotassert. }
      apply bind_nrm_iff.
      exists sigma. exists sigma. split.
      { split; [reflexivity | reflexivity]. }
      apply bind_nrm_iff.
      exists rv. exists smid. split; [exact Hdfsnrm |].
      apply bind_nrm_iff.
      exists tt. exists smid. split.
      * split; [reflexivity | exact Hassert].
      * exact Hcontnrm.
Qed.

(* Consolidated checked transpose-exit helpers. *)
Lemma csr_row_cover__transpose_exit :
  forall n row_l j,
    1 <= n ->
    csr_lo 0 row_l = 0 ->
    Zlength row_l = n + 1 ->
    0 <= j < m_of row_l ->
    exists u, 0 <= u < n /\ csr_lo u row_l <= j < csr_hi u row_l.
Proof.
  intros n row_l j Hn Hzero Hlen Hj.
  assert (Hend : csr_lo n row_l = m_of row_l).
  { unfold csr_lo, m_of.
    replace (Zlength row_l - 1) with n by lia.
    reflexivity. }
  assert (Hcover : forall k : nat,
    (Z.of_nat k <= n)%Z ->
    forall p, csr_lo 0 row_l <= p < csr_lo (Z.of_nat k) row_l ->
      exists u, 0 <= u < Z.of_nat k /\
        csr_lo u row_l <= p < csr_hi u row_l).
  { intro k. induction k as [|k IH]; intros Hkn p Hp.
    - simpl in Hp. lia.
    - destruct (Z_lt_ge_dec p (csr_lo (Z.of_nat k) row_l)) as [Hpk|Hpk].
      + destruct (IH ltac:(lia) p ltac:(lia)) as [u [Hu Hup]].
        exists u. split; [lia|exact Hup].
      + exists (Z.of_nat k).
        split; [lia|].
        unfold csr_hi, csr_lo in *.
        replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
        lia. }
  pose proof (Z2Nat.id n ltac:(lia)) as Hnat.
  specialize (Hcover (Z.to_nat n) ltac:(rewrite Hnat; lia) j).
  rewrite Hnat in Hcover.
  apply Hcover.
  rewrite Hend. lia.
Qed.

Lemma transpose_spec_from_completed_scatter__transpose_exit :
  forall g n m fadj_col_l fadj_row_l radj_col_l radj_row_l pos_l,
    1 <= n ->
    m = m_of fadj_row_l ->
    Zlength radj_col_l = m_of fadj_row_l ->
    Zlength radj_row_l = n + 1 ->
    csr_lo 0 radj_row_l = 0 ->
    csr_wf2_core g fadj_col_l fadj_row_l ->
    csr_lo 0 fadj_row_l = 0 ->
    csr2_faithful g fadj_col_l fadj_row_l ->
    AdjGraphValid g ->
    adj_verts g = n ->
    transpose_scatter_inv n m (csr_lo n fadj_row_l)
      fadj_col_l radj_row_l pos_l ->
    transpose_scatter_rows n m fadj_col_l radj_row_l ->
    transpose_scatter_contents g n (csr_lo n fadj_row_l)
      fadj_row_l fadj_col_l radj_row_l radj_col_l ->
    transpose_spec g fadj_col_l fadj_row_l radj_col_l radj_row_l n.
Proof.
  intros g n m fadj_col_l fadj_row_l radj_col_l radj_row_l pos_l
    Hn Hm Hcollen Hrowlen Hrowzero Hcore Hfrowzero Hfaith
    Hvalid Hverts Hinv Hrows Hcontents.
  assert (Hcursor : csr_lo n fadj_row_l = m).
  { rewrite Hm. unfold csr_lo, m_of.
    unfold csr_wf2_core in Hcore.
    destruct Hcore as [_ [Hfrowlen _]].
    rewrite Hverts in Hfrowlen.
    replace (Zlength fadj_row_l - 1) with n by lia.
    reflexivity. }
  rewrite Hcursor in Hinv, Hcontents.
  pose proof Hcore as Hcore_parts.
  unfold csr_wf2_core in Hcore_parts.
  destruct Hcore_parts as
    [_ [_ [_ [Hflo [Hfhi [_ [_ _]]]]]]].
  pose proof Hrows as Hrows_parts.
  unfold transpose_scatter_rows in Hrows_parts.
  destruct Hrows_parts as [Hrows_len [Hrows_m [Hrows_hi Hrows_order]]].
  pose proof Hinv as Hinv_parts.
  unfold transpose_scatter_inv in Hinv_parts.
  destruct Hinv_parts as [_ [_ [_ Hrows_bound]]].
  pose proof Hcontents as Hcontents_parts.
  unfold transpose_scatter_contents in Hcontents_parts.
  destruct Hcontents_parts as [Hcol_range _].
  unfold transpose_spec.
  split; [exact Hverts|].
  split; [exact Hvalid|].
  split; [lia|].
  split; [exact Hfaith|].
  split.
  - unfold csr_layout.
    split; [lia|].
    split; [lia|].
    split; [exact Hrowzero|].
    split.
    + intros u Hu.
      pose proof (Hrows_bound u ltac:(lia)) as [Hlo Hhi].
      pose proof (Hrows_hi u ltac:(lia)) as Hrow_hi.
      pose proof (zrange_count_value_nonneg 0 m u fadj_col_l) as Hcount.
      split; [exact Hlo|].
      split; [unfold csr_lo; lia|lia].
    + split.
      * intros u Hu.
        pose proof (Hrows_order u (u + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as Hstep.
        pose proof (Hrows_bound (u + 1) ltac:(lia)) as [Hlo Hhi].
        pose proof (Hrows_hi (u + 1) ltac:(lia)) as Hrow_hi.
        pose proof (zrange_count_value_nonneg 0 m (u + 1) fadj_col_l) as Hcount.
        unfold csr_lo in Hstep.
        lia.
      * intros j Hj.
        destruct (csr_row_cover__transpose_exit n radj_row_l j
          Hn Hrowzero Hrowlen ltac:(lia)) as [u [Hu Huj]].
        rewrite Hverts.
        apply (Hcol_range u j Hu).
        rewrite (Hrows_hi u Hu) in Huj.
        exact Huj.
  - eapply (csr1_faithful_of_transpose_scatter_contents
      g n m fadj_col_l fadj_row_l radj_row_l radj_col_l);
      try eassumption.
    + intros u Hu. apply Hflo. rewrite Hverts. exact Hu.
    + intros u Hu. rewrite Hm. apply Hfhi. rewrite Hverts. exact Hu.
Qed.
