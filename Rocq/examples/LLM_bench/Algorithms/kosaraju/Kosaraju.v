Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
(* From MonadLib.MonadErr Require Import StateRelBasic StateRelHoare FixpointLib. *)
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrLoop MonadErrHoarePartial MonadErrLoop.
From GraphLib Require Import graph_basic reachable_basic.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import SCC.
Require Import BourbakiWitt.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Class KosarajuGraph (G V E : Type) := {
  kos_graph :: Graph G V E;
  kos_gvalid :: GValid G;
  kos_stepvalid :: StepValid G V E;
  kos_unique :: StepUniqueDirected G V E;
  kos_finite :: FiniteGraph G V E;
}.

Section Kosaraju.

Context {G V E: Type}
        `{KG: KosarajuGraph G V E}
        (g: G)
        (g_valid: gvalid g).

(* VListBijective (NoDup vertex list = exact |V|) derived from FiniteGraph. *)
#[local] Instance kos_vlist : VListBijective G V E :=
  finite_graph_vlist_bijective G V E.


(* ================================================================= *)
(* Program State — non-primitive inductive record (avoids Coq 8.20   *)
(* primitive record restrictions on intros/subst/destruct/rewrite)   *)
(* ================================================================= *)

Inductive St : Type := MkSt {
  timer    : nat;
  finish   : V -> nat;
  visited1 : V -> Prop;
  visited2 : V -> Prop;
  scc_id   : V -> nat;
  scc_next : nat;
}.

Definition init_st : St :=
  MkSt 0 (fun _ => 0) (fun _ => False) (fun _ => False) (fun _ => 0) 0.

(* ================================================================= *)
(* cardV: cardinality of a vertex predicate, counted over the NoDup   *)
(* vertex list bijective_listV g (= exact number of vertices |V|).    *)
(* Underpins the timer bound: timer <= cardV(visited1) <= |V|.         *)
(* ================================================================= *)

Fixpoint count_pred {A: Type} (P: A -> Prop) (l: list A) : nat :=
  match l with
  | nil => 0
  | x :: xs => match excluded_middle_informative (P x) with left _ => S (count_pred P xs) | right _ => count_pred P xs end
  end.

Definition cardV (P: V -> Prop) : nat := count_pred P (bijective_listV g).

Definition count_step {A: Type} (P: A -> Prop) (x: A) (n: nat) : nat :=
  match excluded_middle_informative (P x) with left _ => S n | right _ => n end.

Lemma count_pred_le : forall {A: Type} (P: A -> Prop) (l: list A),
  count_pred P l <= length l.
Proof.
  intros A P l. induction l as [| a l IH]; simpl; [lia | destruct (excluded_middle_informative (P a)); lia].
Qed.

Lemma count_pred_false : forall {A: Type} (l: list A),
  count_pred (fun _ => False) l = 0.
Proof.
  intros A l. induction l as [| a l IH]; simpl; [reflexivity|].
  destruct (excluded_middle_informative False) as [Hfalse|_];
    [contradiction|exact IH].
Qed.

Lemma cardV_le : forall P, (cardV P <= length (bijective_listV g))%nat.
Proof. intros P. apply count_pred_le. Qed.

Lemma count_pred_cong : forall {A: Type} (P Q: A -> Prop) (l: list A),
  (forall x, In x l -> (P x <-> Q x)) -> count_pred P l = count_pred Q l.
Proof.
  intros A P Q l Hcg. induction l as [| a l IH]; simpl.
  - reflexivity.
  - assert (HPQ : P a <-> Q a) by (apply Hcg; left; reflexivity).
    destruct HPQ as [HP HQ].
    destruct (excluded_middle_informative (P a)) as [Hp | Hnp].
    + destruct (excluded_middle_informative (Q a)) as [Hq | Hnq].
      * f_equal. apply IH. intros y Hy. apply Hcg. right; exact Hy.
      * exfalso. apply Hnq. apply HP. exact Hp.
    + destruct (excluded_middle_informative (Q a)) as [Hq | Hnq].
      * exfalso. apply Hnp. apply HQ. exact Hq.
      * apply IH. intros y Hy. apply Hcg. right; exact Hy.
Qed.

(* If u does not occur in l, the predicates P and (P \/ =u) agree on l. *)
Lemma count_pred_or_notin : forall {A: Type} (P: A -> Prop) (u: A) (l: list A),
  ~ In u l -> count_pred (fun x => P x \/ u = x) l = count_pred P l.
Proof.
  intros A P u l Hni.
  apply count_pred_cong. intros x Hx.
  split.
  - intros [Hp | Heq]; [exact Hp | subst x; exfalso; apply Hni; exact Hx].
  - intros Hp. left; exact Hp.
Qed.

(* If u occurs (once, by NoDup) in l and ~ P u, adding "u=x" raises the count by 1. *)
Lemma count_pred_or_eq : forall {A: Type} (P: A -> Prop) (u: A) (l: list A),
  NoDup l -> In u l -> ~ P u ->
  count_pred (fun x => P x \/ u = x) l = S (count_pred P l).
Proof.
  intros A P u l. induction l as [| a l IH]; intros HND Hin HnPu.
  - simpl. destruct Hin.
  - simpl.
    destruct (excluded_middle_informative (u = a)) as [Hua | Hnua].
    + (* head a = u *)
      subst a. inversion HND; subst.
      destruct (excluded_middle_informative (P u)) as [Hpu | Hnpu]; [exfalso; apply HnPu; exact Hpu | clear Hnpu].
      destruct (excluded_middle_informative (P u \/ u = u)) as [_ | Hnd]; [ | exfalso; apply Hnd; right; reflexivity].
      rewrite count_pred_or_notin by assumption. reflexivity.
    + (* head a <> u, u in tail *)
      assert (Hinl : In u l) by (destruct Hin as [H | Hinl]; [exfalso; apply Hnua; symmetry; exact H | exact Hinl]).
      assert (HNDl : NoDup l) by (inversion HND; assumption).
      assert (HIH : count_pred (fun x => P x \/ u = x) l = S (count_pred P l)) by (apply IH; assumption).
      destruct (excluded_middle_informative (P a)) as [Hpa | Hnpa].
      * destruct (excluded_middle_informative (P a \/ u = a)) as [_ | Hnd]; [ | exfalso; apply Hnd; left; exact Hpa].
        rewrite HIH. reflexivity.
      * destruct (excluded_middle_informative (P a \/ u = a)) as [Hd | Hnd].
        -- exfalso. destruct Hd as [Hp | Heq]; [apply Hnpa; exact Hp | apply Hnua; exact Heq].
        -- rewrite HIH. reflexivity.
Qed.

(* visit1 u (u valid & not yet visited1) increases cardV(visited1) by exactly 1. *)
Lemma cardV_visit1 : forall s1 s2 u,
  visited1 s2 == visited1 s1 ∪ Sets.singleton u ->
  vvalid g u -> ~ visited1 s1 u ->
  cardV (visited1 s2) = S (cardV (visited1 s1)).
Proof.
  intros s1 s2 u Heq Hvu Hnv. unfold cardV.
  transitivity (count_pred (fun v => visited1 s1 v \/ u = v) (bijective_listV g)).
  - apply count_pred_cong. intros x _. sets_unfold in Heq. apply Heq.
  - apply count_pred_or_eq;
      [ apply bijective_listV_NoDup; exact g_valid
      | exact (proj2 (bijective_vertices g g_valid u) Hvu)
      | exact Hnv ].
Qed.

(* count_pred is monotone under pointwise implication (subset on the list's elements). *)
Lemma count_pred_mono : forall {A: Type} (P Q: A -> Prop) (l: list A),
  (forall x, In x l -> P x -> Q x) ->
  count_pred Q l >= count_pred P l.
Proof.
  intros A P Q l. induction l as [| a l' IH]; intros Hle; simpl.
  - lia.
  - assert (Hle_a : P a -> Q a) by (intro HPa; exact (Hle a (or_introl eq_refl) HPa)).
    assert (Hle_l' : forall x, In x l' -> P x -> Q x)
      by (intros x Hx HPx; exact (Hle x (or_intror Hx) HPx)).
    specialize (IH Hle_l').
    destruct (excluded_middle_informative (P a)) as [Hpa | Hnpa];
      destruct (excluded_middle_informative (Q a)) as [Hqa | Hnqa].
    + lia.
    + exfalso. apply Hnqa. apply Hle_a. exact Hpa.
    + lia.
    + lia.
Qed.

(* cardV is monotone: P ⊆ Q (pointwise on V) implies cardV P <= cardV Q. *)
Lemma cardV_mono : forall (P Q: V -> Prop),
  (forall x, P x -> Q x) -> (cardV P <= cardV Q)%nat.
Proof.
  intros P Q Hle. unfold cardV.
  assert (Hge := count_pred_mono P Q (bijective_listV g) (fun x _ => Hle x)).
  lia.
Qed.

(* visit1 u preserves the non-strict bound cardV(visited1) >= timer, with no
   precondition on whether u was already visited. Used to thread the assertS
   timer-bound through DFS_finish_f's loop without needing ~visited1/vvalid. *)
Lemma cardV_visit1_nosteps : forall s1 s2 u,
  visited1 s2 == visited1 s1 ∪ Sets.singleton u ->
  timer s2 = timer s1 ->
  cardV (visited1 s1) >= timer s1 ->
  cardV (visited1 s2) >= timer s2.
Proof.
  intros s1 s2 u Heq Htimer Hle.
  rewrite Htimer.
  assert (Hsub : forall x, visited1 s1 x -> visited1 s2 x).
  { intros x Hx. sets_unfold in Heq. apply Heq. left. exact Hx. }
  assert (Hmono := cardV_mono (visited1 s1) (visited1 s2) Hsub).
  lia.
Qed.

(* visit1 preserves the number of vertices with assigned finish times. *)
Lemma cardV_visit1_finished : forall s1 s2,
  finish s2 = finish s1 ->
  cardV (fun v => finish s2 v <> 0) =
  cardV (fun v => finish s1 v <> 0).
Proof.
  intros s1 s2 Hfin. unfold cardV.
  apply count_pred_cong. intros x _.
  rewrite Hfin. reflexivity.
Qed.

(* set_finish changes exactly one valid vertex from unfinished (0) to finished. *)
Lemma cardV_set_finish_zero_to_nonzero : forall s1 s2 u t,
  vvalid g u ->
  finish s1 u = 0 ->
  finish s2 u = S t ->
  (forall v, v <> u -> finish s2 v = finish s1 v) ->
  cardV (fun v => finish s2 v <> 0) =
  S (cardV (fun v => finish s1 v <> 0)).
Proof.
  intros s1 s2 u t Hvu Hzero Hset Hother. unfold cardV.
  transitivity
    (count_pred (fun v => finish s1 v <> 0 \/ u = v) (bijective_listV g)).
  - apply count_pred_cong. intros x _.
    split.
    + intros Hnz.
      destruct (classic (u = x)) as [Hux | Hux].
      * right; exact Hux.
      * left. rewrite <- (Hother x) by (intro Hxu; apply Hux; symmetry; exact Hxu).
        exact Hnz.
    + intros [Hnz | Hux].
      * destruct (classic (u = x)) as [Hu | Hne].
        -- subst x. rewrite Hzero in Hnz. contradiction.
        -- rewrite (Hother x) by (intro Hxu; apply Hne; symmetry; exact Hxu).
           exact Hnz.
      * subst x. rewrite Hset. discriminate.
  - apply count_pred_or_eq.
    + apply bijective_listV_NoDup; exact g_valid.
    + exact (proj2 (bijective_vertices g g_valid u) Hvu).
    + intro Hnz. rewrite Hzero in Hnz. exact (Hnz eq_refl).
Qed.

Definition FinishedCount (s : St) : Prop :=
  timer s = cardV (fun v => finish s v <> 0).

Definition UnvisitedFinishZero (s : St) : Prop :=
  forall v, ~ visited1 s v -> finish s v = 0.

Lemma FinishedCount_finish_cong : forall s1 s2,
  timer s2 = timer s1 ->
  finish s2 = finish s1 ->
  FinishedCount s1 ->
  FinishedCount s2.
Proof.
  intros s1 s2 Htimer Hfin Hfc.
  unfold FinishedCount in *.
  rewrite Htimer, Hfin. exact Hfc.
Qed.

Lemma UnvisitedFinishZero_visit1 : forall s1 s2 u,
  visited1 s2 == visited1 s1 ∪ Sets.singleton u ->
  finish s2 = finish s1 ->
  UnvisitedFinishZero s1 ->
  UnvisitedFinishZero s2.
Proof.
  intros s1 s2 u Hvis Hfin Hzero v Hnot.
  rewrite Hfin.
  apply Hzero.
  intro Hv.
  apply Hnot.
  sets_unfold in Hvis.
  apply Hvis. left. exact Hv.
Qed.

Lemma UnvisitedFinishZero_finish_update : forall s1 s2 u,
  visited1 s2 = visited1 s1 ->
  (forall v, v <> u -> finish s2 v = finish s1 v) ->
  UnvisitedFinishZero s1 ->
  visited1 s1 u ->
  UnvisitedFinishZero s2.
Proof.
  intros s1 s2 u Hvis Hfin_other Hzero Hu v Hnot.
  destruct (classic (v = u)) as [-> | Hne].
  - exfalso. apply Hnot. rewrite Hvis. exact Hu.
  - rewrite Hfin_other by exact Hne.
    apply Hzero. intro Hv. apply Hnot. rewrite Hvis. exact Hv.
Qed.

Lemma FinishedCount_set_finish_zero : forall s1 s2 u t,
  vvalid g u ->
  finish s1 u = 0 ->
  timer s2 = S (timer s1) ->
  finish s2 u = S t ->
  (forall v, v <> u -> finish s2 v = finish s1 v) ->
  FinishedCount s1 ->
  FinishedCount s2.
Proof.
  intros s1 s2 u t Hvu Hzero Htimer Hfinu Hfinother Hfc.
  unfold FinishedCount in *.
  rewrite Htimer, Hfc.
  symmetry.
  apply cardV_set_finish_zero_to_nonzero with (u := u) (t := t); assumption.
Qed.

Definition custom {Σ A: Type} (nrm: Σ -> A -> Σ -> Prop): MonadErr.M Σ A := {|
  MonadErr.nrm := nrm;
  MonadErr.err := ∅
|}.

Definition visit1 (u: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    visited1 st2 == visited1 st1 ∪ Sets.singleton u /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited2 st2 = visited2 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1).
    

Definition visit2 (u: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    visited2 st2 == visited2 st1 ∪ Sets.singleton u /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1).

Definition set_finish (u: V) (t: nat): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    timer st2 = S (timer st1) /\
    finish st2 u = S t /\
    (forall v, v <> u -> finish st2 v = finish st1 v) /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1).

Definition set_scc_id (u root: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    scc_id st2 u = scc_id st1 root /\
    (forall v, v <> u -> scc_id st2 v = scc_id st1 v) /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1 /\
    scc_next st2 = scc_next st1).

Definition set_scc_root_id (u: V): MonadErr.M St unit :=
  custom (fun st1 _ st2 =>
    scc_id st2 u = scc_next st1 /\
    scc_next st2 = S (scc_next st1) /\
    (forall v, v <> u -> scc_id st2 v = scc_id st1 v) /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1).

(* ================================================================= *)
(* Inner DFS — Phase 1 (reversed graph)                              *)
(* ================================================================= *)

Definition step_rev (x y: V) : Prop := step g y x.
Definition reachable_rev (x y : V) : Prop := SCC.reachable_rev g x y.
Definition mutually_reachable (u v : V) : Prop := SCC.mutually_reachable g u v.

Definition TimerDominates (s: St) : Prop :=
  forall v, visited1 s v -> finish s v <= timer s.

Definition TimerDominates_except (s: St) (u: V) : Prop :=
  forall v, visited1 s v -> v <> u -> finish s v <= timer s.

Definition ReachRevClosed (s: St) : Prop :=
  forall v w, visited1 s v -> reachable_rev v w -> visited1 s w.

Definition DFSFinishInvCore (s : St) : Prop :=
  FinishedCount s /\
  UnvisitedFinishZero s /\
  cardV (visited1 s) >= timer s /\
  TimerDominates s.

Definition DFSFinishScoped (s : St) : Prop :=
  (forall v, ~ vvalid g v -> ~ visited1 s v) /\
  (forall v, ~ vvalid g v -> finish s v = 0).

Definition DFSFinishInv (s : St) : Prop :=
  DFSFinishInvCore s /\ DFSFinishScoped s.

Definition DFSFinishFrame (base : St) (_ : unit) (st : St) : Prop :=
  DFSFinishInv st /\
  visited1 base ⊆ visited1 st /\
  (forall x, visited1 base x -> finish st x = finish base x) /\
  visited2 st = visited2 base /\
  scc_id st = scc_id base /\
  scc_next st = scc_next base.

Lemma DFSFinishFrame_inv : forall base r st,
  DFSFinishFrame base r st -> DFSFinishInv st.
Proof. intros base r st [Hinv _]. exact Hinv. Qed.

Lemma DFSFinishInv_card_timer : forall s,
  DFSFinishInv s -> cardV (visited1 s) >= timer s.
Proof.
  intros s [[_ [_ [Hcard _]]] _]. exact Hcard.
Qed.

Lemma DFSFinishInv_core : forall s,
  DFSFinishInv s -> DFSFinishInvCore s.
Proof. intros s [Hcore _]. exact Hcore. Qed.

Lemma DFSFinishInv_scoped : forall s,
  DFSFinishInv s -> DFSFinishScoped s.
Proof. intros s [_ Hscoped]. exact Hscoped. Qed.

Lemma DFSFinishInv_finished_count : forall s,
  DFSFinishInv s -> FinishedCount s.
Proof. intros s [[H _] _]. exact H. Qed.

Lemma DFSFinishInv_unvisited_zero : forall s,
  DFSFinishInv s -> UnvisitedFinishZero s.
Proof. intros s [[_ [H _]] _]. exact H. Qed.

Lemma DFSFinishInv_timer_dominates : forall s,
  DFSFinishInv s -> TimerDominates s.
Proof. intros s [[_ [_ [_ H]]] _]. exact H. Qed.

Lemma DFSFinishScoped_visit1 : forall s0 st u,
  DFSFinishScoped s0 ->
  vvalid g u ->
  (visit1 u).(MonadErr.nrm) s0 tt st ->
  DFSFinishScoped st.
Proof.
  intros s0 st u [Hvis_invalid Hfin_invalid] Hvalid_u Hnrm.
  cbv beta iota delta [visit1 custom] in Hnrm.
  destruct Hnrm as [Hvis [_ [Hfin _]]].
  split.
  - intros v Hinvalid_v Hvisited.
    sets_unfold in Hvis.
    destruct (proj1 (Hvis v) Hvisited) as [Hvisited0 | Hu].
    + exact (Hvis_invalid v Hinvalid_v Hvisited0).
    + subst v. contradiction.
  - intros v Hinvalid_v.
    rewrite Hfin. exact (Hfin_invalid v Hinvalid_v).
Qed.

Lemma DFSFinishScoped_set_finish : forall s0 st u t,
  DFSFinishScoped s0 ->
  vvalid g u ->
  (set_finish u t).(MonadErr.nrm) s0 tt st ->
  DFSFinishScoped st.
Proof.
  intros s0 st u t [Hvis_invalid Hfin_invalid] Hvalid_u Hnrm.
  cbv beta iota delta [set_finish custom] in Hnrm.
  destruct Hnrm as [_ [_ [Hfin_other [Hv1 _]]]].
  split.
  - intros v Hinvalid_v Hvisited.
    rewrite Hv1 in Hvisited.
    exact (Hvis_invalid v Hinvalid_v Hvisited).
  - intros v Hinvalid_v.
    rewrite Hfin_other.
    + exact (Hfin_invalid v Hinvalid_v).
    + intro Heq. subst v. contradiction.
Qed.

Lemma DFSFinishInv_visit1_nrm : forall s0 st u,
  DFSFinishInv s0 ->
  vvalid g u ->
  ~ visited1 s0 u ->
  (visit1 u).(MonadErr.nrm) s0 tt st ->
  DFSFinishInv st.
Proof.
  intros s0 st u Hinv Hvalid Hnot Hnrm.
  pose proof Hnrm as Hnrm_scoped.
  cbv beta iota delta [visit1 custom] in Hnrm.
  destruct Hnrm as [Hvis [Htimer [Hfin _]]].
  destruct Hinv as [[Hfc [Hzero [Hcard Htd]]] Hscoped].
  unfold DFSFinishInv, DFSFinishInvCore.
  split.
  - split.
    + unfold FinishedCount in *. rewrite Htimer, Hfin. exact Hfc.
    + split.
      * eapply UnvisitedFinishZero_visit1; eauto.
      * split.
        -- eapply cardV_visit1_nosteps; eauto.
        -- unfold TimerDominates in *. intros x Hx.
           rewrite Hfin.
           sets_unfold in Hvis.
           destruct (proj1 (Hvis x) Hx) as [Hx0 | Hu].
           ++ rewrite Htimer. apply Htd. exact Hx0.
           ++ subst x. rewrite Htimer. rewrite Hzero by exact Hnot. lia.
  - eapply DFSFinishScoped_visit1; eauto.
Qed.

Lemma cardV_with_extra_valid : forall (P Q : V -> Prop) u,
  (forall v, P v -> Q v) ->
  vvalid g u ->
  Q u ->
  ~ P u ->
  S (cardV P) <= cardV Q.
Proof.
  intros P Q u HPQ Hvalid HQ HnotP.
  assert (Hadd : cardV (fun v => P v \/ u = v) = S (cardV P)).
  { unfold cardV. apply count_pred_or_eq.
    - apply bijective_listV_NoDup; exact g_valid.
    - exact (proj2 (bijective_vertices g g_valid u) Hvalid).
    - exact HnotP. }
  assert (Hmono : cardV (fun v => P v \/ u = v) <= cardV Q).
  { apply cardV_mono. intros v [HP | Hu]; [apply HPQ; exact HP|subst; exact HQ]. }
  lia.
Qed.

Lemma DFSFinishInv_strict_unfinished : forall st u,
  DFSFinishInv st ->
  vvalid g u ->
  visited1 st u ->
  finish st u = 0 ->
  S (timer st) <= cardV (visited1 st).
Proof.
  intros st u [[Hfc [Hzero [Hcard Htd]]] _] Hvalid Hvis Hfin0.
  unfold FinishedCount in Hfc.
  rewrite Hfc.
  apply cardV_with_extra_valid with (P := fun v => finish st v <> 0) (u := u).
  - intros v Hnz.
    destruct (classic (visited1 st v)) as [Hv|Hnv]; [exact Hv|].
    rewrite (Hzero v Hnv) in Hnz. contradiction.
  - exact Hvalid.
  - exact Hvis.
  - rewrite Hfin0. intro Hnz. apply Hnz. reflexivity.
Qed.

Lemma DFSFinishInv_init : DFSFinishInv init_st.
Proof.
  assert (Hfinish_zero_count : cardV (fun _ : V => 0 <> 0) = 0).
  { unfold cardV.
    transitivity (count_pred (fun _ : V => False) (bijective_listV g)).
    - apply count_pred_cong. intros x _. split; intros H; [lia|contradiction].
    - apply count_pred_false. }
  unfold DFSFinishInv, DFSFinishInvCore, DFSFinishScoped. split.
  - split.
    + unfold FinishedCount, init_st. cbn.
      rewrite Hfinish_zero_count. reflexivity.
    + split.
      * unfold UnvisitedFinishZero, init_st. intros v _. reflexivity.
      * split.
        -- unfold init_st, cardV. cbn. rewrite count_pred_false. lia.
        -- unfold TimerDominates, init_st. intros v H. contradiction.
  - split.
    + unfold init_st. intros v _ H. exact H.
    + unfold init_st. intros v _. reflexivity.
Qed.

(** Local inductive for forward reachability — avoids SetsClass shadowing
    of clos_refl_trans.  rf_step extends on the RIGHT so that structural
    recursion decomposes from the end, matching Hneigh's one-step backward
    reasoning. *)
Inductive reach_fwd (v : V) : V -> Prop :=
| rf_refl : reach_fwd v v
| rf_step z w : reach_fwd v z -> step g z w -> reach_fwd v w.

Lemma reachable_rev_to_reach_fwd : forall x y,
  reachable_rev y x -> reach_fwd x y.
Proof.
  intros x y H.
  unfold reachable_rev in H.
  refine (SCC.reachable_rev_ind _ (fun a b => reach_fwd b a) _ _ _ _ H).
  - intros u0. constructor.
  - intros u0 v0 w0 Hstep Hrev IH.
    econstructor 2.
    + exact IH.
    + unfold step_rev in Hstep; exact Hstep.
Qed.

Lemma reachable_to_reach_fwd : forall x y,
  reachable g x y -> reach_fwd x y.
Proof.
  intros x y H.
  apply reachable_iff_reachable_rev in H.
  apply reachable_rev_to_reach_fwd; exact H.
Qed.

Lemma reach_fwd_to_reachable : forall x y,
  reach_fwd x y -> reachable g x y.
Proof.
  induction 1.
  - apply reachable_iff_reachable_rev; apply SCC.rr_refl.
  - eapply reachable_step_reachable; eauto.
Qed.

Definition DFS_finish_f
           (W: V -> MonadErr.M St unit)
           (u: V): MonadErr.M St unit :=
  visit1 u;;
  repeat_break
    (fun e_set =>
       choice
        (e <- any E;;
          v <- any V;;
          assume (fun _ => ~ e ∈ e_set);;
          assume (fun st => ~ visited1 st v);;
           assume (fun _ => step_aux g e v u);;
           pre <- get (fun st pre => pre = st);;
           W v;;
           assertS (fun st =>
             DFSFinishInv st /\ visited1 st v /\ visited1 pre ⊆ visited1 st);;
           continue (e_set ∪ Sets.singleton e))
        (assume (fun st =>
                     forall (e:E) (v:V),
                      step_aux g e v u ->
                      e ∈ e_set \/ visited1 st v);;
          assertS (fun st => DFSFinishInv st);;
          assertS (fun st => timer st = cardV (fun v => finish st v <> 0));;
          t <- get (fun st t => t = timer st);;
          set_finish u t;;
          break tt))
    ∅.

Definition DFS_finish (u: V): MonadErr.M St unit :=
  BW_fix (DFS_finish_f) u.

(* ================================================================= *)
(* Inner DFS — Phase 2 (original graph, assign SCC root)             *)
(* ================================================================= *)

Definition DFS_scc_f
           (root: V)
           (W: V -> MonadErr.M St unit)
           (u: V): MonadErr.M St unit :=
  visit2 u;;
  set_scc_id u root;;
  repeat_break
    (fun e_set =>
       choice
         (e <- any E;;
          v <- any V;;
          assume (fun _ => ~ e ∈ e_set);;
          assume (fun st => ~ visited2 st v);;
          assume (fun _ => step_aux g e u v);;
          W v;;
          continue (e_set ∪ Sets.singleton e))
         (assume (fun st =>
                    forall (e:E) (v:V),
                      step_aux g e u v ->
                      e ∈ e_set \/ visited2 st v);;
          (* sid-stability assertS: at loop break, u's scc_id equals root's.
             Conveyed to the C refinement via Hoare_assertS_bind / safeExec,
             so the C-side dfs2 return witness can discharge sid-stability
             sampling subgoals without a forall in the loop invariant. *)
          assertS (fun st => scc_id st u = scc_id st root);;
          break tt))
    ∅.

Definition DFS_scc (root u: V): MonadErr.M St unit :=
  BW_fix (DFS_scc_f root) u.

(* ================================================================= *)
(* Pick an unvisited vertex with maximal finish number               *)
(* ================================================================= *)

Definition pick_unvisited1 : MonadErr.M St V :=
  get (fun st v => vvalid g v /\ ~ visited1 st v).

Definition pick_unvisited2 : MonadErr.M St V :=
  get (fun st v =>
    vvalid g v /\
    ~ visited2 st v /\
    forall w, ~ visited2 st w -> finish st v >= finish st w).

(* ================================================================= *)
(* Full Kosaraju algorithm                                           *)
(* ================================================================= *)

Definition kosaraju_finish_f
           (W: unit -> MonadErr.M St unit)
           (u: unit): MonadErr.M St unit :=
  choice
    (u <- pick_unvisited1;;
     DFS_finish u;;
     W tt)
    (assume (fun st => forall v, visited1 st v);;
     skip).

Definition kosaraju_finish : MonadErr.M St unit :=
  BW_fix kosaraju_finish_f tt.

Fixpoint kosaraju_finish_schedule_iter
         (root_at : nat -> V) (idx fuel : nat) : MonadErr.M St unit :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      let root := root_at idx in
      if_else (fun st => visited1 st root)
        (kosaraju_finish_schedule_iter root_at (S idx) fuel')
        (DFS_finish root;;
         kosaraju_finish_schedule_iter root_at (S idx) fuel')
  end.

Definition kosaraju_finish_schedule
           (root_at : nat -> V) (start fuel : nat) : MonadErr.M St unit :=
  kosaraju_finish_schedule_iter root_at start fuel.

Lemma kosaraju_finish_schedule_done :
  forall root_at start,
    kosaraju_finish_schedule root_at start O = ret tt.
Proof.
  intros. unfold kosaraju_finish_schedule. reflexivity.
Qed.

Lemma kosaraju_finish_schedule_step :
  forall root_at start fuel,
    kosaraju_finish_schedule root_at start (S fuel) =
    let root := root_at start in
    if_else (fun st => visited1 st root)
      (kosaraju_finish_schedule root_at (S start) fuel)
      (DFS_finish root;;
       kosaraju_finish_schedule root_at (S start) fuel).
Proof.
  intros. unfold kosaraju_finish_schedule. reflexivity.
Qed.

Definition kosaraju_scc_f
           (W: unit -> MonadErr.M St unit)
           (u: unit): MonadErr.M St unit :=
  choice
    (u <- pick_unvisited2;;
     set_scc_root_id u;;
     DFS_scc u u;;
     W tt)
    (assume (fun st => forall v, visited2 st v);;
     skip).

Definition kosaraju_scc : MonadErr.M St unit :=
  BW_fix kosaraju_scc_f tt.

Fixpoint kosaraju_scc_schedule_iter
         (root_at : nat -> V) (idx fuel : nat) : MonadErr.M St unit :=
  match fuel with
  | O => ret tt
  | S fuel' =>
      let root := root_at idx in
      if_else (fun st => visited2 st root)
        (kosaraju_scc_schedule_iter root_at (S idx) fuel')
        (visit2 root;;
         set_scc_id root root;;
         DFS_scc root root;;
         kosaraju_scc_schedule_iter root_at (S idx) fuel')
  end.

Definition kosaraju_scc_schedule
           (root_at : nat -> V) (start fuel : nat) : MonadErr.M St unit :=
  kosaraju_scc_schedule_iter root_at start fuel.

Lemma kosaraju_scc_schedule_done :
  forall root_at start,
    kosaraju_scc_schedule root_at start O = ret tt.
Proof.
  intros. unfold kosaraju_scc_schedule. reflexivity.
Qed.

Lemma kosaraju_scc_schedule_step :
  forall root_at start fuel,
    kosaraju_scc_schedule root_at start (S fuel) =
    let root := root_at start in
    if_else (fun st => visited2 st root)
      (kosaraju_scc_schedule root_at (S start) fuel)
      (visit2 root;;
       set_scc_id root root;;
       DFS_scc root root;;
       kosaraju_scc_schedule root_at (S start) fuel).
Proof.
  intros. unfold kosaraju_scc_schedule. reflexivity.
Qed.

Definition kosaraju : MonadErr.M St unit :=
  kosaraju_finish;; kosaraju_scc.

(* ================================================================= *)
(* 0. Hoare Helper Theorems (from C10909)                            *)
(* ================================================================= *)

(** Lifts a pointwise Hoare triple to a general precondition P. *)
Theorem Hoare_normalize {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall s0, P s0 -> Hoare (fun s => s = s0) f Q) ->
    Hoare P f Q.
Proof.
  firstorder.
Qed.

(** If P holds at s0, then assume P;; f has the Hoare triple for
    singleton precondition s = s0. Used for assume-guard elimination. *)
Theorem Hoare_normal_assume_bind {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q: A -> Σ -> Prop) s0,
    (P s0 -> Hoare (fun s => s = s0) f Q) ->
    (Hoare (fun s => s = s0) (assume P;; f) Q).
Proof.
  intros P f Q s0 H.
  apply Hoare_assumeS_bind.
  apply Hoare_normalize.
  intros s1 [Hs HP]. subst. apply H. exact HP.
Qed.

(** BW_fix induction principle: if f W a satisfies Q a s0 under the
    hypothesis that W a does, then BW_fix f a also satisfies Q a s0. *)
Theorem Hoare_normal_LFix {Σ A B: Type}:
  forall (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> MonadErr.M Σ B) -> (A -> MonadErr.M Σ B)),
    (forall (W: A -> MonadErr.M Σ B),
       (forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, Hoare (fun s => s = s0) (BW_fix f a) (Q a s0)).
Proof.
  intros Q f H s0 a.
  assert (Hiter : forall n s0 a, Hoare (fun s => s = s0) (Nat.iter n f bot a) (Q a s0)).
  { intro n. induction n; intros s0' a'.
    - unfold Hoare; split; simpl; sets_unfold; intros; tauto.
    - simpl. apply H. exact IHn. }
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  split.
  - intros b s1 s2 Hs1 Hnrm. destruct Hnrm as [n Hnrm].
    destruct (Hiter n s0 a) as [Hn _]. eapply Hn; eauto.
  - intros s1 Hs1 Herr. destruct Herr as [n Herr].
    destruct (Hiter n s0 a) as [_ He]. eapply He; eauto.
Qed.

(** BW_fix induction with an invariant R closed under the recursive step.
    Variant of Hoare_normal_LFix carrying an extra hypothesis R s0. *)
Theorem Hoare_normal_LFix_closed {Σ A B: Type}:
  forall (R: Σ -> Prop)
         (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> MonadErr.M Σ B) -> (A -> MonadErr.M Σ B)),
    (forall (W: A -> MonadErr.M Σ B),
       (forall s0 a, R s0 -> Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, R s0 -> Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, R s0 -> Hoare (fun s => s = s0) (BW_fix f a) (Q a s0)).
Proof.
  intros R Q f H s0 a HR.
  assert (Hiter : forall n s0 a, R s0 -> Hoare (fun s => s = s0) (Nat.iter n f bot a) (Q a s0)).
  { intro n. induction n; intros s0' a' HR'.
    - unfold Hoare; split; simpl; sets_unfold; intros; tauto.
    - simpl. apply H. exact IHn. exact HR'. }
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  split.
  - intros b s1 s2 Hs1 Hnrm. destruct Hnrm as [n Hnrm].
    destruct (Hiter n s0 a HR) as [Hn _]. eapply Hn; eauto.
  - intros s1 Hs1 Herr. destruct Herr as [n Herr].
    destruct (Hiter n s0 a HR) as [_ He]. eapply He; eauto.
Qed.

(* ================================================================= *)
(* 1. Helper Hoare Lemmas for State Primitives                       *)
(* ================================================================= *)

(** visit1 u adds u to visited1; all other fields unchanged.
    Proved property: visited1 s' == visited1 s0 ∪ {u} *)
Lemma Hoare_visit1 : forall s0 u P,
  (forall s1, visited1 s1 == visited1 s0 ∪ Sets.singleton u -> P s1) ->
  Hoare (fun st => st = s0) (visit1 u) (fun _ => P).
Proof.
  intros s0 u P H.
  unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [visit1 custom] in Hprog.
    destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
    apply H; assumption.
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

(** visit2 u adds u to visited2; all other fields unchanged.
    Proved property: visited2 s' == visited2 s0 ∪ {u} *)
Lemma Hoare_visit2 : forall s0 u P,
  (forall s1, visited2 s1 == visited2 s0 ∪ Sets.singleton u -> P s1) ->
  Hoare (fun st => st = s0) (visit2 u) (fun _ => P).
Proof.
  intros s0 u P H.
  unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [visit2 custom] in Hprog.
    destruct Hprog as [Hv [Htimer [Hfin [Hv1 [Hsid _]]]]].
    apply H; assumption.
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

(** get timer then set_finish u t stores one plus the current timer as finish[u],
    increments timer, and preserves finish for other vertices.
    Proved property: timer s' = S(timer s0) /\ finish s' u = S (timer s0) /\ ... *)
Lemma Hoare_set_finish : forall s0 u,
  Hoare (fun st => st = s0) (t <- get (fun st t => t = timer st);; set_finish u t)
    (fun _ s' =>
       timer s' = S (timer s0) /\
       finish s' u = S (timer s0) /\
       (forall v, v <> u -> finish s' v = finish s0 v) /\
       visited1 s' = visited1 s0 /\
       visited2 s' = visited2 s0 /\
       scc_id s' = scc_id s0 /\
       scc_next s' = scc_next s0).
Proof.
  intros s0 u.
  unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [MonadErr.bind MonadErr.nrm_nrm get set_finish custom] in Hprog.
    destruct Hprog as [t [s' [[Ht Hs'] Hset]]].
    rewrite <- Hs' in Hset.
    destruct Hset as [Htimer [Hfinish [Hfinish_other [Hv1 [Hv2 [Hsid Hnext]]]]]].
    split; [exact Htimer|].
    split; [rewrite <- Ht; exact Hfinish|].
    split; [exact Hfinish_other|].
    split; [exact Hv1|].
    split; [exact Hv2|].
    split; [exact Hsid|exact Hnext].
  - intros s1 Hs1 Herr. exfalso.
    cbv beta iota delta [MonadErr.bind MonadErr.nrm_err get set_finish custom] in Herr.
    sets_unfold in Herr. firstorder.
Qed.

Lemma Hoare_set_finish_raw : forall s0 u t,
  Hoare (fun st => st = s0) (set_finish u t)
    (fun _ s' =>
       timer s' = S (timer s0) /\
       finish s' u = S t /\
       (forall v, v <> u -> finish s' v = finish s0 v) /\
       visited1 s' = visited1 s0 /\
       visited2 s' = visited2 s0 /\
       scc_id s' = scc_id s0 /\
       scc_next s' = scc_next s0).
Proof.
  intros s0 u t.
  unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [set_finish custom] in Hprog.
    exact Hprog.
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

(* ================================================================= *)
(* 2. Inner DFS Phase 1 — Core Properties                            *)
(* ================================================================= *)

(** [DFS_finish_f_preserves_excess]: the single-unroll step underlying
    the timer/cardinality side condition. For any recursive body W that itself preserves
    the excess cardV(visited1) - timer (parameterised by k), DFS_finish_f W
    preserves it too. Factored out so that other Phase-1 fixpoint lemmas can
    reuse it as the "side" step in Hoare_BW_fix_logicv_conj'. *)
Lemma DFS_finish_f_preserves_inv :
  forall (W : V -> MonadErr.M St unit),
    (forall (s0 : St) (u : V),
       DFSFinishInv s0 ->
       ~ visited1 s0 u -> vvalid g u ->
       Hoare (fun st => st = s0) (W u)
         (fun _ st => DFSFinishFrame s0 tt st /\ visited1 st u)) ->
    forall (s0 : St) (u : V),
       DFSFinishInv s0 ->
       ~ visited1 s0 u -> vvalid g u ->
       Hoare (fun st => st = s0) (DFS_finish_f W u)
         (fun _ st => DFSFinishFrame s0 tt st /\ visited1 st u).
Proof.
  intros W IH s0 u Hinv0 Hnot_u Hvalid_u.
  unfold DFS_finish_f.
  apply Hoare_bind with
    (Q := fun (_:unit) st =>
      DFSFinishInv st /\
      visited1 s0 ⊆ visited1 st /\
      visited1 st u /\
      finish st u = finish s0 u /\
      (forall x, visited1 s0 x -> finish st x = finish s0 x) /\
      visited2 st = visited2 s0 /\
      scc_id st = scc_id s0 /\
      scc_next st = scc_next s0).
  - unfold Hoare. split.
    + intros s1 [] st Hs1 Hprog. rewrite Hs1 in Hprog.
      pose proof Hprog as Hprog_scoped.
      cbv beta iota delta [visit1 custom] in Hprog.
      destruct Hprog as [Hvis [Htimer [Hfin [Hv2 [Hsid Hnext]]]]].
      destruct Hinv0 as [[Hfc0 [Hzero0 [Hcard0 Htd0]]] Hscoped0].
      split.
      * unfold DFSFinishInv, DFSFinishInvCore.
        split.
        { split.
          - eapply FinishedCount_finish_cong; eauto.
          - split.
            + eapply (UnvisitedFinishZero_visit1 s0 st u); [exact Hvis|exact Hfin|exact Hzero0].
            + split.
              * eapply (cardV_visit1_nosteps s0 st u); [exact Hvis|exact Htimer|exact Hcard0].
              * unfold TimerDominates. intros x Hx.
                sets_unfold in Hvis.
                destruct (proj1 (Hvis x) Hx) as [Hx0 | Hu].
                -- rewrite Hfin, Htimer. apply Htd0. exact Hx0.
                -- subst x. rewrite Hfin, Htimer. rewrite Hzero0 by exact Hnot_u. lia. }
        { eapply DFSFinishScoped_visit1; eauto. }
      * repeat split.
        -- intros x Hx. sets_unfold in Hvis. apply Hvis. left. exact Hx.
        -- sets_unfold in Hvis. apply Hvis. right. reflexivity.
        -- rewrite Hfin. reflexivity.
        -- intros x _. rewrite Hfin. reflexivity.
        -- exact Hv2.
        -- exact Hsid.
        -- exact Hnext.
    + intros s1 Hs1 Herr. exfalso. exact Herr.
  - intros _. apply Hoare_normalize.
    intros st [Hinv_st [Hsub_s0 [Hvis_u [Hfin_u [Hfin_s0 [Hv2_s0 [Hsid_s0 Hnext_s0]]]]]]].
    eapply Hoare_cons_pre.
    2: {
    apply Hoare_repeat_break with
      (P := fun _ st' =>
        DFSFinishInv st' /\
        visited1 s0 ⊆ visited1 st' /\
        visited1 st' u /\
        finish st' u = finish s0 u /\
        (forall x, visited1 s0 x -> finish st' x = finish s0 x) /\
        visited2 st' = visited2 s0 /\
        scc_id st' = scc_id s0 /\
        scc_next st' = scc_next s0)
      (Q := fun r st' => DFSFinishFrame s0 r st' /\ visited1 st' u).
    intros e_set.
    apply Hoare_choice.
    + apply Hoare_bind with (Q := fun (e:E) st' =>
        DFSFinishInv st' /\
        visited1 s0 ⊆ visited1 st' /\
        visited1 st' u /\
        finish st' u = finish s0 u /\
        (forall x, visited1 s0 x -> finish st' x = finish s0 x) /\
        visited2 st' = visited2 s0 /\
        scc_id st' = scc_id s0 /\
        scc_next st' = scc_next s0).
      * apply Hoare_any.
      * intro e. apply Hoare_bind with (Q := fun (v:V) st' =>
          DFSFinishInv st' /\
          visited1 s0 ⊆ visited1 st' /\
          visited1 st' u /\
          finish st' u = finish s0 u /\
          (forall x, visited1 s0 x -> finish st' x = finish s0 x) /\
          visited2 st' = visited2 s0 /\
          scc_id st' = scc_id s0 /\
          scc_next st' = scc_next s0).
        -- apply Hoare_any.
        -- intro v.
           apply Hoare_assumeS_bind.
           apply Hoare_assumeS_bind.
           apply Hoare_assumeS_bind.
           apply Hoare_normalize.
           intros st1 [[[[Hinv1 [Hsub1 [Hvis_u1 [Hfin_u1 [Hfin_s01 [Hv2_s01 [Hsid_s01 Hnext_s01]]]]]]] _] Hnot_v] Hstep].
           apply Hoare_bind with (Q := fun (pre:St) st' => pre = st' /\ st' = st1).
           ++ apply Hoare_get.
           ++ intro pre. apply Hoare_normalize.
              intros st_pre [Hpre Hst_pre]. subst st_pre. subst pre.
              apply Hoare_bind with (Q := fun r st' => DFSFinishFrame st1 r st' /\ visited1 st' v).
              ** apply IH.
                 --- exact Hinv1.
                 --- exact Hnot_v.
                 --- eapply step_vvalid1; eauto.
              ** intros []. apply Hoare_normalize.
                 intros st' [[Hinv' [Hsub_st [Hfin_st [Hv2_st [Hsid_st Hnext_st]]]]] Hvis_v_st].
                 apply Hoare_assertS_bind.
                 --- intros st_assert Hst_assert. subst st_assert.
                     split; [ exact Hinv' | split; [ exact Hvis_v_st | exact Hsub_st ] ].
                 --- apply Hoare_ret. intros st'' Hst''. subst st''.
                     split; [exact Hinv'|].
                     repeat split.
                     +++ intros x Hx. apply Hsub_st. apply Hsub1. exact Hx.
                     +++ apply Hsub_st. exact Hvis_u1.
                     +++ transitivity (finish st1 u).
                         *** apply Hfin_st. exact Hvis_u1.
                         *** exact Hfin_u1.
                     +++ intros x Hx.
                         transitivity (finish st1 x).
                         *** apply Hfin_st. apply Hsub1. exact Hx.
                         *** apply Hfin_s01. exact Hx.
                     +++ rewrite Hv2_st. exact Hv2_s01.
                     +++ rewrite Hsid_st. exact Hsid_s01.
                     +++ rewrite Hnext_st. exact Hnext_s01.
    + apply Hoare_assumeS_bind.
      apply Hoare_normalize.
	      intros st1 [[Hinv1 [Hsub1 [Hvis_u1 [Hfin_u1 [Hfin_s01 [Hv2_s01 [Hsid_s01 Hnext_s01]]]]]]] _].
      apply Hoare_assertS_bind.
      * intros st' Hst'. subst st'. exact Hinv1.
      * apply Hoare_assertS_bind.
        -- intros st' Hst'. subst st'. exact (DFSFinishInv_finished_count _ Hinv1).
        -- apply Hoare_bind with (Q := fun (t:nat) st' => t = timer st' /\ st' = st1).
           ++ apply Hoare_get.
           ++ intro t. apply Hoare_normalize.
           intros st_get [Ht Hst_get]. subst st_get.
           apply Hoare_bind with
          (Q := fun (_:unit) st' =>
	             timer st' = S (timer st1) /\
	             finish st' u = S (timer st1) /\
	             (forall v, v <> u -> finish st' v = finish st1 v) /\
	             visited1 st' = visited1 st1 /\
	             visited2 st' = visited2 st1 /\
	             scc_id st' = scc_id st1 /\
	             scc_next st' = scc_next st1).
              ** apply (Hoare_cons_post
	                (fun st' => st' = st1)
                (set_finish u t)
                (fun (_:unit) st' =>
	                   timer st' = S (timer st1) /\
	                   finish st' u = S t /\
	                   (forall v, v <> u -> finish st' v = finish st1 v) /\
	                   visited1 st' = visited1 st1 /\
	                   visited2 st' = visited2 st1 /\
	                   scc_id st' = scc_id st1 /\
	                   scc_next st' = scc_next st1)).
                 --- intros _ st' [Htimer [Hfin_set [Hfin_other [Hv1_eq [Hv2_eq [Hsid_eq Hnext_eq]]]]]].
		                 split; [exact Htimer|].
		                 split.
		                 { rewrite <- Ht. exact Hfin_set. }
		                 repeat split; assumption.
                 --- apply Hoare_set_finish_raw.
              ** intros [].
              apply Hoare_ret. intros st' [Htimer [Hfin_set [Hfin_other [Hv1_eq [Hv2_eq [Hsid_eq Hnext_eq]]]]]].
	        assert (Hfin_u_zero : finish st1 u = 0).
        { rewrite Hfin_u1.
          pose proof (DFSFinishInv_unvisited_zero _ Hinv0) as Hzero0.
          apply Hzero0. exact Hnot_u. }
        split.
        { unfold DFSFinishFrame.
          split.
          { unfold DFSFinishInv, DFSFinishInvCore.
            split.
            { split.
              - eapply FinishedCount_set_finish_zero; eauto.
                exact (DFSFinishInv_finished_count _ Hinv1).
              - split.
                + eapply UnvisitedFinishZero_finish_update.
                  * exact Hv1_eq.
                  * exact Hfin_other.
                  * exact (DFSFinishInv_unvisited_zero _ Hinv1).
                  * exact Hvis_u1.
                + split.
                  * rewrite Hv1_eq.
                    pose proof (DFSFinishInv_strict_unfinished st1 u Hinv1 Hvalid_u Hvis_u1 Hfin_u_zero).
                    lia.
                  * unfold TimerDominates. intros x Hvis_x.
                    rewrite Hv1_eq in Hvis_x.
                    destruct (classic (x = u)) as [-> | Hne].
                    -- rewrite Hfin_set. rewrite Htimer. lia.
                    -- rewrite Hfin_other by exact Hne.
                       pose proof (DFSFinishInv_timer_dominates _ Hinv1 x Hvis_x).
                       rewrite Htimer. lia. }
            { destruct (DFSFinishInv_scoped _ Hinv1) as [Hvis_invalid Hfin_invalid].
              split.
              - intros x Hinvalid Hvisited.
                rewrite Hv1_eq in Hvisited.
                exact (Hvis_invalid x Hinvalid Hvisited).
              - intros x Hinvalid.
                rewrite Hfin_other.
                + exact (Hfin_invalid x Hinvalid).
                + intro Heq. subst x. contradiction. } }
          repeat split.
          { intros x Hx. rewrite Hv1_eq. apply Hsub1. exact Hx. }
          { intros x Hx.
            rewrite Hfin_other.
            - apply Hfin_s01. exact Hx.
            - intro Heq. subst x. exact (Hnot_u Hx). }
          { rewrite Hv2_eq. exact Hv2_s01. }
          { rewrite Hsid_eq. exact Hsid_s01. }
          { rewrite Hnext_eq. exact Hnext_s01. } }
        { rewrite Hv1_eq. exact Hvis_u1. }
    }
    intros st' Hst'. subst st'.
    split; [exact Hinv_st|].
    repeat split; assumption.
Qed.

(** [DFS_finish_fixpoint_ind_strong]: a tailored fixpoint induction principle for
    Phase-1 property lemmas about [DFS_finish]. The step gets TWO induction
    hypotheses for the recursive body W: one for the (entry-state-indexed)
    property Q, and one for the k-parameterised excess (cardV - timer).
    The excess IH is what lets the step discharge the assertS timer-bound
    inside DFS_finish_f's break branch, while Q is free to mention the entry
    state s0 (so subset-style invariants carry). *)
Lemma DFS_finish_fixpoint_ind_strong :
  forall (Q : V -> St -> unit -> St -> Prop),
    (forall (W : V -> MonadErr.M St unit),
       (forall (s0 : St) (u : V),
          DFSFinishInv s0 ->
          ~ visited1 s0 u ->
          vvalid g u ->
          Hoare (fun st => st = s0) (W u)
            (fun _ s' => DFSFinishFrame s0 tt s' /\ Q u s0 tt s')) ->
       forall (s0 : St) (u : V),
          DFSFinishInv s0 ->
          ~ visited1 s0 u ->
          vvalid g u ->
          Hoare (fun st => st = s0) (DFS_finish_f W u)
            (fun _ s' => DFSFinishFrame s0 tt s' /\ Q u s0 tt s')) ->
    forall (s0 : St) (u : V),
       DFSFinishInv s0 ->
       ~ visited1 s0 u ->
       vvalid g u ->
       Hoare (fun st => st = s0) (DFS_finish u)
         (fun _ s' => DFSFinishFrame s0 tt s' /\ Q u s0 tt s').
Proof.
  intros Q Hstep s0 u Hentry Hnot_u Hvalid_u.
  unfold DFS_finish.
  assert (Hiter : forall n s0 u,
                    DFSFinishInv s0 ->
                    ~ visited1 s0 u ->
                    vvalid g u ->
                    Hoare (fun st => st = s0) (Nat.iter n DFS_finish_f (fun _ => bot) u)
                          (fun _ s' => DFSFinishFrame s0 tt s' /\ Q u s0 tt s')).
  { intro n. induction n as [| n IH]; intros s0' u' Hinv' Hnot' Hvalid'.
    - unfold Hoare. split; intros; simpl in *.
      + exfalso. exact H0.
      + exfalso. exact H0.
    - simpl.
      apply (Hstep (Nat.iter n DFS_finish_f (fun _ => bot)) IH s0' u' Hinv' Hnot' Hvalid'). }
  unfold Hoare.
  unfold DFS_finish, BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  split.
  - intros b s1 s2 Hs1 Hnrm. destruct Hnrm as [n Hnrm].
    destruct (Hiter n s0 u Hentry Hnot_u Hvalid_u) as [Hn _]. eapply Hn; eauto.
  - intros s1 Hs1 Herr. destruct Herr as [n Herr].
    destruct (Hiter n s0 u Hentry Hnot_u Hvalid_u) as [_ He]. eapply He; eauto.
Qed.

(** Postcondition weakening: Hoare P f Q and Q -> R gives Hoare P f R. *)
Lemma Hoare_imp_post {Σ A: Type} (P: Σ -> Prop) (f: program Σ A) (Q R: A -> Σ -> Prop) :
  Hoare P f Q -> (forall a s, Q a s -> R a s) -> Hoare P f R.
Proof.
  unfold Hoare; firstorder.
Qed.

Lemma DFS_finish_preserves_inv : forall s0 u,
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' => DFSFinishInv s').
Proof.
  intros s0 u Hinv Hnot Hvalid.
  eapply Hoare_imp_post.
  - eapply DFS_finish_fixpoint_ind_strong with
    (Q := fun root _ _ st => visited1 st root);
      try exact Hinv; try exact Hnot; try exact Hvalid.
    intros W IH s1 v Hinv1 Hnot1 Hvalid1.
    apply (DFS_finish_f_preserves_inv W IH s1 v Hinv1 Hnot1 Hvalid1).
  - intros _ s' [Hframe _]. exact (DFSFinishFrame_inv _ _ _ Hframe).
Qed.

Lemma DFS_finish_phase1_light : forall s0 u,
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' =>
      DFSFinishInv s' /\ visited1 s' u /\ visited1 s0 ⊆ visited1 s').
Proof.
  intros s0 u Hinv Hnot Hvalid.
  eapply Hoare_imp_post.
  - eapply DFS_finish_fixpoint_ind_strong with
      (Q := fun root _ _ st => visited1 st root);
      try exact Hinv; try exact Hnot; try exact Hvalid.
    intros W IH s1 v Hinv1 Hnot1 Hvalid1.
    apply (DFS_finish_f_preserves_inv W IH s1 v Hinv1 Hnot1 Hvalid1).
  - intros _ s' [Hframe Hvis].
    destruct Hframe as [Hinv' [Hsub _]].
    split; [ exact Hinv' | split; [ exact Hvis | exact Hsub ] ].
Qed.

Lemma DFS_finish_phase1_frame_light : forall s0 u,
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' => DFSFinishFrame s0 tt s' /\ visited1 s' u).
Proof.
  intros s0 u Hinv Hnot Hvalid.
  eapply DFS_finish_fixpoint_ind_strong with
    (Q := fun root _ _ st => visited1 st root);
    try exact Hinv; try exact Hnot; try exact Hvalid.
  intros W IH s1 v Hinv1 Hnot1 Hvalid1.
  apply (DFS_finish_f_preserves_inv W IH s1 v Hinv1 Hnot1 Hvalid1).
Qed.

(** visit1 preserves finish. Trivial but needed for set_finish reasoning.
    Proved property: finish s' = finish s0 *)
Lemma Hoare_visit1_preserve_finish : forall s0 u,
  Hoare (fun st => st = s0) (visit1 u) (fun _ s' => finish s' = finish s0).
Proof.
  intros s0 u.
  unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [visit1 custom] in Hprog.
    destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
    exact Hfin.
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

(** TimerDominates implies TimerDominates_except. Trivial weakening. *)
Lemma TDom_implies_except : forall s u,
  TimerDominates s -> TimerDominates_except s u.
Proof.
  unfold TimerDominates, TimerDominates_except; intros s u Htd v Hvis Hv_ne; apply Htd; assumption.
Qed.

(** [DFS_finish_preserves_TimerDominates]
    DFS_finish u preserves the TimerDominates invariant (every visited1
    vertex has finish < timer), provided u was not already visited1.
    Proved property: TimerDominates s' *)
Lemma DFS_finish_preserves_TimerDominates : forall s0 u,
  TimerDominates s0 ->
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' => TimerDominates s').
Proof.
  intros s0 u _ Hinv Hnot Hvalid.
  eapply Hoare_imp_post.
  - apply (DFS_finish_preserves_inv s0 u Hinv Hnot Hvalid).
  - intros r st Hst. exact (DFSFinishInv_timer_dominates st Hst).
Qed.

Definition Q_strict_new_finish (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  timer s0' <= timer s' /\
  (forall v, visited1 s' v -> ~ visited1 s0' v -> timer s0' < finish s' v).

Lemma DFS_finish_strict_new_finish_full : forall s0 u,
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' => DFSFinishFrame s0 tt s' /\ Q_strict_new_finish u s0 tt s').
Proof.
  intros s0 u Hinv0 Hnot_u Hvalid_u.
  eapply Hoare_imp_post.
  - eapply DFS_finish_fixpoint_ind_strong with
    (Q := fun root s_base _ st =>
            visited1 st root /\ Q_strict_new_finish root s_base tt st);
      try exact Hinv0; try exact Hnot_u; try exact Hvalid_u.
  intros W IH s_base root Hinv_base Hnot_root Hvalid_root.
  unfold DFS_finish_f.
  apply Hoare_bind with
    (Q := fun (_:unit) st =>
      DFSFinishInv st /\
      visited1 s_base ⊆ visited1 st /\
      visited1 st root /\
      finish st root = finish s_base root /\
      (forall x, visited1 s_base x -> finish st x = finish s_base x) /\
      visited2 st = visited2 s_base /\
      scc_id st = scc_id s_base /\
      scc_next st = scc_next s_base /\
      timer s_base <= timer st /\
      (forall x, visited1 st x -> ~ visited1 s_base x -> x <> root ->
                 timer s_base < finish st x)).
  * unfold Hoare. split.
	    + intros s1 [] st Hs1 Hprog. rewrite Hs1 in Hprog.
	      pose proof Hprog as Hprog_scoped.
	      cbv beta iota delta [visit1 custom] in Hprog.
	      destruct Hprog as [Hvis [Htimer [Hfin [Hv2 [Hsid Hnext]]]]].
		      destruct Hinv_base as [[Hfc0 [Hzero0 [Hcard0 Htd0]]] Hscoped0].
		      split.
		      { unfold DFSFinishInv, DFSFinishInvCore.
		        split.
		        { split.
		          - unfold FinishedCount in *. rewrite Htimer, Hfin. exact Hfc0.
		          - split.
		            + eapply (UnvisitedFinishZero_visit1 s_base st root); [exact Hvis|exact Hfin|exact Hzero0].
		            + split.
		              * eapply (cardV_visit1_nosteps s_base st root); [exact Hvis|exact Htimer|exact Hcard0].
		              * unfold TimerDominates. intros x Hx.
		                sets_unfold in Hvis.
		                destruct (proj1 (Hvis x) Hx) as [Hx0 | Hroot].
			                -- rewrite Hfin, Htimer. apply Htd0. exact Hx0.
			                -- subst x. rewrite Hfin, Htimer. rewrite Hzero0 by exact Hnot_root. lia. }
		        { eapply DFSFinishScoped_visit1; eauto. } }
	      { repeat split.
		        + intros x Hx. sets_unfold in Hvis. apply Hvis. left. exact Hx.
		        + sets_unfold in Hvis. apply Hvis. right. reflexivity.
		        + rewrite Hfin. reflexivity.
	        + intros x _. rewrite Hfin. reflexivity.
	        + exact Hv2.
	        + exact Hsid.
	        + exact Hnext.
	        + rewrite Htimer. lia.
	        + intros x Hx Hnew Hne.
	           sets_unfold in Hvis.
	           destruct (proj1 (Hvis x) Hx) as [Hx0 | Hroot].
	           * exfalso. exact (Hnew Hx0).
	           * subst x. exfalso. exact (Hne eq_refl). }
    + intros s1 Hs1 Herr. exfalso. exact Herr.
  * intros _. apply Hoare_normalize.
    intros st [Hinv_st [Hsub_st [Hvis_root [Hfin_root [Hfin_base
      [Hv2_base [Hsid_base [Hnext_base [Htimer_base Hstrict_st]]]]]]]]].
    eapply Hoare_cons_pre.
    2: {
    apply Hoare_repeat_break with
      (P := fun _ st' =>
        DFSFinishInv st' /\
        visited1 s_base ⊆ visited1 st' /\
        visited1 st' root /\
        finish st' root = finish s_base root /\
        (forall x, visited1 s_base x -> finish st' x = finish s_base x) /\
        visited2 st' = visited2 s_base /\
        scc_id st' = scc_id s_base /\
        scc_next st' = scc_next s_base /\
        timer s_base <= timer st' /\
        (forall x, visited1 st' x -> ~ visited1 s_base x -> x <> root ->
                   timer s_base < finish st' x))
      (Q := fun (_:unit) st' =>
        DFSFinishFrame s_base tt st' /\
        visited1 st' root /\ Q_strict_new_finish root s_base tt st').
    intros e_set.
    apply Hoare_choice.
    + apply Hoare_bind with (Q := fun (e:E) st' =>
        DFSFinishInv st' /\
        visited1 s_base ⊆ visited1 st' /\
        visited1 st' root /\
        finish st' root = finish s_base root /\
        (forall x, visited1 s_base x -> finish st' x = finish s_base x) /\
        visited2 st' = visited2 s_base /\
        scc_id st' = scc_id s_base /\
        scc_next st' = scc_next s_base /\
        timer s_base <= timer st' /\
        (forall x, visited1 st' x -> ~ visited1 s_base x -> x <> root ->
                   timer s_base < finish st' x)).
      * apply Hoare_any.
      * intro e. apply Hoare_bind with (Q := fun (v:V) st' =>
          DFSFinishInv st' /\
          visited1 s_base ⊆ visited1 st' /\
          visited1 st' root /\
          finish st' root = finish s_base root /\
          (forall x, visited1 s_base x -> finish st' x = finish s_base x) /\
          visited2 st' = visited2 s_base /\
          scc_id st' = scc_id s_base /\
          scc_next st' = scc_next s_base /\
          timer s_base <= timer st' /\
          (forall x, visited1 st' x -> ~ visited1 s_base x -> x <> root ->
                     timer s_base < finish st' x)).
        -- apply Hoare_any.
        -- intro v.
           apply Hoare_assumeS_bind.
           apply Hoare_assumeS_bind.
           apply Hoare_assumeS_bind.
           apply Hoare_normalize.
           intros st1 [[[[Hinv1 [Hsub1 [Hvis_root1 [Hfin_root1 [Hfin_base1
             [Hv2_base1 [Hsid_base1 [Hnext_base1 [Htimer_base1 Hstrict1]]]]]]]]] _] Hnot_v] Hstep].
           apply Hoare_bind with (Q := fun (pre:St) st' => pre = st' /\ st' = st1).
           ++ apply Hoare_get.
           ++ intro pre. apply Hoare_normalize.
              intros st_pre [Hpre Hst_pre]. subst st_pre. subst pre.
              apply Hoare_bind with
                (Q := fun (_:unit) s_child =>
                  DFSFinishFrame st1 tt s_child /\
                  visited1 s_child v /\ Q_strict_new_finish v st1 tt s_child).
              ** apply IH.
                 --- exact Hinv1.
                 --- exact Hnot_v.
                 --- eapply step_vvalid1; eauto.
              ** intros []. apply Hoare_normalize.
              intros s_child [Hframe_child [Hvis_child_v [Htimer_child Hstrict_child]]].
              destruct Hframe_child as [Hinv_child [Hsub_child [Hfin_child_old
                [Hv2_child [Hsid_child Hnext_child]]]]].
              apply Hoare_assertS_bind.
              *** intros st_assert Hst_assert. subst st_assert.
                  split; [ exact Hinv_child | split; [ exact Hvis_child_v | exact Hsub_child ] ].
              *** apply Hoare_ret. intros st' Hst'. subst st'.
                  split; [exact Hinv_child|].
                  repeat split.
                  ---- intros x Hx. apply Hsub_child. apply Hsub1. exact Hx.
                  ---- apply Hsub_child. exact Hvis_root1.
                  ---- transitivity (finish st1 root).
                       +++ apply Hfin_child_old. exact Hvis_root1.
                       +++ exact Hfin_root1.
                  ---- intros x Hx.
                       transitivity (finish st1 x).
                       +++ apply Hfin_child_old. apply Hsub1. exact Hx.
                       +++ apply Hfin_base1. exact Hx.
                  ---- rewrite Hv2_child. exact Hv2_base1.
                  ---- rewrite Hsid_child. exact Hsid_base1.
                  ---- rewrite Hnext_child. exact Hnext_base1.
                  ---- lia.
                  ---- intros x Hx Hnew_base Hne_root.
                       destruct (classic (visited1 st1 x)) as [Hx_st1 | Hx_new_st1].
                       +++ rewrite (Hfin_child_old x Hx_st1).
                           apply Hstrict1; assumption.
                       +++ pose proof (Hstrict_child x Hx Hx_new_st1) as Hchild_x.
                           lia.
    + apply Hoare_assumeS_bind.
      apply Hoare_normalize.
      intros st1 [[Hinv1 [Hsub1 [Hvis_root1 [Hfin_root1 [Hfin_base1
        [Hv2_base1 [Hsid_base1 [Hnext_base1 [Htimer_base1 Hstrict1]]]]]]]]] _].
      apply Hoare_assertS_bind.
      * intros st' Hst'. subst st'. exact Hinv1.
      * apply Hoare_assertS_bind.
        -- intros st' Hst'. subst st'. exact (DFSFinishInv_finished_count _ Hinv1).
        -- apply Hoare_bind with (Q := fun (t:nat) st' => t = timer st' /\ st' = st1).
           ++ apply Hoare_get.
           ++ intro t. apply Hoare_normalize.
           intros st_get [Ht Hst_get]. subst st_get.
           apply Hoare_bind with
          (Q := fun (_:unit) st' =>
             timer st' = S (timer st1) /\
             finish st' root = S (timer st1) /\
             (forall v, v <> root -> finish st' v = finish st1 v) /\
             visited1 st' = visited1 st1 /\
             visited2 st' = visited2 st1 /\
             scc_id st' = scc_id st1 /\
             scc_next st' = scc_next st1).
              ** apply (Hoare_cons_post
                (fun st' => st' = st1)
                (set_finish root t)
                (fun (_:unit) st' =>
                   timer st' = S (timer st1) /\
                   finish st' root = S t /\
                   (forall v, v <> root -> finish st' v = finish st1 v) /\
                   visited1 st' = visited1 st1 /\
                   visited2 st' = visited2 st1 /\
                   scc_id st' = scc_id st1 /\
                   scc_next st' = scc_next st1)).
                 --- intros _ st' [Htimer [Hfin_set [Hfin_other [Hv1_eq [Hv2_eq [Hsid_eq Hnext_eq]]]]]].
	                 split; [exact Htimer|].
	                 split.
	                 { rewrite <- Ht. exact Hfin_set. }
	                 repeat split; assumption.
                 --- apply Hoare_set_finish_raw.
              ** intros [].
              apply Hoare_ret. intros st' [Htimer [Hfin_set [Hfin_other [Hv1_eq [Hv2_eq [Hsid_eq Hnext_eq]]]]]].
              assert (Hfin_root_zero : finish st1 root = 0).
              { rewrite Hfin_root1.
                pose proof (DFSFinishInv_unvisited_zero _ Hinv_base) as Hzero_base.
                apply Hzero_base. exact Hnot_root. }
	              unfold DFSFinishFrame, Q_strict_new_finish.
	              split.
	              { split.
	                { unfold DFSFinishInv, DFSFinishInvCore.
	                  split.
	                  { split.
	                    - eapply FinishedCount_set_finish_zero; eauto.
	                      exact (DFSFinishInv_finished_count _ Hinv1).
	                    - split.
	                      + eapply UnvisitedFinishZero_finish_update.
	                        * exact Hv1_eq.
	                        * exact Hfin_other.
	                        * exact (DFSFinishInv_unvisited_zero _ Hinv1).
	                        * exact Hvis_root1.
	                      + split.
	                        * rewrite Hv1_eq.
	                          pose proof (DFSFinishInv_strict_unfinished st1 root Hinv1 Hvalid_root Hvis_root1 Hfin_root_zero).
	                          lia.
	                        * unfold TimerDominates. intros x Hvis_x.
	                          rewrite Hv1_eq in Hvis_x.
	                          destruct (classic (x = root)) as [-> | Hne].
	                          -- rewrite Hfin_set. rewrite Htimer. lia.
	                          -- rewrite Hfin_other by exact Hne.
	                             pose proof (DFSFinishInv_timer_dominates _ Hinv1 x Hvis_x).
	                             rewrite Htimer. lia. }
	                  { destruct (DFSFinishInv_scoped _ Hinv1) as [Hvis_invalid Hfin_invalid].
	                    split.
	                    - intros x Hinvalid Hvisited.
	                      rewrite Hv1_eq in Hvisited.
	                      exact (Hvis_invalid x Hinvalid Hvisited).
	                    - intros x Hinvalid.
	                      rewrite Hfin_other.
	                      + exact (Hfin_invalid x Hinvalid).
	                      + intro Heq. subst x. contradiction. } }
	                repeat split.
	                - intros x Hx. rewrite Hv1_eq. apply Hsub1. exact Hx.
	                - intros x Hx.
	                  rewrite Hfin_other by (intro Heq; subst x; exact (Hnot_root Hx)).
	                  apply Hfin_base1. exact Hx.
	                - rewrite Hv2_eq. exact Hv2_base1.
	                - rewrite Hsid_eq. exact Hsid_base1.
	                - rewrite Hnext_eq. exact Hnext_base1. }
	              { split.
	                - rewrite Hv1_eq. exact Hvis_root1.
	                - split.
	                  + rewrite Htimer. lia.
	                  + intros x Hx Hnew_base.
	                    rewrite Hv1_eq in Hx.
	                    destruct (classic (x = root)) as [Heq | Hne].
	                    { subst x. rewrite Hfin_set. lia. }
	                    { rewrite Hfin_other by exact Hne.
	                      apply Hstrict1; assumption. } }
    }
    intros st' Hst'. subst st'.
    split; [exact Hinv_st|].
    repeat split; try assumption.
  - intros _ st' [Hframe [_ Hstrict]]. exact (conj Hframe Hstrict).
Qed.

Lemma DFS_finish_strict_new_finish : forall s0 u,
  ReachRevClosed s0 ->
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' =>
      forall v, visited1 s' v -> ~ visited1 s0 v -> timer s0 < finish s' v).
Proof.
  intros s0 u _ Hinv Hnot Hvalid.
  eapply Hoare_imp_post.
  - apply (DFS_finish_strict_new_finish_full s0 u Hinv Hnot Hvalid).
  - intros _ s' [_ [_ Hstrict]]. exact Hstrict.
Qed.

Definition R_non_closed (u : V) (st : St) : Prop :=
  forall v, visited1 st v ->
    ~ (forall w, step_rev v w -> visited1 st w) ->
    reachable_rev v u.

Definition ForwardReachClosed (s: St) : Prop :=
  forall v w, visited2 s v -> reachable g v w -> visited2 s w.

(** reachable_rev is transitive. *)
Lemma reachable_rev_trans : forall x y z,
  reachable_rev x y -> reachable_rev y z -> reachable_rev x z.
Proof.
  intros x y z Hxy Hyz.
  unfold reachable_rev in *.
  eapply reachable_trans; [exact Hyz | exact Hxy].
Qed.

(** Combining two Hoare triples for the same program into a conjunction. *)
Lemma Hoare_conj (Σ A: Type) (P: Σ -> Prop) (f: program Σ A) (Q1 Q2: A -> Σ -> Prop) :
  Hoare P f Q1 -> Hoare P f Q2 -> Hoare P f (fun a s => Q1 a s /\ Q2 a s).
Proof.
  intros H1 H2.
  unfold Hoare in *. destruct H1 as [H1n H1e], H2 as [H2n H2e]. split.
  - intros a s1 s2 Hpre Hnrm. split.
    + apply (H1n a s1 s2 Hpre Hnrm).
    + apply (H2n a s1 s2 Hpre Hnrm).
  - intros s1 Hpre Herr. exact (H1e s1 Hpre Herr).
Qed.

(** [finished_rev_to_root]
    Under ReachRevClosed s0' and visited1 s0' ⊆ visited1 st, if a is a
    non-root new vertex that has been finished (its subtree returned),
    b is not yet visited, and a can reachable_rev b, then the path
    a →* b must pass through the current DFS root u'.
    Uses ReachRevClosed s0' (not st) so it works at intermediate
    loop states where st may not be closed under reachable_rev. *)
Lemma finished_rev_to_root :
  forall st s0' u' a b,
  ReachRevClosed s0' ->
  visited1 s0' ⊆ visited1 st ->
  visited1 st a -> ~ visited1 s0' a -> a <> u' ->
  (forall v w, visited1 st v -> ~ visited1 s0' v -> v <> u' -> step_rev v w -> visited1 st w) ->
  ~ visited1 st b ->
  reachable_rev a b ->
  reachable_rev a u'.
Proof.
  intros st s0' u' a b Hclosed Hsub Hvis_a Hnew_a Hne_a Hstep_vis Hunvis_b Hreach.
  unfold reachable_rev in Hreach.
  revert Hvis_a Hnew_a Hne_a Hunvis_b.
  refine (SCC.reachable_rev_ind _
            (fun a b => visited1 st a -> ~ visited1 s0' a -> a <> u' ->
                        ~ visited1 st b -> reachable_rev a u')
            _ _ _ _ Hreach).
  - intros u0 Hvis_u0 Hnew_u0 Hne_u0 Hunvis_u0.
    exfalso. exact (Hunvis_u0 Hvis_u0).
  - intros a0 v w Hstep Hreach' IH Hvis_a0 Hnew_a0 Hne_a0 Hunvis_w.
    pose proof (Hstep_vis a0 v Hvis_a0 Hnew_a0 Hne_a0 Hstep) as Hvis_v.
    destruct (classic (visited1 s0' v)) as [Hv_s0 | Hv_new].
    + exfalso. apply Hunvis_w. apply Hsub, (Hclosed v w Hv_s0 Hreach').
    + destruct (classic (v = u')) as [Hv_u' | Hv_ne].
      * subst v. apply (SCC.rr_step g a0 u' u' Hstep (SCC.rr_refl g u')).
      * apply (SCC.rr_step g a0 v u' Hstep).
        exact (IH Hvis_v Hv_new Hv_ne Hunvis_w).
Qed.

(** [visited_boundary_not_closed]
    Purely set-theoretic: if [b] ∈ visited can reachable_rev some
    [c] ∉ visited, then the path [b →* c] must cross the boundary
    of [visited] at a vertex [v] ∈ visited that has a step_rev
    neighbour outside [visited] (hence [v] is not step_rev-closed).
    Moreover [reachable_rev b v]. *)
Lemma visited_boundary_not_closed :
  forall (visited : V -> Prop) (b c : V),
  visited b ->
  ~ visited c ->
  reachable_rev b c ->
  exists v, visited v /\ ~ (forall w, step_rev v w -> visited w) /\ reachable_rev b v.
Proof.
  intros visited b c Hvis_b Hunvis_c Hreach.
  unfold reachable_rev in Hreach.
  revert Hvis_b Hunvis_c.
  refine (SCC.reachable_rev_ind _
            (fun b c => visited b -> ~ visited c ->
               exists v, visited v /\ ~ (forall w, step_rev v w -> visited w)
                         /\ reachable_rev b v)
            _ _ _ _ Hreach).
  - intros u0 Hvis_u0 Hunvis_u0. exfalso. exact (Hunvis_u0 Hvis_u0).
  - intros b0 v w Hstep Hreach' IH Hvis_b0 Hunvis_w.
    destruct (classic (visited v)) as [Hvis_v | Hunvis_v].
    + destruct (IH Hvis_v Hunvis_w) as [x [Hvis_x [Hnot_closed Hreach_x]]].
      exists x. split; [exact Hvis_x | split; [exact Hnot_closed |]].
      apply (SCC.rr_step g b0 v x Hstep Hreach_x).
    + exists b0. split; [exact Hvis_b0 | split].
      * intro Hclosed_b. apply Hunvis_v, Hclosed_b. exact Hstep.
      * apply SCC.rr_refl.
Qed.

Definition ReachRevClosedEx (s: St) (x: V) : Prop :=
  forall v w, visited1 s v -> v <> x -> reachable_rev v w -> visited1 s w.

(** Phase 1 postcondition: if a can reverse-reach b but not vice versa,
    then a's SCC contains a vertex c whose finish exceeds b's finish.
    Encodes the condensation-DAG edge direction: larger finish values
    lie further "upstream" in the forward graph. *)
Definition Phase1_Order (s : St) : Prop :=
  forall a b, reachable_rev a b -> ~ reachable_rev b a ->
    exists c, mutually_reachable a c /\ finish s b < finish s c.

Lemma mutually_reachable_self_from_rev : forall a,
  mutually_reachable a a.
Proof.
  intro a.
  unfold mutually_reachable.
  split; unfold reachable; reflexivity.
Qed.

Lemma mutually_reachable_from_rev : forall a c,
  reachable_rev a c -> reachable_rev c a -> mutually_reachable a c.
Proof.
  intros a c Hac Hca.
  unfold mutually_reachable, reachable_rev, SCC.reachable_rev in *.
  split; assumption.
Qed.

Lemma R_non_closed_from_ReachRevClosed : forall s u,
  ReachRevClosed s -> R_non_closed u s.
Proof.
  intros s u Hclosed v Hvis Hnot_closed.
  exfalso. apply Hnot_closed.
  intros w Hstep.
  apply Hclosed with (v := v).
  - exact Hvis.
  - apply (SCC.rr_step g v w w Hstep (SCC.rr_refl g w)).
Qed.

Lemma mutually_reachable_old_closed : forall s a b,
  ReachRevClosed s ->
  visited1 s a ->
  reachable_rev a b ->
  ~ reachable_rev b a ->
  ~ visited1 s b -> False.
Proof.
  intros s a b Hclosed Hvis_a Hreach Hnot_back Hnot_b.
  apply Hnot_b.
  exact (Hclosed a b Hvis_a Hreach).
Qed.
    
(* ================================================================= *)
(* 3. Outer Phase 1 — kosaraju_finish                                 *)
(* ================================================================= *)

(** [kosaraju_finish_visited_all_aux]
    Helper: if the remaining computation W visits all vertices, then one
    iteration of kosaraju_finish_f (pick unvisited, DFS_finish, recurse) also
    visits all vertices.
    Proved property: forall v, visited1 s' v *)
Lemma kosaraju_finish_visited_all_aux : forall W,
  (forall s0, DFSFinishInv s0 ->
     Hoare (fun st => st = s0) (W tt)
       (fun _ s' => (forall v, visited1 s' v) /\ DFSFinishInv s')) ->
  forall s0, DFSFinishInv s0 ->
  Hoare (fun st => st = s0) (kosaraju_finish_f W tt)
    (fun _ s' => (forall v, visited1 s' v) /\ DFSFinishInv s').
Proof.
  intros W IH s0 Hinv_s0.
  unfold kosaraju_finish_f.
  apply Hoare_choice.
  { apply Hoare_bind with
      (Q := fun (u:V) (s':St) => s' = s0 /\ vvalid g u /\ ~ visited1 s' u).
    { unfold Hoare. split.
      - intros s1 a s2 Hs1 Hprog.
        rewrite Hs1 in *.
        cbv beta iota delta [pick_unvisited1 MonadErr.nrm_nrm get] in Hprog.
        destruct Hprog as [[Hvv Hnot_vis] Hsame].
        rewrite Hsame in Hnot_vis.
        split; [symmetry; exact Hsame | split; [exact Hvv | exact Hnot_vis]].
      - intros s1 Hs1 Herr. exfalso.
        cbv beta iota delta [pick_unvisited1 MonadErr.nrm_err get] in Herr.
        sets_unfold in Herr. firstorder. }
    { intro u. apply Hoare_normalize.
      intros s1 [Hs1_eq [Hvv Hunvis]]. subst s1.
      apply Hoare_bind with (Q := fun (_:unit) (s':St) => DFSFinishInv s').
      - apply (DFS_finish_preserves_inv s0 u Hinv_s0 Hunvis Hvv).
      - intro junk. apply Hoare_normalize. intros s2 Hinv_s2.
        apply (IH s2 Hinv_s2). } }
  { apply Hoare_normal_assume_bind; intros Hall.
    apply Hoare_ret.
    intros s1 Hs1. subst s1. split; [exact Hall | exact Hinv_s0]. }
Qed.

(** [kosaraju_finish_visited_all]
    After the full kosaraju_finish, all vertices are visited1.
    Proved property: forall v, visited1 s' v *)
Lemma kosaraju_finish_visited_all : forall s0,
  DFSFinishInv s0 ->
  Hoare (fun st => st = s0) kosaraju_finish (fun _ s' => forall v, visited1 s' v).
Proof.
  intros s0 Hinv_s0.
  apply Hoare_imp_post with
    (Q := fun (_:unit) (s':St) =>
           (forall v, visited1 s' v) /\ DFSFinishInv s').
  - unfold kosaraju_finish.
    apply Hoare_normal_LFix_closed with
      (R := DFSFinishInv)
      (Q := fun (_:unit) (s0':St) (_:unit) (s':St) =>
             (forall v, visited1 s' v) /\ DFSFinishInv s').
    + intros W IH s0' u Hinv_s0'.
      apply kosaraju_finish_visited_all_aux;
        [ intro s0''; exact (IH s0'' tt) | exact Hinv_s0' ].
    + exact Hinv_s0.
  - intros _ s' [Hall _] v. apply Hall.
Qed.

(* ================================================================= *)
(* 3a. Inner Phase 1 — Phase1_Order for a single DFS tree             *)
(* ================================================================= *)

Definition Q_phase1 (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited1 s0' ⊆ visited1 s' /\
  visited1 s' u' /\
  (forall v w, visited1 s' v -> ~visited1 s0' v ->
               step_rev v w -> visited1 s' w) /\
  (forall v, visited1 s' v -> ~visited1 s0' v -> reachable_rev u' v) /\
  finish s' u' <= timer s' /\
  (forall z, visited1 s0' z -> z <> u' -> finish s' z = finish s0' z) /\
  timer s0' <= timer s' /\
  (forall v, v <> u' -> visited1 s' v ->
             visited1 s0' v \/ finish s' v < finish s' u') /\
  (forall v, visited1 s' v -> ~visited1 s0' v -> timer s0' <= finish s' v) /\
  (R_non_closed u' s0' -> R_non_closed u' s') /\
  (R_non_closed u' s0' ->
   forall a b,
     visited1 s' a -> ~visited1 s0' a ->
     visited1 s' b -> ~visited1 s0' b ->
     reachable_rev a b -> ~reachable_rev b a ->
     exists c, mutually_reachable a c /\ finish s' b < finish s' c).

Lemma DFS_finish_phase1_core : forall s0 u,
  ReachRevClosed s0 ->
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' =>
      DFSFinishFrame s0 tt s' /\
      Q_phase1 u s0 tt s' /\
      (forall v, visited1 s' v -> ~ visited1 s0 v -> timer s0 < finish s' v)).
Proof.
  intros s0 u Hclosed0 Hinv0 Hnot_u Hvalid_u.
  eapply DFS_finish_fixpoint_ind_strong with
    (Q := fun u' s0' _ s' =>
      Q_phase1 u' s0' tt s' /\
      (forall v, visited1 s' v -> ~ visited1 s0' v -> timer s0' < finish s' v));
    try exact Hinv0; try exact Hnot_u; try exact Hvalid_u.
  intros W IH s0' u' Hinv_s0 Hnot_u' Hvalid_u'.
  unfold DFS_finish_f, Q_phase1.
  set (P_loop := fun (e_set : E -> Prop) (st : St) =>
    DFSFinishInv st /\
    visited1 s0' ⊆ visited1 st /\
    visited1 st u' /\
    finish st u' = finish s0' u' /\
    (forall v w, visited1 st v -> ~ visited1 s0' v -> v <> u' ->
                 step_rev v w -> visited1 st w) /\
    (forall v, visited1 st v -> ~ visited1 s0' v -> reachable_rev u' v) /\
    (forall z, visited1 s0' z -> finish st z = finish s0' z) /\
    visited2 st = visited2 s0' /\
    scc_id st = scc_id s0' /\
    scc_next st = scc_next s0' /\
    timer s0' <= timer st /\
    (forall v, v <> u' -> visited1 st v ->
               visited1 s0' v \/ finish st v <= timer st) /\
    (forall v, visited1 st v -> ~ visited1 s0' v -> v <> u' ->
               timer s0' <= finish st v) /\
    (forall v, visited1 st v -> ~ visited1 s0' v -> v <> u' ->
               timer s0' < finish st v) /\
    (forall e v, e ∈ e_set -> step_aux g e v u' -> visited1 st v) /\
    (R_non_closed u' s0' -> R_non_closed u' st) /\
    (R_non_closed u' s0' ->
     forall a b,
       visited1 st a -> ~ visited1 s0' a ->
       visited1 st b -> ~ visited1 s0' b ->
       reachable_rev a b -> ~ reachable_rev b a ->
       (exists c, mutually_reachable a c /\ finish st b < finish st c) \/
       (mutually_reachable a u' /\ finish st b <= timer st))).
  apply Hoare_bind with (Q := fun (_:unit) (st:St) => P_loop ∅ st).
  - unfold Hoare. split.
    + intros s1 [] st Hs1 Hprog. rewrite Hs1 in Hprog.
      pose proof Hprog as Hprog_scoped.
      cbv beta iota delta [visit1 custom] in Hprog.
      destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid Hnext]]]]].
      destruct Hinv_s0 as [[Hfc0 [Hzero0 [Hcard0 Htd0]]] Hscoped0].
      unfold P_loop.
      split.
      * unfold DFSFinishInv, DFSFinishInvCore.
        split.
        { split.
          - unfold FinishedCount in *. rewrite Htimer, Hfin. exact Hfc0.
          - split.
            + eapply (UnvisitedFinishZero_visit1 s0' st u'); [exact Hv|exact Hfin|exact Hzero0].
            + split.
              * eapply (cardV_visit1_nosteps s0' st u'); [exact Hv|exact Htimer|exact Hcard0].
              * unfold TimerDominates. intros x Hx.
                sets_unfold in Hv.
                destruct (proj1 (Hv x) Hx) as [Hx0 | Hu].
                -- rewrite Hfin, Htimer. apply Htd0. exact Hx0.
                -- subst x. rewrite Hfin, Htimer. rewrite Hzero0 by exact Hnot_u'. lia. }
        { eapply DFSFinishScoped_visit1; eauto. }
      * sets_unfold in Hv.
        repeat split.
        -- intros w Hw. apply Hv. left. exact Hw.
        -- apply Hv. right. reflexivity.
        -- rewrite Hfin. reflexivity.
        -- intros v w Hvis Hnew Hne. apply Hv in Hvis.
           destruct Hvis as [H0|Heq]; [exfalso; exact (Hnew H0)|subst; exfalso; exact (Hne eq_refl)].
        -- intros v Hvis Hnew. apply Hv in Hvis.
           destruct Hvis as [H0|Heq]; [exfalso; exact (Hnew H0)|subst; apply SCC.rr_refl].
        -- intros z Hz. rewrite Hfin. reflexivity.
        -- exact Hv2.
        -- exact Hsid.
        -- exact Hnext.
        -- rewrite Htimer. lia.
        -- intros v Hne Hvis. apply Hv in Hvis.
           destruct Hvis as [H0|Heq]; [left; exact H0|exfalso; exact (Hne (eq_sym Heq))].
        -- intros v Hvis Hnew Hne. apply Hv in Hvis.
           destruct Hvis as [H0|Heq]; [exfalso; exact (Hnew H0)|subst; exfalso; exact (Hne eq_refl)].
        -- intros v Hvis Hnew Hne. apply Hv in Hvis.
           destruct Hvis as [H0|Heq]; [exfalso; exact (Hnew H0)|subst; exfalso; exact (Hne eq_refl)].
        -- intros e v He. exfalso. exact He.
        -- intros HR v Hvis Hnot_closed. apply Hv in Hvis.
           destruct Hvis as [H0|Heq].
           ++ apply HR; [exact H0|].
              intro Hcl. apply Hnot_closed. intros w Hstep. apply Hv. left. apply Hcl. exact Hstep.
           ++ subst v. apply SCC.rr_refl.
        -- intros HR a0 b0 Ha0 Hna0 Hb0 Hnb0. apply Hv in Ha0. apply Hv in Hb0.
           destruct Ha0 as [H0|Heq]; [exfalso; exact (Hna0 H0)|subst a0].
           destruct Hb0 as [H0|Heq]; [exfalso; exact (Hnb0 H0)|subst b0].
           intros _ Hnot. exfalso. apply Hnot. apply SCC.rr_refl.
    + intros s1 Hs1 Herr. exfalso. exact Herr.
  - intros [].
    apply Hoare_normalize.
    intros st HPstart.
    destruct HPstart as (Hinv_st & Hsub & Hvis_u & Hfin_root & Hclosed_new &
      Hreach_new & Hfin_old & Hv2_s0 & Hsid_s0 & Hnext_s0 & Htimer_mono &
      Hfin_le_timer & Hge_timer & Hstrict_timer & He_set & HR_pres & HPO_pres).
    eapply Hoare_cons_pre.
    2: {
    apply Hoare_repeat_break with
      (P := P_loop)
      (Q := fun (_:unit) (s':St) =>
        DFSFinishFrame s0' tt s' /\
        Q_phase1 u' s0' tt s' /\
        (forall v, visited1 s' v -> ~ visited1 s0' v -> timer s0' < finish s' v)).
    intros e_set.
    apply Hoare_choice.
    + apply Hoare_bind with (Q := fun (e:E) st' => P_loop e_set st').
      * apply Hoare_any.
      * intro e. apply Hoare_bind with (Q := fun (v:V) st' => P_loop e_set st').
        -- apply Hoare_any.
        -- intro v.
           apply Hoare_assumeS_bind.
           apply Hoare_assumeS_bind.
           apply Hoare_assumeS_bind.
           apply Hoare_normalize.
           intros s1 [[[HP _] Hnot_v] Hstep].
           unfold P_loop in HP.
           destruct HP as (Hinv1 & Hsub1 & Hvis_u1 & Hfin_root1 & Hclosed_new1 & Hreach_new1 &
             Hfin_old1 & Hv2_s01 & Hsid_s01 & Hnext_s01 &
             Htimer_mono1 & Hfin_le_timer1 & Hge_timer1 & Hstrict_timer1 &
             He_set1 & HR_pres1 & HPO_pres1).
	           apply Hoare_bind with (Q := fun (pre:St) st' => pre = st' /\ st' = s1).
	           ++ apply Hoare_get.
	           ++ intro pre. apply Hoare_normalize.
	              intros st_pre [Hpre Hst_pre]. subst st_pre. subst pre.
	           apply Hoare_bind with (Q := fun (_:unit) s2 =>
	             DFSFinishFrame s1 tt s2 /\
	             Q_phase1 v s1 tt s2 /\
	             (forall x, visited1 s2 x -> ~ visited1 s1 x -> timer s1 < finish s2 x)).
		              ** apply IH.
		                 --- exact Hinv1.
		                 --- exact Hnot_v.
		                 --- eapply step_vvalid1; eauto.
		              ** intros []. apply Hoare_normalize.
	              intros s2 [Hframe2 [HQ2 Hstrict2]].
	              destruct Hframe2 as [Hinv2 [Hsub2 [Hfin_frame2 [Hv2_eq2 [Hsid_eq2 Hnext_eq2]]]]].
	              destruct HQ2 as [Hsubq2 [Hvis_v2 [Hclosed2 [Hreach2
	                [Hfin_v_le [Hfin_old2 [Htimer2 [Hfin_lt_v [Hge2
	                [HR2 HPO2]]]]]]]]]].
	              apply Hoare_assertS_bind.
		              --- intros st_assert Hst_assert. subst st_assert.
		                 split; [ exact Hinv2 | split; [ exact Hvis_v2 | exact Hsub2 ] ].
		              --- apply Hoare_ret. intros st' Hst'. subst st'.
	              unfold P_loop. split; [exact Hinv2|].
              repeat split.
	              ---- intros x Hx. apply Hsub2. apply Hsub1. exact Hx.
	              ---- apply Hsub2. exact Hvis_u1.
	              ---- transitivity (finish s1 u').
	                 ----- apply Hfin_frame2. exact Hvis_u1.
	                 ----- exact Hfin_root1.
	              ---- intros x w Hvis_x Hnew_x Hne_x Hstep_xw.
                 destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
	                 ----- apply Hsub2. exact (Hclosed_new1 x w Hx_s1 Hnew_x Hne_x Hstep_xw).
	                 ----- exact (Hclosed2 x w Hvis_x Hx_ns1 Hstep_xw).
	              ---- intros x Hvis_x Hnew_x.
                 destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
	                 ----- exact (Hreach_new1 x Hx_s1 Hnew_x).
	                 ----- refine (reachable_rev_trans u' v x _ _).
                     { unfold reachable_rev. apply (SCC.rr_step g u' v v).
                       - unfold step_rev. exists e. exact Hstep.
                       - apply SCC.rr_refl. }
                     { exact (Hreach2 x Hvis_x Hx_ns1). }
	              ---- intros z Hz.
                 assert (Hz_s1 : visited1 s1 z) by (apply Hsub1; exact Hz).
                 assert (Hz_ne_v : z <> v) by (intro Heq; subst; exact (Hnot_v Hz_s1)).
                 rewrite (Hfin_old2 z Hz_s1 Hz_ne_v). exact (Hfin_old1 z Hz).
	              ---- rewrite Hv2_eq2. exact Hv2_s01.
	              ---- rewrite Hsid_eq2. exact Hsid_s01.
	              ---- rewrite Hnext_eq2. exact Hnext_s01.
	              ---- etransitivity; eauto.
	              ---- intros x Hne Hvis_x.
                 destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
	                 ----- destruct (Hfin_le_timer1 x Hne Hx_s1) as [Hx_old|Hx_le].
                     { left. exact Hx_old. }
                     { right. assert (Hx_ne_v : x <> v)
                         by (intro Heq; subst; exact (Hnot_v Hx_s1)).
                       rewrite (Hfin_old2 x Hx_s1 Hx_ne_v). lia. }
	                 ----- right. destruct (classic (x = v)) as [->|Hx_ne_v].
                     { exact Hfin_v_le. }
                     { destruct (Hfin_lt_v x Hx_ne_v Hvis_x) as [Hx_s1'|Hx_lt];
                         [exfalso; exact (Hx_ns1 Hx_s1')|lia]. }
	              ---- intros x Hvis_x Hnew_x Hne_x.
                 destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
	                 ----- assert (Hx_ne_v : x <> v)
                       by (intro Heq; subst; exact (Hnot_v Hx_s1)).
                     rewrite (Hfin_old2 x Hx_s1 Hx_ne_v).
                     exact (Hge_timer1 x Hx_s1 Hnew_x Hne_x).
	                 ----- pose proof (Hge2 x Hvis_x Hx_ns1). lia.
	              ---- intros x Hvis_x Hnew_x Hne_x.
                 destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
	                 ----- assert (Hx_ne_v : x <> v)
                       by (intro Heq; subst; exact (Hnot_v Hx_s1)).
                     rewrite (Hfin_old2 x Hx_s1 Hx_ne_v).
                     exact (Hstrict_timer1 x Hx_s1 Hnew_x Hne_x).
	                 ----- pose proof (Hstrict2 x Hvis_x Hx_ns1). lia.
	              ---- intros e0 v0 He0 Hstep0.
                 sets_unfold in He0. destruct He0 as [He0_in|He0_eq].
	                 ----- apply Hsub2. apply (He_set1 e0 v0 He0_in Hstep0).
	                 ----- subst e0.
                     destruct (KG.(kos_unique).(step_aux_unique) g e v u' v0 u' g_valid Hstep Hstep0) as [Hv_eq _].
                     subst v0. exact Hvis_v2.
	              ---- intros HR0 z Hvis_z Hnot_closed_z.
                 pose proof (HR_pres1 HR0) as HR1.
                 destruct (classic (visited1 s1 z)) as [Hz_s1|Hz_ns1].
	                 ----- apply HR1; [exact Hz_s1|].
                     intro Hcl. apply Hnot_closed_z.
                     intros w Hstepw. apply Hsub2. exact (Hcl w Hstepw).
	                 ----- exfalso. apply Hnot_closed_z.
                     intros w Hstepw. exact (Hclosed2 z w Hvis_z Hz_ns1 Hstepw).
	              ---- intros HR0 a0 b0 Ha0 Hna0 Hb0 Hnb0 Hrev Hnrev.
                 pose proof (HR_pres1 HR0) as HR1.
                 assert (Hrv : reachable_rev u' v).
                 { unfold reachable_rev. apply (SCC.rr_step g u' v v).
                   - unfold step_rev. exists e. exact Hstep.
                   - apply SCC.rr_refl. }
                 assert (HR_v : R_non_closed v s1).
                 { intros z Hz Hnc.
                   apply (reachable_rev_trans z u' v); [exact (HR1 z Hz Hnc)|exact Hrv]. }
                 assert (Hb0_ne_u' : b0 <> u').
                 { intro Heq; subst b0; apply Hnrev.
                   destruct (classic (visited1 s1 a0)) as [Ha0_s1|Ha0_ns1].
                   - exact (Hreach_new1 a0 Ha0_s1 Hna0).
                   - apply (reachable_rev_trans u' v a0); [exact Hrv|].
                     exact (Hreach2 a0 Ha0 Ha0_ns1). }
                 destruct (classic (visited1 s1 a0)) as [Ha0_s1|Ha0_ns1];
                 destruct (classic (visited1 s1 b0)) as [Hb0_s1|Hb0_ns1].
	                 ----- assert (Hb0_ne_v : b0 <> v) by (intro Heq; subst; exact (Hnot_v Hb0_s1)).
                     destruct (HPO_pres1 HR0 a0 b0 Ha0_s1 Hna0 Hb0_s1 Hnb0 Hrev Hnrev)
                       as [[c [Hmr Hfin]]|[Hmr Hfin]].
                     { destruct (classic (visited1 s1 c)) as [Hc_s1|Hc_ns1].
                       - left. exists c. split; [exact Hmr|].
                         assert (Hc_ne_v : c <> v) by (intro Heq; subst; exact (Hnot_v Hc_s1)).
                         rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v), (Hfin_old2 c Hc_s1 Hc_ne_v).
                         exact Hfin.
                       - right. split.
                         + split.
                           * apply reachable_iff_reachable_rev.
                               exact (Hreach_new1 a0 Ha0_s1 Hna0).
                           * apply reachable_iff_reachable_rev.
                               destruct Hmr as [_ Hc_a0].
                               apply reachable_iff_reachable_rev in Hc_a0.
                               pose proof (visited_boundary_not_closed (visited1 s1) a0 c
                                             Ha0_s1 Hc_ns1 Hc_a0) as [z [Hz_vis [Hz_nc Hz_reach]]].
                               exact (reachable_rev_trans a0 z u' Hz_reach (HR1 z Hz_vis Hz_nc)).
                         + rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v).
                            destruct (Hfin_le_timer1 b0 Hb0_ne_u' Hb0_s1) as [Hb0_old|Hb0_le];
                              [exfalso; exact (Hnb0 Hb0_old)|lia]. }
                     { right. split; [exact Hmr|].
                       rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v). lia. }
	                 ----- right. split.
                     { split.
                       - apply reachable_iff_reachable_rev.
                         exact (Hreach_new1 a0 Ha0_s1 Hna0).
                       - apply reachable_iff_reachable_rev.
                         pose proof (visited_boundary_not_closed (visited1 s1) a0 b0
                                       Ha0_s1 Hb0_ns1 Hrev) as [z [Hz_vis [Hz_nc Hz_reach]]].
                         exact (reachable_rev_trans a0 z u' Hz_reach (HR1 z Hz_vis Hz_nc)). }
                     { destruct (classic (b0 = v)) as [->|Hb0_ne_v].
                       - exact Hfin_v_le.
                       - destruct (Hfin_lt_v b0 Hb0_ne_v Hb0) as [Hb0_s1'|Hb0_lt];
                           [exfalso; exact (Hb0_ns1 Hb0_s1')|lia]. }
	                 ----- assert (Hb0_ne_v : b0 <> v) by (intro Heq; subst; exact (Hnot_v Hb0_s1)).
	                     left. exists a0. split.
	                     { apply mutually_reachable_self_from_rev. }
	                     { rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v).
	                       assert (Hfin_b0 : finish s1 b0 <= timer s1).
	                       { destruct (Hfin_le_timer1 b0 Hb0_ne_u' Hb0_s1) as [Hb0_old|Hb0_le];
	                           [exfalso; exact (Hnb0 Hb0_old)|exact Hb0_le]. }
                       pose proof (Hstrict2 a0 Ha0 Ha0_ns1). lia. }
	                 ----- left. exact (HPO2 HR_v a0 b0 Ha0 Ha0_ns1 Hb0 Hb0_ns1 Hrev Hnrev).
    + apply Hoare_assumeS_bind.
      apply Hoare_normalize.
      intros s1 [HP Hall].
      unfold P_loop in HP.
      destruct HP as (Hinv1 & Hsub1 & Hvis_u1 & Hfin_root1 & Hclosed_new1 & Hreach_new1 &
        Hfin_old1 & Hv2_s01 & Hsid_s01 & Hnext_s01 &
        Htimer_mono1 & Hfin_le_timer1 & Hge_timer1 & Hstrict_timer1 &
        He_set1 & HR_pres1 & HPO_pres1).
	      apply Hoare_assertS_bind.
	      * intros st' Hst'. subst st'. exact Hinv1.
	      * apply Hoare_assertS_bind.
        -- intros st' Hst'. subst st'. exact (DFSFinishInv_finished_count _ Hinv1).
	        -- apply Hoare_bind with (Q := fun (t:nat) st' => t = timer st' /\ st' = s1).
	           ++ apply Hoare_get.
	           ++ intro t. apply Hoare_normalize.
           intros st_get [Ht Hst_get]. subst st_get.
           apply Hoare_bind with
             (Q := fun (_:unit) st' =>
               timer st' = S (timer s1) /\
               finish st' u' = S (timer s1) /\
               (forall v, v <> u' -> finish st' v = finish s1 v) /\
               visited1 st' = visited1 s1 /\
               visited2 st' = visited2 s1 /\
               scc_id st' = scc_id s1 /\
               scc_next st' = scc_next s1).
	              ** apply (Hoare_cons_post
                (fun st' => st' = s1)
                (set_finish u' t)
                (fun (_:unit) st' =>
                   timer st' = S (timer s1) /\
                   finish st' u' = S t /\
                   (forall v, v <> u' -> finish st' v = finish s1 v) /\
                   visited1 st' = visited1 s1 /\
                   visited2 st' = visited2 s1 /\
                   scc_id st' = scc_id s1 /\
                   scc_next st' = scc_next s1)).
	                 --- intros _ st' [Htimer [Hfin_set [Hfin_other [Hv1_eq [Hv2_eq [Hsid_eq Hnext_eq]]]]]].
                 split; [exact Htimer|].
                 split.
                 { rewrite <- Ht. exact Hfin_set. }
                 repeat split; assumption.
	                 --- apply Hoare_set_finish_raw.
	              ** intros [].
              apply Hoare_ret. intros st' [Htimer [Hfin_set [Hfin_other [Hv1_eq [Hv2_eq [Hsid_eq Hnext_eq]]]]]].
              assert (Hfin_u_zero : finish s1 u' = 0).
              { rewrite Hfin_root1.
                pose proof (DFSFinishInv_unvisited_zero _ Hinv_s0) as Hzero0.
                apply Hzero0. exact Hnot_u'. }
              unfold DFSFinishFrame.
              split.
	              ---- split.
                 { unfold DFSFinishInv, DFSFinishInvCore.
                   split.
                   { split.
                     - eapply FinishedCount_set_finish_zero; eauto.
                       exact (DFSFinishInv_finished_count _ Hinv1).
                     - split.
                       + eapply UnvisitedFinishZero_finish_update.
                         * exact Hv1_eq.
                         * exact Hfin_other.
                         * exact (DFSFinishInv_unvisited_zero _ Hinv1).
                         * exact Hvis_u1.
                       + split.
                         * rewrite Hv1_eq.
                           pose proof (DFSFinishInv_strict_unfinished s1 u' Hinv1 Hvalid_u' Hvis_u1 Hfin_u_zero).
                           lia.
                         * unfold TimerDominates. intros x Hvis_x.
                           rewrite Hv1_eq in Hvis_x.
                           destruct (classic (x = u')) as [-> | Hne].
                           -- rewrite Hfin_set. rewrite Htimer. lia.
                           -- rewrite Hfin_other by exact Hne.
                              pose proof (DFSFinishInv_timer_dominates _ Hinv1 x Hvis_x).
                              rewrite Htimer. lia. }
                   { destruct (DFSFinishInv_scoped _ Hinv1) as [Hvis_invalid Hfin_invalid].
                     split.
                     - intros x Hinvalid Hvisited.
                       rewrite Hv1_eq in Hvisited.
                       exact (Hvis_invalid x Hinvalid Hvisited).
                     - intros x Hinvalid.
                       rewrite Hfin_other.
                       + exact (Hfin_invalid x Hinvalid).
                       + intro Heq. subst x. contradiction. } }
                 repeat split.
	                 ----- intros x Hx. rewrite Hv1_eq. apply Hsub1. exact Hx.
	                 ----- intros x Hx.
                     rewrite Hfin_other by (intro Heq; subst x; exact (Hnot_u' Hx)).
                     apply Hfin_old1. exact Hx.
	                 ----- rewrite Hv2_eq. exact Hv2_s01.
	                 ----- rewrite Hsid_eq. exact Hsid_s01.
	                 ----- rewrite Hnext_eq. exact Hnext_s01.
	              ---- repeat split.
	                 ----- intros x Hx. rewrite Hv1_eq. apply Hsub1. exact Hx.
	                 ----- rewrite Hv1_eq. exact Hvis_u1.
		                 ----- intros x0 w0 Hvis_x0 Hnew_x0 Hstep_x0.
	                     rewrite Hv1_eq in *.
	                     destruct (classic (x0 = u')) as [->|Hne].
	                     { unfold step_rev in Hstep_x0. destruct Hstep_x0 as [e0 Hstep_aux0].
	                       destruct (Hall e0 w0 Hstep_aux0) as [He0|Hw0].
	                       - apply (He_set1 e0 w0 He0 Hstep_aux0).
	                       - exact Hw0. }
	                     { apply (Hclosed_new1 x0 w0 Hvis_x0 Hnew_x0 Hne Hstep_x0). }
	                 ----- intros x0 Hvis_x0 Hnew_x0.
                     rewrite Hv1_eq in Hvis_x0.
                     exact (Hreach_new1 x0 Hvis_x0 Hnew_x0).
	                 ----- rewrite Htimer. lia.
	                 ----- intros z Hz Hz_ne.
                     rewrite Hfin_other by exact Hz_ne.
                     apply Hfin_old1. exact Hz.
	                 ----- rewrite Htimer. lia.
		                 ----- intros x0 Hne Hvis_x0.
	                     rewrite Hv1_eq in Hvis_x0.
	                     destruct (Hfin_le_timer1 x0 Hne Hvis_x0) as [Hx_old|Hx_le].
	                     { left. exact Hx_old. }
	                     { right. rewrite Hfin_set.
	                       rewrite (Hfin_other x0 Hne). lia. }
			                 ----- intros x0 Hvis_x0 Hnew_x0.
		                     rewrite Hv1_eq in Hvis_x0.
		                     destruct (classic (x0 = u')) as [->|Hne].
		                     { rewrite Hfin_set. lia. }
		                     { rewrite Hfin_other by exact Hne.
		                       apply Hge_timer1; auto. }
		                 ----- intro HR0. unfold R_non_closed.
                     intros z Hz Hnc.
                     rewrite Hv1_eq in Hz.
                     assert (Hnc' : ~ (forall w, step_rev z w -> visited1 s1 w)).
                     { intro Hcl. apply Hnc. intros w Hstepw.
                       rewrite Hv1_eq. exact (Hcl w Hstepw). }
                     exact (HR_pres1 HR0 z Hz Hnc').
	                 ----- intro HR0. intros a0 b0 Ha0 Hna0 Hb0 Hnb0 Hrev Hnrev.
                     rewrite Hv1_eq in Ha0, Hb0.
                     assert (Hb0_ne_u' : b0 <> u')
                       by (intro Heq; subst b0; apply Hnrev; exact (Hreach_new1 a0 Ha0 Hna0)).
	                     destruct (HPO_pres1 HR0 a0 b0 Ha0 Hna0 Hb0 Hnb0 Hrev Hnrev)
	                       as [[c [Hmr Hfin]]|[Hmr Hfin]].
	                     { destruct (classic (c = u')) as [->|Hc_ne].
	                       - exists u'. split; [exact Hmr|].
	                         rewrite Hfin_set, (Hfin_other b0 Hb0_ne_u'). lia.
	                       - exists c. split; [exact Hmr|].
	                         rewrite (Hfin_other b0 Hb0_ne_u'), (Hfin_other c Hc_ne). exact Hfin. }
		                     { exists u'. split; [exact Hmr|].
		                       rewrite Hfin_set, (Hfin_other b0 Hb0_ne_u'). lia. }
			                 ----- intros x0 Hvis_x0 Hnew_x0.
		                     rewrite Hv1_eq in Hvis_x0.
		                     destruct (classic (x0 = u')) as [->|Hne].
		                     { rewrite Hfin_set. lia. }
		                     { rewrite Hfin_other by exact Hne.
		                       apply Hstrict_timer1; auto. }
    }
    intros st' Hst'. subst st'.
    unfold P_loop.
    split; [exact Hinv_st|].
    repeat split; try assumption.
Qed.

Lemma DFS_finish_phase1_plus : forall s0 u,
  ReachRevClosed s0 ->
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' =>
      DFSFinishFrame s0 tt s' /\
      Q_phase1 u s0 tt s' /\
      (forall v, visited1 s' v -> ~ visited1 s0 v -> timer s0 < finish s' v)).
Proof.
  intros s0 u Hclosed Hinv Hnot Hvalid.
  apply (DFS_finish_phase1_core s0 u Hclosed Hinv Hnot Hvalid).
Qed.

Definition Phase1_R (s : St) : Prop :=
  ReachRevClosed s /\
  DFSFinishInv s /\
  (forall a b, visited1 s a -> visited1 s b ->
    reachable_rev a b -> ~ reachable_rev b a ->
    exists c, mutually_reachable a c /\ finish s b < finish s c).

Lemma DFS_finish_preserves_Phase1_R : forall s0 u,
  Phase1_R s0 ->
  ~ visited1 s0 u ->
  vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' => Phase1_R s' /\ visited1 s0 ⊆ visited1 s' /\ visited1 s' u).
Proof.
  intros s0 u [Hclosed0 [Hinv0 Hphase0]] Hnot_u Hvalid_u.
  apply Hoare_imp_post with
    (Q := fun (_:unit) (s':St) =>
      DFSFinishFrame s0 tt s' /\
      Q_phase1 u s0 tt s' /\
      (forall v, visited1 s' v -> ~ visited1 s0 v -> timer s0 < finish s' v)).
  - apply DFS_finish_phase1_plus; assumption.
  - intros _ s2 [Hframe [Hq Hstrict]].
    destruct Hframe as [Hinv2 [Hsub0 [Hfin_old [Hv2_eq [Hsid_eq Hnext_eq]]]]].
    destruct Hq as
      [Hsubq [Hvis_u [Hstep_new [Hreach_u [Hfin_u_le
      [Hfin_old_ne [Htimer_mono [Hfinish_below [Hnew_lower
      [HRnc_pres Hphase_new]]]]]]]]]].
    split.
    + unfold Phase1_R.
      split.
      * unfold ReachRevClosed.
        intros v w Hvis_v Hreach_vw.
        destruct (classic (visited1 s0 v)) as [Hv_old | Hv_new].
        -- apply Hsub0. exact (Hclosed0 v w Hv_old Hreach_vw).
        -- destruct (classic (visited1 s0 w)) as [Hw_old | Hw_new].
           ++ apply Hsub0. exact Hw_old.
           ++ unfold reachable_rev in Hreach_vw.
              revert Hvis_v Hv_new Hw_new.
              refine (SCC.reachable_rev_ind _
                (fun a b => visited1 s2 a -> ~ visited1 s0 a ->
                  ~ visited1 s0 b -> visited1 s2 b)
                _ _ _ _ Hreach_vw).
              ** intros x Hx _ _. exact Hx.
              ** intros a x y Hstep Hreach_xy IHxy Hvis_a Hnew_a Hnew_y.
                 assert (Hvis_x : visited1 s2 x).
                 { apply Hstep_new with (v := a).
                   - exact Hvis_a.
                   - exact Hnew_a.
                   - exact Hstep. }
                 destruct (classic (visited1 s0 x)) as [Hx_old | Hx_new].
                 --- apply Hsub0. exact (Hclosed0 x y Hx_old Hreach_xy).
                 --- apply IHxy; assumption.
      * split.
        -- exact Hinv2.
        -- intros a b Hvis_a2 Hvis_b2 Hreach_ab Hnot_ba.
           destruct (classic (visited1 s0 a)) as [Ha_old | Ha_new].
           ++ destruct (classic (visited1 s0 b)) as [Hb_old | Hb_new].
              ** destruct (Hphase0 a b Ha_old Hb_old Hreach_ab Hnot_ba) as [c [Hmut Hlt]].
                 exists c. split; [exact Hmut|].
                 assert (Hc_old : visited1 s0 c).
                 { unfold mutually_reachable in Hmut.
                   destruct Hmut as [_ Hc_a].
                   apply Hclosed0 with (v := a).
                   - exact Ha_old.
                   - apply reachable_iff_reachable_rev. exact Hc_a. }
                 rewrite (Hfin_old c Hc_old).
                 rewrite (Hfin_old b Hb_old).
                 exact Hlt.
              ** exfalso. apply Hb_new. exact (Hclosed0 a b Ha_old Hreach_ab).
           ++ destruct (classic (visited1 s0 b)) as [Hb_old | Hb_new].
              ** exists a. split.
                 { apply mutually_reachable_self_from_rev. }
                 { rewrite (Hfin_old b Hb_old).
                   pose proof (Hstrict a Hvis_a2 Ha_new) as Hlt_a.
                   pose proof (DFSFinishInv_timer_dominates _ Hinv0 b Hb_old) as Htd_b.
                   lia. }
              ** destruct (Hphase_new (R_non_closed_from_ReachRevClosed s0 u Hclosed0)
                    a b Hvis_a2 Ha_new Hvis_b2 Hb_new Hreach_ab Hnot_ba) as
                   [c [Hmut Hlt]].
                 exists c. split; [exact Hmut | exact Hlt].
    + split; assumption.
Qed.

Lemma kosaraju_finish_schedule_Phase1_R : forall root_at start fuel s0,
  (forall i, start <= i < start + fuel -> vvalid g (root_at i))%nat ->
  Phase1_R s0 ->
  Hoare (fun st => st = s0)
    (kosaraju_finish_schedule root_at start fuel)
    (fun _ s' =>
      Phase1_R s' /\
      visited1 s0 ⊆ visited1 s' /\
      forall i, (start <= i < start + fuel)%nat -> visited1 s' (root_at i)).
Proof.
  intros root_at start fuel.
  revert start.
  induction fuel as [|fuel IH]; intros start s0 Hvalid_roots HR0.
  - rewrite kosaraju_finish_schedule_done.
    apply Hoare_ret. intros s' Hs'. subst s'.
    split; [exact HR0 |].
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
        -- apply IH.
           ++ intros i Hi.
              apply Hvalid_roots. lia.
           ++ exact HR0.
        -- intros _ s' [HR' [Hsub Hdone]].
        split; [exact HR' |].
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
        -- apply DFS_finish_preserves_Phase1_R.
           ++ exact HR0.
           ++ exact Hroot_not.
           ++ apply Hvalid_roots. lia.
        -- intros [].
           apply Hoare_normalize.
           intros s1 [HR1 [Hsub01 Hroot_vis]].
           eapply Hoare_imp_post.
           ++ apply IH.
              ** intros i Hi.
                 apply Hvalid_roots. lia.
              ** exact HR1.
           ++ intros _ s' [HR' [Hsub1 Hdone]].
           split; [exact HR' |].
           split.
           ** intros x Hx. apply Hsub1. apply Hsub01. exact Hx.
           ** intros i Hi.
              destruct (Nat.eq_dec i start) as [-> | Hne].
              --- apply Hsub1. exact Hroot_vis.
              --- apply Hdone. lia.
Qed.

Lemma kosaraju_finish_schedule_phase1_order : forall root_at start fuel,
  (forall v, vvalid g v ->
    exists i, (start <= i < start + fuel)%nat /\ root_at i = v) ->
  (forall i, (start <= i < start + fuel)%nat -> vvalid g (root_at i)) ->
  Hoare (fun st => st = init_st)
    (kosaraju_finish_schedule root_at start fuel)
    (fun _ s' => Phase1_Order s').
Proof.
  intros root_at start fuel Hcovers Hvalid_roots.
  eapply Hoare_imp_post.
  - apply kosaraju_finish_schedule_Phase1_R.
    + exact Hvalid_roots.
    + unfold Phase1_R.
      split.
      * unfold ReachRevClosed, init_st. intros v w Hfalse _. contradiction.
      * split.
        -- apply DFSFinishInv_init.
        -- unfold init_st. intros a b Hfalse _ _ _. contradiction.
  - intros _ s' [HR' [_ Hdone]].
    unfold Phase1_R in HR'.
    destruct HR' as [_ [_ Hphase]].
	    unfold Phase1_Order.
	    intros a b Hreach Hnot.
    assert (Hreach_ba : reachable g b a).
    { apply reachable_iff_reachable_rev. exact Hreach. }
	    apply Hphase.
	    + destruct (Hcovers a) as [i [Hi Hroot]].
	      { destruct (classic (a = b)) as [-> | Hne].
	        - exfalso. apply Hnot. exact Hreach.
	        - pose proof (@reachable_vvalid G V E g _ _ _ b a
              (fun Heq => Hne (eq_sym Heq))
	            Hreach_ba) as [_ Ha].
	          exact Ha. }
	      rewrite <- Hroot. apply Hdone. exact Hi.
	    + destruct (Hcovers b) as [i [Hi Hroot]].
	      { destruct (classic (a = b)) as [Heq | Hne].
	        - subst b. exfalso. apply Hnot. exact Hreach.
	        - pose proof (@reachable_vvalid G V E g _ _ _ b a
              (fun Heq => Hne (eq_sym Heq))
	            Hreach_ba) as [Hb _].
	          exact Hb. }
	      rewrite <- Hroot. apply Hdone. exact Hi.
	    + exact Hreach.
	    + exact Hnot.
Qed.

(** Phase 1 establishes the condensation-DAG ordering: if a can
    reverse-reach b but not vice versa, then a's SCC contains a
    vertex with strictly larger finish than b's. *)
Lemma kosaraju_finish_phase1_order :
  Hoare (fun st => st = init_st) kosaraju_finish (fun _ s' => Phase1_Order s').
Proof.
  unfold kosaraju_finish.
  set (R := fun s =>
    ReachRevClosed s /\
    DFSFinishInv s /\
    (forall a b, visited1 s a -> visited1 s b ->
      reachable_rev a b -> ~ reachable_rev b a ->
      exists c, mutually_reachable a c /\ finish s b < finish s c)).
  set (Q := fun (_:unit) (_:St) (_:unit) (s':St) => Phase1_Order s').
  apply Hoare_normal_LFix_closed with (R := R) (Q := Q).
  - intros W IH s0' u0 HR.
    destruct HR as [Hclosed0 [Hinv0 Hphase0]].
    unfold kosaraju_finish_f.
    apply Hoare_choice.
    + apply Hoare_bind with
        (Q := fun (u:V) (s':St) =>
          s' = s0' /\ vvalid g u /\ ~ visited1 s' u).
      * unfold Hoare. split.
        -- intros s1 a s2 Hs1 Hprog.
           rewrite Hs1 in *.
           cbv beta iota delta [pick_unvisited1 MonadErr.nrm_nrm get] in Hprog.
           destruct Hprog as [[Hvv Hnot_vis] Hsame].
           rewrite Hsame in Hnot_vis.
           split; [symmetry; exact Hsame | split; [exact Hvv | exact Hnot_vis]].
        -- intros s1 Hs1 Herr. exfalso.
           cbv beta iota delta [pick_unvisited1 MonadErr.nrm_err get] in Herr.
           sets_unfold in Herr. firstorder.
      * intro u.
        apply Hoare_normalize.
        intros s1 [Hs1_eq [Hvalid_u Hunvis_u]]; subst s1.
        apply Hoare_bind with
          (Q := fun (_:unit) (s':St) =>
            DFSFinishFrame s0' tt s' /\
            Q_phase1 u s0' tt s' /\
            (forall v, visited1 s' v -> ~ visited1 s0' v -> timer s0' < finish s' v)).
        -- apply DFS_finish_phase1_plus; assumption.
        -- intro junk.
           apply Hoare_normalize.
           intros s2 [Hframe [Hq Hstrict]].
           apply (IH s2 tt).
           unfold R.
           destruct Hframe as [Hinv2 [Hsub0 [Hfin_old [Hv2_eq [Hsid_eq Hnext_eq]]]]].
           destruct Hq as
             [Hsubq [Hvis_u [Hstep_new [Hreach_u [Hfin_u_le
             [Hfin_old_ne [Htimer_mono [Hfinish_below [Hnew_lower
             [HRnc_pres Hphase_new]]]]]]]]]].
           split.
           ++ unfold ReachRevClosed.
              intros v w Hvis_v Hreach_vw.
              destruct (classic (visited1 s0' v)) as [Hv_old | Hv_new].
              ** apply Hsub0. exact (Hclosed0 v w Hv_old Hreach_vw).
              ** destruct (classic (visited1 s0' w)) as [Hw_old | Hw_new].
                 --- apply Hsub0. exact Hw_old.
                 --- unfold reachable_rev in Hreach_vw.
                     revert Hvis_v Hv_new Hw_new.
                     refine (SCC.reachable_rev_ind _
                       (fun a b => visited1 s2 a -> ~ visited1 s0' a ->
                         ~ visited1 s0' b -> visited1 s2 b)
                       _ _ _ _ Hreach_vw).
                     +++ intros x Hx _ _. exact Hx.
                     +++ intros a x y Hstep Hreach_xy IHxy Hvis_a Hnew_a Hnew_y.
                         assert (Hvis_x : visited1 s2 x).
                         { apply Hstep_new with (v := a).
                           - exact Hvis_a.
                           - exact Hnew_a.
                           - exact Hstep. }
                         destruct (classic (visited1 s0' x)) as [Hx_old | Hx_new].
                         *** apply Hsub0. exact (Hclosed0 x y Hx_old Hreach_xy).
                         *** apply IHxy; assumption.
           ++ split.
              ** exact Hinv2.
              ** intros a b Hvis_a2 Hvis_b2 Hreach_ab Hnot_ba.
                 destruct (classic (visited1 s0' a)) as [Ha_old | Ha_new].
                 --- destruct (classic (visited1 s0' b)) as [Hb_old | Hb_new].
                     +++ destruct (Hphase0 a b Ha_old Hb_old Hreach_ab Hnot_ba) as [c [Hmut Hlt]].
                         exists c. split; [exact Hmut|].
                         assert (Hc_old : visited1 s0' c).
                         { unfold mutually_reachable in Hmut.
                           destruct Hmut as [_ Hc_a].
                           apply Hclosed0 with (v := a).
                           - exact Ha_old.
                           - apply reachable_iff_reachable_rev. exact Hc_a. }
                         rewrite (Hfin_old c Hc_old).
                         rewrite (Hfin_old b Hb_old).
                         exact Hlt.
                     +++ exfalso. apply Hb_new. exact (Hclosed0 a b Ha_old Hreach_ab).
                 --- destruct (classic (visited1 s0' b)) as [Hb_old | Hb_new].
                     +++ exists a. split.
                         *** apply mutually_reachable_self_from_rev.
                         *** pose proof (Hstrict a Hvis_a2 Ha_new) as Hlt_a.
                             pose proof (DFSFinishInv_timer_dominates _ Hinv0 b Hb_old) as Htd_b.
                             rewrite (Hfin_old b Hb_old).
                             lia.
                     +++ apply Hphase_new.
                         *** apply R_non_closed_from_ReachRevClosed. exact Hclosed0.
                         *** exact Hvis_a2.
                         *** exact Ha_new.
                         *** exact Hvis_b2.
                         *** exact Hb_new.
                         *** exact Hreach_ab.
                         *** exact Hnot_ba.
    + apply Hoare_normal_assume_bind; intros Hall.
      apply Hoare_ret.
      intros s1 Hs1. subst s1.
      unfold Phase1_Order.
      intros a b Hreach_ab Hnot_ba.
      apply Hphase0; [apply Hall | apply Hall | exact Hreach_ab | exact Hnot_ba].
  - unfold R. split.
    + unfold ReachRevClosed, init_st. intros v w H. contradiction.
    + split.
      * apply DFSFinishInv_init.
      * intros a b Ha. contradiction.
Qed.

(* ================================================================= *)
(* 4. Inner DFS Phase 2 — Core Properties                            *)
(* ================================================================= *)

Definition neighbor_visited (st : St) (v : V) : Prop :=
  forall w, step g v w -> visited2 st w.

(** set_scc_id u root assigns scc_id[u] := scc_id[root]; other fields unchanged.
    Proved property: scc_id s' u = scc_id s0 root /\ ... *)
Lemma Hoare_set_scc_id : forall s0 u root P,
  (forall s1,
     scc_id s1 u = scc_id s0 root /\
     (forall v, v <> u -> scc_id s1 v = scc_id s0 v) /\
     timer s1 = timer s0 /\
     finish s1 = finish s0 /\
     visited1 s1 = visited1 s0 /\
     visited2 s1 = visited2 s0 /\
     scc_next s1 = scc_next s0 -> P s1) ->
  Hoare (fun st => st = s0) (set_scc_id u root) (fun _ => P).
Proof.
  intros s0 u root P H; unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [set_scc_id custom] in Hprog.
    destruct Hprog as [Huid [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
    apply H; split; [exact Huid | split; [exact Hother | split; [exact Htimer | split; [exact Hfin | split; [exact Hv1 | split; [exact Hv2 | exact Hscc_next]]]]]].
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

(** set_scc_root_id u assigns a fresh scc_id (scc_next) to u, then
    increments scc_next; other scc_id values unchanged.
    Proved property: scc_id s' u = scc_next s0 /\ scc_next s' = S(scc_next s0) /\ ... *)
Lemma Hoare_set_scc_root_id : forall s0 u P,
  (forall s1,
     scc_id s1 u = scc_next s0 /\
     scc_next s1 = S (scc_next s0) /\
     (forall v, v <> u -> scc_id s1 v = scc_id s0 v) /\
     timer s1 = timer s0 /\
     finish s1 = finish s0 /\
     visited1 s1 = visited1 s0 /\
     visited2 s1 = visited2 s0 -> P s1) ->
  Hoare (fun st => st = s0) (set_scc_root_id u) (fun _ => P).
Proof.
  intros s0 u P H; unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [set_scc_root_id custom] in Hprog.
    destruct Hprog as [Huid [Hscc_next [Hother [Htimer [Hfin [Hv1 Hv2]]]]]].
    apply H; split; [exact Huid | split; [exact Hscc_next | split; [exact Hother | split; [exact Htimer | split; [exact Hfin | split; [exact Hv1 | exact Hv2]]]]]].
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

Definition Q_scc_step_visited (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited2 s0' ⊆ visited2 s' /\
  visited2 s' u' /\
  (forall v, step g u' v -> visited2 s' v).

Definition DFSSccStable (root : V) (s0 st : St) : Prop :=
  scc_id st root = scc_id s0 root /\
  visited1 st = visited1 s0 /\
  finish st = finish s0 /\
  scc_next st = scc_next s0.

(** [DFS_scc_neighbor_visited_aux]
    Helper for the neighbor_visited invariant (forward graph analog of
    neighbor_visited_rev). Preserves visited2, subset, and neighbor_visited.
    Proved property: visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) *)
Lemma DFS_scc_neighbor_visited_aux : forall root W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u)
       (fun _ s' =>
          visited2 s' u /\
          visited2 s0 ⊆ visited2 s' /\
          (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) /\
          scc_id s' u = scc_id s' root /\
          (forall v, visited2 s0 v -> v <> u -> scc_id s' v = scc_id s0 v) /\
          DFSSccStable root s0 s')) ->
  (forall s0 u,
     Hoare (fun st => st = s0) (DFS_scc_f root W u)
       (fun _ s' =>
          visited2 s' u /\
          visited2 s0 ⊆ visited2 s' /\
          (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) /\
          scc_id s' u = scc_id s' root /\
          (forall v, visited2 s0 v -> v <> u -> scc_id s' v = scc_id s0 v) /\
          DFSSccStable root s0 s')).
Proof.
  intros root W IH s0 u.
  unfold DFS_scc_f.
  set (P_loop := fun (es : E -> Prop) (st : St) =>
    visited2 st u /\
    visited2 s0 ⊆ visited2 st /\
    (forall v, visited2 st v -> visited2 s0 v \/ v = u \/ neighbor_visited st v) /\
    (forall e v, e ∈ es -> step_aux g e u v -> visited2 st v) /\
    scc_id st u = scc_id st root /\
    (forall v, visited2 s0 v -> v <> u -> scc_id st v = scc_id s0 v) /\
    DFSSccStable root s0 st).
  apply Hoare_bind with (Q := fun (_:unit) (s1:St) =>
    visited2 s1 u /\
    visited2 s0 ⊆ visited2 s1 /\
    (forall x, visited2 s1 x -> visited2 s0 x \/ x = u) /\
    scc_id s1 = scc_id s0 /\
    visited1 s1 = visited1 s0 /\
    finish s1 = finish s0 /\
    scc_next s1 = scc_next s0).
  - unfold Hoare. split.
    + intros s1 [] s2 Hs1 Hprog. rewrite Hs1 in Hprog.
      cbv beta iota delta [visit2 custom] in Hprog.
      destruct Hprog as [Hv2 [_ [Hfin [Hv1 [Hsid Hnext]]]]].
      repeat split.
      * pose proof Hv2 as Hv2_unfold. sets_unfold in Hv2_unfold.
        apply Hv2_unfold. right; reflexivity.
      * intros x Hx. pose proof Hv2 as Hv2_unfold. sets_unfold in Hv2_unfold.
        apply Hv2_unfold. left; exact Hx.
      * intros x Hx. pose proof Hv2 as Hv2_unfold. sets_unfold in Hv2_unfold.
        destruct (proj1 (Hv2_unfold x) Hx) as [Hx0 | Hxu]; [left; exact Hx0 | right; symmetry; exact Hxu].
      * exact Hsid.
      * exact Hv1.
      * exact Hfin.
      * exact Hnext.
    + intros s1 Hs1 Herr. exfalso. exact Herr.
  - intros []. apply Hoare_normalize.
    intros s1 [Hvis_u1 [Hv2_sub1 [Hv2_char1 [Hsid1 [Hv1_1 [Hfin1 Hnext1]]]]]].
    apply Hoare_bind with (Q := fun (_:unit) (s2:St) => P_loop ∅ s2).
    + apply Hoare_set_scc_id with (P := fun s2 => P_loop ∅ s2).
      intros s2 [Huid [Hother [_ [Hfin2 [Hv1_2 [Hv2_2 Hnext2]]]]]].
      unfold P_loop, DFSSccStable.
      repeat split.
      * rewrite Hv2_2. exact Hvis_u1.
      * intros x Hx. rewrite Hv2_2. apply Hv2_sub1. exact Hx.
      * intros x Hx.
        rewrite Hv2_2 in Hx.
        destruct (Hv2_char1 x Hx) as [Hx0 | Hxu].
        -- left; exact Hx0.
        -- subst x. right. left. reflexivity.
      * intros e v Hempty _. exfalso. exact Hempty.
      * destruct (classic (root = u)) as [Hru | Hru].
        -- subst root. reflexivity.
        -- rewrite Huid, (Hother root Hru). rewrite Hsid1. reflexivity.
      * intros x Hx Hxu. rewrite (Hother x Hxu), Hsid1. reflexivity.
      * destruct (classic (root = u)) as [Hru | Hru].
        -- subst root. rewrite Huid, Hsid1. reflexivity.
        -- rewrite (Hother root Hru), Hsid1. reflexivity.
      * rewrite Hv1_2, Hv1_1. reflexivity.
      * rewrite Hfin2, Hfin1. reflexivity.
      * rewrite Hnext2, Hnext1. reflexivity.
    + intros []. simpl.
      apply Hoare_repeat_break with
          (P := P_loop)
          (Q := fun (_:unit) st =>
            visited2 st u /\
            visited2 s0 ⊆ visited2 st /\
            (forall v, visited2 st v -> visited2 s0 v \/ neighbor_visited st v) /\
            scc_id st u = scc_id st root /\
            (forall v, visited2 s0 v -> v <> u -> scc_id st v = scc_id s0 v) /\
            DFSSccStable root s0 st).
        intros e_set.
        apply Hoare_normalize.
        intros st [HPu [HPsub [HPneigh [HPedges [HPsid [HPold HPstable]]]]]].
        apply Hoare_choice.
        * apply Hoare_any_bind; intros e.
          apply Hoare_any_bind; intros v.
          apply Hoare_normal_assume_bind; intros Hnot_e.
          apply Hoare_normal_assume_bind; intros Hnot_v.
          apply Hoare_normal_assume_bind; intros Hstep.
          apply Hoare_bind with
            (Q := fun (_:unit) s3 =>
              visited2 s3 v /\
              visited2 st ⊆ visited2 s3 /\
              (forall x, visited2 s3 x -> visited2 st x \/ neighbor_visited s3 x) /\
              scc_id s3 v = scc_id s3 root /\
              (forall x, visited2 st x -> x <> v -> scc_id s3 x = scc_id st x) /\
              DFSSccStable root st s3).
          { exact (IH st v). }
          { intros []. apply Hoare_ret. intros s3 [Hchild_v [Hchild_sub [Hchild_neigh [Hchild_sid [Hchild_old Hchild_stable]]]]].
            destruct Hchild_stable as [Hroot_eq [Hv1_eq [Hfin_eq Hnext_eq]]].
            unfold P_loop, DFSSccStable in *.
            repeat split.
            * apply Hchild_sub. exact HPu.
            * intros x Hx. apply Hchild_sub, HPsub; exact Hx.
            * intros x Hx.
              destruct (Hchild_neigh x Hx) as [Hx_st | Hn3].
              -- destruct (HPneigh x Hx_st) as [Hx0 | [Hx_u | Hn_st]].
                 ++ left; exact Hx0.
                 ++ right. left; exact Hx_u.
                 ++ right. right. unfold neighbor_visited in *. intros w Hxw.
                    apply Hchild_sub. apply Hn_st. exact Hxw.
              -- right. right; exact Hn3.
            * intros e' w He_in Hstep'.
              sets_unfold in He_in.
              destruct He_in as [He_old | He_new].
              -- apply Hchild_sub. apply HPedges with (e := e'); assumption.
              -- subst e'.
                 destruct (step_aux_unique g e u v u w g_valid Hstep Hstep') as [_ Hvw].
                 subst w. exact Hchild_v.
            * rewrite (Hchild_old u HPu).
              -- rewrite Hroot_eq. exact HPsid.
              -- intro Huv; subst v. exact (Hnot_v HPu).
            * intros x Hx0 Hxu.
              rewrite (Hchild_old x).
              -- apply HPold; assumption.
              -- apply HPsub; exact Hx0.
              -- intro Hxv. subst v. apply Hnot_v, HPsub; exact Hx0.
            * rewrite Hroot_eq. destruct HPstable as [H _]. exact H.
            * rewrite Hv1_eq. destruct HPstable as [_ [H _]]. exact H.
            * rewrite Hfin_eq. destruct HPstable as [_ [_ [H _]]]. exact H.
            * rewrite Hnext_eq. destruct HPstable as [_ [_ [_ H]]]. exact H. }
        * apply Hoare_normal_assume_bind; intros Hall.
          apply Hoare_assertS_bind.
          { intros st' Hst'. subst st'. exact HPsid. }
          { apply Hoare_ret.
            intros st' Hst'. subst st'.
            assert (Hneigh_final : forall x, visited2 st x -> visited2 s0 x \/ neighbor_visited st x).
            { intros x Hx.
              destruct (HPneigh x Hx) as [Hx0 | [Hxu | Hnx]].
              - left; exact Hx0.
              - subst x. right. unfold neighbor_visited. intros w [e Hstep].
                destruct (Hall e w Hstep) as [He_done | Hvisited].
                + apply HPedges with (e := e); assumption.
                + exact Hvisited.
              - right; exact Hnx. }
            exact (conj HPu (conj HPsub (conj Hneigh_final (conj HPsid (conj HPold HPstable))))). }
Qed.

Lemma DFS_scc_neighbor_visited_stable : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u)
    (fun _ s' => visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) /\
      DFSSccStable root s0 s').
Proof.
  intros s0 root u.
  unfold DFS_scc.
  eapply Hoare_imp_post.
  - apply Hoare_normal_LFix with (Q := fun (u' : V) (s0' : St) (_ : unit) (s' : St) =>
      visited2 s' u' /\ visited2 s0' ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0' v \/ neighbor_visited s' v) /\
      scc_id s' u' = scc_id s' root /\
      (forall v, visited2 s0' v -> v <> u' -> scc_id s' v = scc_id s0' v) /\
      DFSSccStable root s0' s').
    intros W IH s0' u'.
    apply (DFS_scc_neighbor_visited_aux root).
    exact IH.
  - intros _ s' [Hu [Hsub [Hneigh [_ [_ Hstable]]]]].
    exact (conj Hu (conj Hsub (conj Hneigh Hstable))).
Qed.

(** [DFS_scc_neighbor_visited_strong]
    Fixed-point version of neighbor_visited for DFS_scc.
    Proved property: visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) *)
Lemma DFS_scc_neighbor_visited_strong : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u)
    (fun _ s' => visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v)).
Proof.
  intros s0 root u.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_stable.
  - intros _ s' [Hu [Hsub [Hneigh _]]].
    repeat split; assumption.
Qed.

(* SCC membership properties for Phase 2 correctness *)
(* L0a: all vertices newly visited by DFS_scc are reachable from u (the
   current vertex) in the original graph.  Direct mirror of
   DFS_finish_reachable_rev with step_rev replaced by step g. *)
(** [DFS_scc_reachable_aux]
    Helper: every newly visited2 vertex is reachable from u (forward graph)
    or was already in s0.
    Proved property: forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v *)
Lemma DFS_scc_reachable_aux : forall root W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u) (fun _ s' =>
       visited2 s' u /\
       visited2 s0 ⊆ visited2 s' /\
       (forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v) /\
       scc_id s' u = scc_id s' root /\
       (forall v, visited2 s0 v -> v <> u -> scc_id s' v = scc_id s0 v) /\
       DFSSccStable root s0 s')) ->
  (forall s0 u,
     Hoare (fun st => st = s0) (DFS_scc_f root W u) (fun _ s' =>
       visited2 s' u /\
       visited2 s0 ⊆ visited2 s' /\
       (forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v) /\
       scc_id s' u = scc_id s' root /\
       (forall v, visited2 s0 v -> v <> u -> scc_id s' v = scc_id s0 v) /\
       DFSSccStable root s0 s')).
Proof.
  intros root W IH s0 u.
  unfold DFS_scc_f.
  set (P_loop := fun (_ : E -> Prop) (st : St) =>
    visited2 st u /\
    visited2 s0 ⊆ visited2 st /\
    (forall v, visited2 st v -> visited2 s0 v \/ reachable g u v) /\
    scc_id st u = scc_id st root /\
    (forall v, visited2 s0 v -> v <> u -> scc_id st v = scc_id s0 v) /\
    DFSSccStable root s0 st).
  apply Hoare_bind with (Q := fun (_:unit) (s1:St) =>
    visited2 s1 u /\
    visited2 s0 ⊆ visited2 s1 /\
    (forall v, visited2 s1 v -> visited2 s0 v \/ u = v) /\
    scc_id s1 = scc_id s0 /\
    visited1 s1 = visited1 s0 /\
    finish s1 = finish s0 /\
    scc_next s1 = scc_next s0).
  - unfold Hoare. split.
    + intros s1 [] s2 Hs1 Hprog. rewrite Hs1 in Hprog.
      cbv beta iota delta [visit2 custom] in Hprog.
      destruct Hprog as [Hv2 [_ [Hfin [Hv1 [Hsid Hnext]]]]].
      repeat split.
      * pose proof Hv2 as Hv2_unfold. sets_unfold in Hv2_unfold.
        apply Hv2_unfold. right; reflexivity.
      * intros x Hx. pose proof Hv2 as Hv2_unfold. sets_unfold in Hv2_unfold.
        apply Hv2_unfold. left; exact Hx.
      * intros x Hx. pose proof Hv2 as Hv2_unfold. sets_unfold in Hv2_unfold.
        destruct (proj1 (Hv2_unfold x) Hx) as [Hx0 | Hxu];
          [left; exact Hx0 | right; exact Hxu].
      * exact Hsid.
      * exact Hv1.
      * exact Hfin.
      * exact Hnext.
    + intros s1 Hs1 Herr. exfalso. exact Herr.
  - intros []. apply Hoare_normalize.
    intros s1 [Hvis_u1 [Hv2_sub1 [Hv2_char1 [Hsid1 [Hv1_1 [Hfin1 Hnext1]]]]]].
    apply Hoare_bind with (Q := fun (_:unit) (s2:St) => P_loop ∅ s2).
    + apply Hoare_set_scc_id with (P := fun s2 => P_loop ∅ s2).
      intros s2 [Huid [Hother [_ [Hfin2 [Hv1_2 [Hv2_2 Hnext2]]]]]].
      unfold P_loop, DFSSccStable.
      repeat split.
      * rewrite Hv2_2. exact Hvis_u1.
      * intros x Hx. rewrite Hv2_2. apply Hv2_sub1. exact Hx.
      * intros x Hx.
        rewrite Hv2_2 in Hx.
        destruct (Hv2_char1 x Hx) as [Hx0 | Hxu].
        -- left; exact Hx0.
        -- subst x. right. unfold reachable. reflexivity.
      * destruct (classic (root = u)) as [Hru | Hru].
        -- subst root. reflexivity.
        -- rewrite Huid, (Hother root Hru). rewrite Hsid1. reflexivity.
      * intros x Hx Hxu. rewrite (Hother x Hxu), Hsid1. reflexivity.
      * destruct (classic (root = u)) as [Hru | Hru].
        -- subst root. rewrite Huid, Hsid1. reflexivity.
        -- rewrite (Hother root Hru), Hsid1. reflexivity.
      * rewrite Hv1_2, Hv1_1. reflexivity.
      * rewrite Hfin2, Hfin1. reflexivity.
      * rewrite Hnext2, Hnext1. reflexivity.
    + intros []. simpl.
      apply Hoare_repeat_break with
          (P := P_loop)
          (Q := fun (_:unit) st =>
            visited2 st u /\
            visited2 s0 ⊆ visited2 st /\
            (forall v, visited2 st v -> visited2 s0 v \/ reachable g u v) /\
            scc_id st u = scc_id st root /\
            (forall v, visited2 s0 v -> v <> u -> scc_id st v = scc_id s0 v) /\
            DFSSccStable root s0 st).
      intros e_set.
      apply Hoare_normalize.
      intros st [HPu [HPsub [HPreach [HPsid [HPold HPstable]]]]].
      apply Hoare_choice.
      * apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros Hnot_e.
        apply Hoare_normal_assume_bind; intros Hnot_v.
        apply Hoare_normal_assume_bind; intros Hstep.
        apply Hoare_bind with
          (Q := fun (_:unit) s3 =>
            visited2 s3 v /\
            visited2 st ⊆ visited2 s3 /\
            (forall x, visited2 s3 x -> visited2 st x \/ reachable g v x) /\
            scc_id s3 v = scc_id s3 root /\
            (forall x, visited2 st x -> x <> v -> scc_id s3 x = scc_id st x) /\
            DFSSccStable root st s3).
        { exact (IH st v). }
        { intros []. apply Hoare_ret.
          intros s3 [Hchild_v [Hchild_sub [Hchild_reach [Hchild_sid [Hchild_old Hchild_stable]]]]].
          destruct Hchild_stable as [Hroot_eq [Hv1_eq [Hfin_eq Hnext_eq]]].
          unfold P_loop, DFSSccStable in *.
          repeat split.
          - apply Hchild_sub. exact HPu.
          - intros x Hx. apply Hchild_sub, HPsub; exact Hx.
          - intros x Hx.
            destruct (Hchild_reach x Hx) as [Hx_st | Hv_reach].
            + apply HPreach; exact Hx_st.
            + right.
              eapply step_reachable_reachable.
              -- unfold step. exists e. exact Hstep.
              -- exact Hv_reach.
          - rewrite (Hchild_old u HPu).
            + rewrite Hroot_eq. exact HPsid.
            + intro Huv; subst v. exact (Hnot_v HPu).
          - intros x Hx0 Hxu.
            rewrite (Hchild_old x).
            + apply HPold; assumption.
            + apply HPsub; exact Hx0.
            + intro Hxv. subst v. apply Hnot_v, HPsub; exact Hx0.
          - rewrite Hroot_eq. destruct HPstable as [H _]. exact H.
          - rewrite Hv1_eq. destruct HPstable as [_ [H _]]. exact H.
          - rewrite Hfin_eq. destruct HPstable as [_ [_ [H _]]]. exact H.
          - rewrite Hnext_eq. destruct HPstable as [_ [_ [_ H]]]. exact H. }
      * apply Hoare_normal_assume_bind; intros Hall.
        apply Hoare_assertS_bind.
        { intros st' Hst'. subst st'. exact HPsid. }
        { apply Hoare_ret.
          intros st' Hst'. subst st'.
          exact (conj HPu (conj HPsub (conj HPreach (conj HPsid (conj HPold HPstable))))). }
Qed.

(** [DFS_scc_reachable_from_u]
    Fixed-point version: after DFS_scc root u, newly visited2 vertices are
    reachable from u in the original graph.
    Proved property: forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v *)
Lemma DFS_scc_reachable_from_u : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v).
Proof.
  intros s0 root u.
  unfold DFS_scc.
  eapply Hoare_imp_post.
  - apply Hoare_normal_LFix with
      (Q := fun u' s0' _ s' =>
        visited2 s' u' /\
        visited2 s0' ⊆ visited2 s' /\
        (forall v, visited2 s' v -> visited2 s0' v \/ reachable g u' v) /\
        scc_id s' u' = scc_id s' root /\
        (forall v, visited2 s0' v -> v <> u' -> scc_id s' v = scc_id s0' v) /\
        DFSSccStable root s0' s').
    intros W IH s0' u'.
    apply DFS_scc_reachable_aux.
    exact IH.
  - intros _ s' [_ [_ [Hreach _]]]. exact Hreach.
Qed.

(** [DFS_scc_reachable]
    If root is reachable from root -> u, then DFS_scc root u ensures every
    newly visited2 vertex is reachable from root.
    Proved property: forall v, visited2 s' v -> ~visited2 s0 v -> reachable g root v *)
Lemma DFS_scc_reachable : forall s0 root u,
  reachable g root u ->
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    forall v, visited2 s' v -> ~visited2 s0 v -> reachable g root v).
Proof.
  intros s0 root u Hreach.
  eapply Hoare_imp_post.
  - apply DFS_scc_reachable_from_u.
  - intros junk st H v Hvis_v Hnew.
    destruct (H v Hvis_v) as [H_old | H_reach_u].
    { exfalso; exact (Hnew H_old). }
    { etransitivity; eauto. }
Qed.

(** [DFS_scc_preserves_ForwardReachClosed]
    DFS_scc root u preserves the ForwardReachClosed invariant
    (visited2 is closed under forward reachability g),
    provided u was not already visited2.
    Proved property: ForwardReachClosed s' *)
Lemma DFS_scc_preserves_ForwardReachClosed : forall s0 root u,
  ~ visited2 s0 u ->
  ForwardReachClosed s0 ->
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => ForwardReachClosed s').
Proof.
  intros s0 root u Hnot_vis Hclosed.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_strong.
  - intros _ s' [Hvis_u [Hsub Hneigh]].
    unfold ForwardReachClosed.
    intros v w0 Hvis_v Hreach.
    destruct (classic (visited2 s0 v)) as [Hv_s0 | Hv_not].
    + apply Hsub.
      exact (Hclosed v w0 Hv_s0 Hreach).
    + destruct (Hneigh v Hvis_v) as [Hv_s0' | Hn_v]; [exfalso; exact (Hv_not Hv_s0') |].
      apply reachable_to_reach_fwd in Hreach.
      induction Hreach as [| z w0' Hrest IH Hstep].
      * exact Hvis_v.
      * destruct (Hneigh z IH) as [Hz_s0 | Hn_z].
        -- apply Hsub.
           exact (Hclosed z w0' Hz_s0 (step_rt g z w0' Hstep)).
        -- exact (Hn_z w0' Hstep).
Qed.

(** [DFS_scc_reachable_visited_closed]
    Under ForwardReachClosed s0, DFS_scc root u visits every vertex
    reachable from u that was not already in visited2 s0.
    The closure condition ensures that the path from u to v contains
    no s0-vertex, so the DFS guard never blocks.
    Proved property: forall v, reachable g u v -> ~visited2 s0 v -> visited2 s' v *)
Lemma DFS_scc_reachable_visited_closed : forall s0 root u,
  ForwardReachClosed s0 ->
  ~ visited2 s0 u ->
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    forall v, reachable g u v -> ~ visited2 s0 v -> visited2 s' v).
Proof.
  intros s0 root u Hclosed Hnot_u.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_strong.
  - intros _ s' [Hvis_u [Hsub Hneigh]].
    intros v Hreach_v Hnot_v.
    apply reachable_to_reach_fwd in Hreach_v.
    induction Hreach_v as [| z v' Hrest IH Hstep].
    + exact Hvis_u.
    + assert (Hnot_z : ~ visited2 s0 z).
      { intro Hz_s0.
        apply Hnot_v.
        apply (Hclosed z v' Hz_s0).
        apply step_rt; exact Hstep. }
      specialize (IH Hnot_z).
      (* IH : visited2 s' z *)
      destruct (Hneigh z IH) as [Hz_s0 | Hn_z].
      { exfalso; exact (Hnot_z Hz_s0). }
      { exact (Hn_z v' Hstep). }
Qed.

(** [mutually_reachable_from_order]
    Pure logic: if root can reach v, both are visited1, root has max finish
    among vertices not yet visited2, and v is not yet visited2, then
    root and v are mutually reachable.
    Proof: Phase1_Order gives exist c mutually-reachable v c with
    finish root < finish c; ForwardReachClosed + ~visited2 v forces
    ~visited2 c, then max-finish contradicts the strict inequality.
    Therefore reachable_rev root v must hold, giving mutually_reachable. *)
Lemma mutually_reachable_from_order : forall s root v,
  Phase1_Order s ->
  ForwardReachClosed s ->
  reachable g root v ->
  (forall w, ~ visited2 s w -> finish s root >= finish s w) ->
  ~ visited2 s v ->
  mutually_reachable root v.
Proof.
  intros s root v Hphase Hclosed Hreach Hmax Hnot2.
  apply reachable_iff_reachable_rev in Hreach.
  destruct (classic (reachable_rev root v)) as [Hrev | Hnot_rev].
  - apply reachable_iff_reachable_rev in Hreach.
    apply reachable_iff_reachable_rev in Hrev.
    split; assumption.
  - destruct (Hphase v root Hreach Hnot_rev) as (c & Hmut & Hfin_lt).
    destruct Hmut as (Hv2c & Hc2v).
    assert (Hnot_c : ~ visited2 s c) by
      (intro Hc; apply Hnot2; apply (Hclosed c v Hc Hc2v)).
    specialize (Hmax c Hnot_c); lia.
Qed.

(** [DFS_scc_mutually_reachable_root]
    Under ForwardReachClosed, OrderInv, all-visited1, and max-finish,
    every vertex newly visited2 by DFS_scc root root is mutually reachable
    with root.
    Proved property: forall v, visited2 s' v -> ~visited2 s0 v -> mutually_reachable root v *)
Lemma DFS_scc_mutually_reachable_root : forall s0 root,
  ForwardReachClosed s0 ->
  Phase1_Order s0 ->
  ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (DFS_scc root root) (fun _ s' =>
    forall v, visited2 s' v -> ~ visited2 s0 v -> mutually_reachable root v).
Proof.
  intros s0 root Hclosed Hphase Hnot2_r Hmax.
  eapply Hoare_imp_post.
  - apply DFS_scc_reachable_from_u.
  - intros a s' Hreachable.
    intros x Hvis_x Hnew.
    destruct (Hreachable x Hvis_x) as [Hx_s0 | Hreach_x].
    + exfalso; exact (Hnew Hx_s0).
    + exact (mutually_reachable_from_order s0 root x
        Hphase Hclosed Hreach_x Hmax Hnew).
Qed.

(** [DFS_scc_visits_scc]
    Under ForwardReachClosed and max-finish, DFS_scc root root visits
    every vertex mutually reachable with root that is not already visited2.
    Proof: mutual → reachable, then DFS_scc_reachable_visited_closed.
    Proved property: forall v, mutually_reachable root v -> ~visited2 s0 v -> visited2 s' v *)
Lemma DFS_scc_visits_scc : forall s0 root,
  ForwardReachClosed s0 ->
  ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (DFS_scc root root) (fun _ s' =>
    forall v, mutually_reachable root v -> ~ visited2 s0 v -> visited2 s' v).
Proof.
  intros s0 root Hclosed Hnot2_r Hmax.
  eapply Hoare_imp_post.
  - apply (DFS_scc_reachable_visited_closed s0 root root Hclosed Hnot2_r).
  - intros a s' Hreach_closed.
    intros x Hmut Hnew.
    apply Hreach_closed.
    + destruct Hmut; assumption.
    + exact Hnew.
Qed.

(* Every new vertex gets the same scc_id as root.
   Together with scc_next counter uniqueness, this gives:
   same scc_id → same SCC iteration → mutually reachable. *)
(** [DFS_scc_same_root_id]
    All newly visited2 vertices get the same scc_id as root,
    and scc_id of already-visited vertices is preserved. *)
Lemma DFS_scc_same_root_id : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    (forall v, visited2 s' v -> ~visited2 s0 v -> scc_id s' v = scc_id s' root) /\
    (forall v, visited2 s0 v -> v <> u -> scc_id s' v = scc_id s0 v) /\
    scc_id s' root = scc_id s0 root /\
    visited2 s0 ⊆ visited2 s').
Proof.
  intros s0 root u.
  unfold DFS_scc.
  set (Q := fun (u': V) (s0': St) (_ : unit) (s' : St) =>
    (forall v, visited2 s' v -> ~visited2 s0' v -> scc_id s' v = scc_id s' root) /\
    (forall v, visited2 s0' v -> v <> u' -> scc_id s' v = scc_id s0' v) /\
    scc_id s' root = scc_id s0' root /\
    visited2 s0' ⊆ visited2 s').
  apply Hoare_normal_LFix with (Q := Q).
    intros W IH s0' u'.
    unfold Q; simpl.
    unfold DFS_scc_f.
    set (P_loop := fun (e_set: E -> Prop) (st: St) =>
      (forall v, visited2 st v -> ~visited2 s0' v -> scc_id st v = scc_id st root) /\
      (forall v, visited2 s0' v -> v <> u' -> scc_id st v = scc_id s0' v) /\
      scc_id st root = scc_id s0' root /\
      visited2 s0' ⊆ visited2 st /\
      scc_id st u' = scc_id st root /\
      visited2 st u').
    apply Hoare_bind with (Q := fun (_:unit) (s':St) =>
      visited2 s' u' /\ visited2 s' == visited2 s0' ∪ Sets.singleton u' /\ scc_id s' = scc_id s0').
    + unfold Hoare. split.
      - intros s1 a s2 Hs1 Hprog.
        rewrite Hs1 in *.
        cbv beta iota delta [visit2 custom] in Hprog.
        destruct Hprog as [Hv [_ [_ [_ [Hsid _]]]]].
        split.
        * pose proof Hv as Hv_unfold.
          sets_unfold in Hv_unfold.
          apply (Hv_unfold u'). right; reflexivity.
        * split; [exact Hv | exact Hsid].
      - intros s1 Hs1 Herr. exfalso. exact Herr.
    + intros junk. apply Hoare_normalize.
      intros s2 [Hvis_u2 [Hv_char2 Hscc_eq]].
      eapply Hoare_bind.
      * apply Hoare_set_scc_id with (P := fun s' => P_loop ∅ s').
        intros s' [Hscc [Hother [_ [_ [_ [Hv2 _]]]]]].
        unfold P_loop.
        repeat split.
        { intros v Hvis_v Hnew_v.
          rewrite Hv2 in Hvis_v. apply (Hv_char2 v) in Hvis_v.
          sets_unfold in Hvis_v.
          destruct Hvis_v as [Hv0 | Hv_eq].
          - exfalso; exact (Hnew_v Hv0).
          - subst v.
            destruct (classic (root = u')) as [Hr_eq | Hr_ne].
            + subst root. reflexivity.
            + rewrite (Hother root Hr_ne). apply Hscc. }
        { intros v Hv0 Hv_ne.
          rewrite (Hother v Hv_ne), Hscc_eq. reflexivity. }
        { destruct (classic (root = u')) as [Hr_eq | Hr_ne].
          - subst root. rewrite Hscc, Hscc_eq. reflexivity.
          - rewrite (Hother root Hr_ne), Hscc_eq. reflexivity. }
        { intros w Hw_s0. rewrite Hv2. apply (proj2 (Hv_char2 w)). left; exact Hw_s0. }
        { destruct (classic (root = u')) as [Hr_eq | Hr_ne].
          - subst root. reflexivity.
          - rewrite Hscc. rewrite (Hother root Hr_ne). reflexivity. }
        { rewrite Hv2. exact Hvis_u2. }
      * intro junk2. simpl.
        eapply Hoare_imp_post.
        { apply Hoare_repeat_break with
            (P := P_loop)
            (Q := fun (_ : unit) (s' : St) => P_loop ∅ s').
          intros e_set.
          apply Hoare_normalize.
          intros s1 [HP1 [HP2 [HP3 [HP4 [HPsid HPu]]]]].
          apply Hoare_choice.
        { apply Hoare_any_bind; intros e.
          apply Hoare_any_bind; intros v.
          apply Hoare_normal_assume_bind; intros H_not_e.
          apply Hoare_normal_assume_bind; intros H_not_vis.
          apply Hoare_normal_assume_bind; intros H_step.
          eapply Hoare_bind with (Q := Q v s1).
          - exact (IH s1 v).
          - intro junk3. simpl. apply Hoare_ret.
            intros s3 [Hnew_s3 [Hpres_s3 [Hroot_s3 Hsub3]]].
            unfold P_loop.
            repeat split.
            + intros w Hvis_w Hnew_w.
              destruct (classic (visited2 s1 w)) as [Hw_s1 | Hw_not_s1].
              * assert (Heq1 : scc_id s1 w = scc_id s1 root) by (apply HP1; auto).
                assert (Hw_ne_v : w <> v) by (intro Heq; subst w; exact (H_not_vis Hw_s1)).
                rewrite (Hpres_s3 w Hw_s1 Hw_ne_v).
                rewrite Hroot_s3. exact Heq1.
              * apply Hnew_s3; auto.
            + intros w Hw_s0 Hw_ne_u.
              assert (Heq2 : scc_id s1 w = scc_id s0' w) by (apply HP2; auto).
              assert (Hw_s1 : visited2 s1 w) by (apply HP4; exact Hw_s0).
              assert (Hw_ne_v : w <> v) by (intro Heq; subst w; exact (H_not_vis Hw_s1)).
              rewrite (Hpres_s3 w Hw_s1 Hw_ne_v). exact Heq2.
            + rewrite Hroot_s3, HP3. reflexivity.
            + intros w Hw_s0. apply Hsub3, HP4; exact Hw_s0.
            + assert (Hu'_ne_v : u' <> v) by (intro Heq; subst v; exact (H_not_vis HPu)).
              rewrite (Hpres_s3 u').
              * rewrite Hroot_s3. exact HPsid.
              * exact HPu.
              * exact Hu'_ne_v.
            + apply Hsub3. exact HPu. }
        { apply Hoare_normal_assume_bind; intros Hall.
          apply (proj2 (Hoare_assertS_bind _ _ _ _
            (fun st Hst => eq_ind_r (fun st0 => scc_id st0 u' = scc_id st0 root) HPsid Hst))).
          apply Hoare_ret.
          intros s' Hs'. subst s'. simpl.
          exact (conj HP1 (conj HP2 (conj HP3 (conj HP4 (conj HPsid HPu))))). } }
        { intros _ s' [HP1 [HP2 [HP3 [HP4 _]]]].
          exact (conj HP1 (conj HP2 (conj HP3 HP4))). }
Qed.

(** [mutually_reachable_unvisited2]
    If root has max finish among unvisited vertices and is itself unvisited,
    then any vertex mutually reachable with root is also unvisited.
    Proof: if v were visited2 and reachable back to root, ForwardReachClosed
    would force root ∈ visited2, contradiction. *)
Lemma mutually_reachable_unvisited2 : forall s root v,
  ForwardReachClosed s ->
  ~ visited2 s root ->
  mutually_reachable root v ->
  ~ visited2 s v.
Proof.
  intros s root v Hclosed Hnot_r [Hr2v Hv2r] Hv.
  apply Hnot_r, (Hclosed v root Hv Hv2r).
Qed.

(** [DFS_scc_new_mutually_reachable]
    All vertices newly visited by DFS_scc root root are mutually reachable
    with each other.  Follows from DFS_scc_mutually_reachable_root
    (new → mutually reachable with root) and mutually_reachable_trans/sym.
    Proved property: forall u v, visited2 s' u -> visited2 s' v ->
      ~visited2 s0 u -> ~visited2 s0 v -> mutually_reachable u v *)
Lemma DFS_scc_new_mutually_reachable : forall s0 root,
  ForwardReachClosed s0 ->
  Phase1_Order s0 ->
  ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (DFS_scc root root) (fun _ s' =>
    forall u v, visited2 s' u -> visited2 s' v ->
      ~ visited2 s0 u -> ~ visited2 s0 v ->
      mutually_reachable u v).
Proof.
  intros s0 root Hclosed Hphase Hnot2 Hmax.
  eapply Hoare_imp_post.
  - apply (DFS_scc_mutually_reachable_root s0 root Hclosed Hphase Hnot2 Hmax).
  - intros a s' Hmut_root.
    intros u v Hvis_u Hvis_v Hnew_u Hnew_v.
    apply Hmut_root in Hvis_u; auto.
    apply Hmut_root in Hvis_v; auto.
    apply mutually_reachable_sym in Hvis_u.
    apply mutually_reachable_trans with (v := root); assumption.
Qed.

(** The invariant R(s) maintained by kosaraju_scc:
    - ForwardReachClosed: no forward edge crosses visited2 boundary
    - Phase1_Order: condensation-DAG finish ordering (immutable in Phase 2)
    - visited1-all: every vertex has been visited1 (immutable)
    - scc_id < scc_next: visited2 scc_ids from past rounds
    - correctness: scc_id equality iff mutually reachable within visited2 *)
Definition R (s : St) : Prop :=
  ForwardReachClosed s /\
  Phase1_Order s /\
  (forall v, visited1 s v) /\
  (forall v, visited2 s v -> scc_id s v < scc_next s) /\
  (forall u v, visited2 s u -> visited2 s v ->
    (scc_id s u = scc_id s v <-> mutually_reachable u v)).

Lemma set_scc_root_id_R : forall s0 root,
  R s0 -> ~ visited2 s0 root ->
  Hoare (fun st => st = s0) (set_scc_root_id root) (fun _ s1 =>
    visited2 s1 = visited2 s0 /\ visited1 s1 = visited1 s0 /\ finish s1 = finish s0 /\
    R s1 /\ scc_id s1 root = scc_next s0 /\ scc_next s1 = S (scc_next s0) /\
    (forall v, v <> root -> scc_id s1 v = scc_id s0 v)).
Proof.
  intros s0 root [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]] Hnot_root.
  apply Hoare_set_scc_root_id with (P := fun s1 =>
    visited2 s1 = visited2 s0 /\ visited1 s1 = visited1 s0 /\ finish s1 = finish s0 /\
    R s1 /\ scc_id s1 root = scc_next s0 /\ scc_next s1 = S (scc_next s0) /\
    (forall v, v <> root -> scc_id s1 v = scc_id s0 v)).
  intros s1 [Hroot_id [Hscc_next [Hother [Htimer [Hfin [Hv1 Hv2]]]]]].
  assert (HR1 : R s1). {
    unfold R; split; [| split; [| split; [| split]]].
    { intros u v Hvis Hreach. rewrite Hv2 in Hvis.
      specialize (Hclosed u v Hvis Hreach). rewrite Hv2; exact Hclosed. }
    { intros a b Hrev Hnot. destruct (Hphase a b Hrev Hnot) as [c [Hmut Hfin_lt]].
      exists c; split; [exact Hmut | rewrite Hfin; exact Hfin_lt]. }
    { intros v. rewrite Hv1. apply Hvis1. }
    { intros v Hvis. rewrite Hv2 in Hvis.
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst v. exfalso; apply Hnot_root; exact Hvis.
      - rewrite (Hother v Hv_ne). apply Hscclt in Hvis; rewrite Hscc_next; lia. }
    { intros u v Hvis_u Hvis_v. rewrite Hv2 in Hvis_u, Hvis_v.
      destruct (classic (u = root)) as [Hu_eq | Hu_ne];
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst u v. exfalso; apply Hnot_root; exact Hvis_u.
      - subst u. exfalso; apply Hnot_root; exact Hvis_u.
      - subst v. exfalso; apply Hnot_root; exact Hvis_v.
      - rewrite (Hother u Hu_ne), (Hother v Hv_ne). apply Hcorrect; assumption. } }
  exact (conj Hv2 (conj Hv1 (conj Hfin (conj HR1 (conj Hroot_id (conj Hscc_next Hother)))))).
Qed.

Lemma visit2_preserves_scc_next : forall s0 u,
  Hoare (fun st => st = s0) (visit2 u) (fun _ s' => scc_next s' = scc_next s0).
Proof.
  intros s0 u. unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [visit2 custom] in Hprog.
    destruct Hprog as [_ [_ [_ [_ [_ Hscc]]]]]. exact Hscc.
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

Lemma set_scc_id_preserves_scc_next : forall s0 u root0,
  Hoare (fun st => st = s0) (set_scc_id u root0) (fun _ s' => scc_next s' = scc_next s0).
Proof.
  intros s0 u root0. unfold Hoare. split.
  - intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    cbv beta iota delta [set_scc_id custom] in Hprog.
    destruct Hprog as [_ [_ [_ [_ [_ [_ Hscc]]]]]]. exact Hscc.
  - intros s1 Hs1 Herr. exfalso. exact Herr.
Qed.

Lemma DFS_scc_preserves_scc_next : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => scc_next s' = scc_next s0).
Proof.
  intros s0 root u.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_stable.
  - intros _ s' [_ [_ [_ [_ [_ [_ Hnext]]]]]].
    exact Hnext.
Qed.

Lemma DFS_scc_preserves_visited1 : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => visited1 s' = visited1 s0).
Proof.
  intros s0 root u.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_stable.
  - intros _ s' [_ [_ [_ [_ [Hv1 _]]]]].
    exact Hv1.
Qed.

Lemma DFS_scc_preserves_finish : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => finish s' = finish s0).
Proof.
  intros s0 root u.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_stable.
  - intros _ s' [_ [_ [_ [_ [_ [Hfinish _]]]]]].
    exact Hfinish.
Qed.

Lemma DFS_scc_R : forall s1 root,
  R s1 -> ~ visited2 s1 root ->
  (forall w, ~ visited2 s1 w -> finish s1 root >= finish s1 w) ->
  (forall v, visited2 s1 v -> scc_id s1 v < scc_id s1 root) ->
  scc_id s1 root < scc_next s1 ->
  Hoare (fun st => st = s1) (DFS_scc root root) (fun _ s' => R s').
Proof.
  intros s1 root [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]] Hnot_root Hmax Hlt_root Hroot_lt.
  eapply Hoare_imp_post.
  - apply Hoare_conj.
    + apply (DFS_scc_preserves_ForwardReachClosed s1 root root Hnot_root Hclosed).
    + apply Hoare_conj.
      * apply (DFS_scc_mutually_reachable_root s1 root Hclosed Hphase Hnot_root Hmax).
      * apply Hoare_conj with
          (Q1 := fun _ s' =>
            (forall v, visited2 s' v -> ~visited2 s1 v -> scc_id s' v = scc_id s' root) /\
            (forall v, visited2 s1 v -> v <> root -> scc_id s' v = scc_id s1 v) /\
            scc_id s' root = scc_id s1 root /\
            visited2 s1 ⊆ visited2 s')
          (Q2 := fun _ s' => visited1 s' = visited1 s1 /\ finish s' = finish s1 /\ scc_next s' = scc_next s1).
        -- apply (DFS_scc_same_root_id s1 root root).
        -- apply Hoare_conj.
           ++ apply (DFS_scc_preserves_visited1 s1 root root).
           ++ apply Hoare_conj.
              ** apply (DFS_scc_preserves_finish s1 root root).
              ** apply (DFS_scc_preserves_scc_next s1 root root).
  - intro a0. intro s'. simpl. intro Hpost.
    destruct Hpost as [Hclosed2 [Hmut_root [Hsame4 [Hv1_eq [Hfin_eq Hscc_next_eq]]]]].
    destruct Hsame4 as [Hsame_id [Hpres_id [Hroot_id2 Hsub2]]].
    unfold R; split; [| split; [| split; [| split]]].
    { exact Hclosed2. }
    { intros a b Hrev Hnot. destruct (Hphase a b Hrev Hnot) as [c [Hmut Hfin_lt]].
      exists c; split; [exact Hmut | rewrite Hfin_eq; exact Hfin_lt]. }
    { intro x. rewrite Hv1_eq. apply Hvis1. }
    { intros x Hvis.
      destruct (classic (visited2 s1 x)) as [Hv_s1 | Hv_new].
      - assert (Hx_ne_root : x <> root). { intro Heq; subst x. apply Hnot_root; exact Hv_s1. }
        pose proof (Hpres_id x Hv_s1 Hx_ne_root) as Heq_id.
        rewrite Heq_id. rewrite Hscc_next_eq. apply Hscclt; exact Hv_s1.
      - pose proof (Hsame_id x Hvis Hv_new) as Heq_root.
        rewrite Heq_root, Hroot_id2. rewrite Hscc_next_eq. apply Hroot_lt. }
    { intros u v Hvis_u Hvis_v.
      destruct (classic (visited2 s1 u)) as [Hu_s1 | Hu_new];
      destruct (classic (visited2 s1 v)) as [Hv_s1 | Hv_new].
      - assert (Hu_ne_root : u <> root). { intro Heq; subst u. apply Hnot_root; exact Hu_s1. }
        assert (Hv_ne_root : v <> root). { intro Heq; subst v. apply Hnot_root; exact Hv_s1. }
        rewrite (Hpres_id u Hu_s1 Hu_ne_root), (Hpres_id v Hv_s1 Hv_ne_root).
        apply Hcorrect; assumption.
      - assert (Hu_ne_root : u <> root). { intro Heq; subst u. apply Hnot_root; exact Hu_s1. }
        pose proof (Hsame_id v Hvis_v Hv_new) as Heq_v.
        rewrite (Hpres_id u Hu_s1 Hu_ne_root), Heq_v. split.
        + intro Heq. exfalso. pose proof (Hlt_root u Hu_s1) as Htemp.
          assert (Heq' : scc_id s1 u = scc_id s1 root). { transitivity (scc_id s' root); [| assumption]. apply Heq. }
          rewrite Heq' in Htemp. lia.
        + intros [Hreach _]. exfalso. apply Hv_new. apply (Hclosed u v Hu_s1 Hreach).
      - assert (Hv_ne_root : v <> root). { intro Heq; subst v. apply Hnot_root; exact Hv_s1. }
        pose proof (Hsame_id u Hvis_u Hu_new) as Heq_u.
        rewrite (Hpres_id v Hv_s1 Hv_ne_root), Heq_u. split.
        + intro Heq. exfalso. pose proof (Hlt_root v Hv_s1) as Htemp.
          assert (Heq' : scc_id s1 v = scc_id s1 root). { transitivity (scc_id s' root); [| assumption]. symmetry; assumption. }
          rewrite Heq' in Htemp. lia.
        + intros [_ Hreach]. exfalso. apply Hu_new. apply (Hclosed v u Hv_s1 Hreach).
      - pose proof (Hmut_root u Hvis_u Hu_new) as Hmut_u.
        pose proof (Hmut_root v Hvis_v Hv_new) as Hmut_v.
        pose proof (Hsame_id u Hvis_u Hu_new) as Heq_u.
        pose proof (Hsame_id v Hvis_v Hv_new) as Heq_v. 
        rewrite Heq_u, Heq_v. split.
        + intros _. apply mutually_reachable_sym in Hmut_u.
          apply mutually_reachable_trans with (v := root); assumption.
        + intros Hmut. reflexivity. } 
Qed.

Lemma DFS_scc_phase2_post_state : forall s1 root,
  R s1 -> ~ visited2 s1 root ->
  (forall w, ~ visited2 s1 w -> finish s1 root >= finish s1 w) ->
  (forall v, visited2 s1 v -> scc_id s1 v < scc_id s1 root) ->
  scc_id s1 root < scc_next s1 ->
  Hoare (fun st => st = s1) (DFS_scc root root) (fun _ s' =>
    R s' /\
    (forall v, visited2 s' v -> ~ visited2 s1 v -> mutually_reachable root v) /\
    (forall v, mutually_reachable root v -> visited2 s' v) /\
    (forall v, visited2 s' v -> ~ visited2 s1 v ->
      scc_id s' v = scc_id s' root) /\
    (forall v, visited2 s1 v -> v <> root -> scc_id s' v = scc_id s1 v) /\
    visited2 s1 ⊆ visited2 s' /\
    scc_id s' root = scc_id s1 root).
Proof.
  intros s1 root HR Hnot_root Hmax Hlt_root Hroot_lt.
  destruct HR as [Hclosed [Hphase [Hall1 [Hscclt Hcorrect]]]].
  eapply Hoare_imp_post.
  - apply Hoare_conj with
      (Q1 := fun _ s' => R s')
      (Q2 := fun _ s' =>
        (forall v, visited2 s' v -> ~ visited2 s1 v -> mutually_reachable root v) /\
        (forall v, mutually_reachable root v -> ~ visited2 s1 v -> visited2 s' v) /\
        ((forall v, visited2 s' v -> ~ visited2 s1 v ->
            scc_id s' v = scc_id s' root) /\
         (forall v, visited2 s1 v -> v <> root -> scc_id s' v = scc_id s1 v) /\
         scc_id s' root = scc_id s1 root /\
         visited2 s1 ⊆ visited2 s')).
    + apply (DFS_scc_R s1 root
        (conj Hclosed (conj Hphase (conj Hall1 (conj Hscclt Hcorrect))))
        Hnot_root Hmax Hlt_root Hroot_lt).
    + apply Hoare_conj.
      * apply (DFS_scc_mutually_reachable_root s1 root
          Hclosed Hphase Hnot_root Hmax).
      * apply Hoare_conj.
        -- apply (DFS_scc_visits_scc s1 root
             Hclosed Hnot_root Hmax).
        -- apply DFS_scc_same_root_id.
  - intros _ s' [HR' [Hnew_mut [Hvisit_new [Hsame [Hpres [Hroot_id Hsub]]]]]].
    split; [ exact HR' | ].
    split; [ exact Hnew_mut | ].
    split.
    + intros v Hmut.
      destruct (classic (visited2 s1 v)) as [Hv_old | Hv_new].
      * sets_unfold in Hsub. apply Hsub. exact Hv_old.
      * apply Hvisit_new; assumption.
    + split; [ exact Hsame | ].
      split; [ exact Hpres | ].
      split.
      * exact Hsub.
      * exact Hroot_id.
Qed.

(* ================================================================= *)
(* 5. Outer Phase 2 — kosaraju_scc                                    *)
(* ================================================================= *)

(** [kosaraju_scc_all_visited_aux]
    Helper: one iteration of kosaraju_scc_f visits all vertices in visited2.
    Proved property: forall v, visited2 s' v *)
Lemma kosaraju_scc_all_visited_aux : forall W,
  (forall s0, Hoare (fun st => st = s0) (W tt) (fun _ s' => forall v, visited2 s' v)) ->
  (forall s0, Hoare (fun st => st = s0) (kosaraju_scc_f W tt) (fun _ s' => forall v, visited2 s' v)).
Proof.
  intros W IH s0.
  unfold kosaraju_scc_f.
  apply Hoare_choice.
  { apply Hoare_bind with (Q := fun (u:V) (s':St) => s' = s0 /\ ~ visited2 s' u).
    { unfold Hoare. split.
      - intros s1 a s2 Hs1 Hprog.
        rewrite Hs1 in *.
        cbv beta iota delta [pick_unvisited2 MonadErr.nrm_nrm get] in Hprog.
        destruct Hprog as [[_ [Hnot_vis _]] Hsame].
        rewrite Hsame in Hnot_vis.
        split; [symmetry; exact Hsame | exact Hnot_vis].
      - intros s1 Hs1 Herr. exfalso.
        cbv beta iota delta [pick_unvisited2 MonadErr.nrm_err get] in Herr.
        sets_unfold in Herr. firstorder. }
    { intro u.
      apply Hoare_normalize.
      intros s1 [Hs1_eq Hunvis].
      rewrite Hs1_eq.
      simpl.
      eapply Hoare_bind with (Q := fun (_:unit) (s':St) => True).
      { apply Hoare_set_scc_root_id with (P := fun _ => True).
        intros s' _. exact I. }
      { intro junk. apply Hoare_normalize; intros s2 Htrue.
        apply Hoare_bind with (Q := fun (_:unit) (s':St) => visited2 s' u).
        { eapply Hoare_imp_post.
          { apply DFS_scc_neighbor_visited_strong. }
          { intros _ s' [Hvis_u _]; exact Hvis_u. } }
        { intro a; apply Hoare_normalize; intros s3 _; apply (IH s3). } } } }
  { apply Hoare_normal_assume_bind; intros Hall.
    apply Hoare_ret.
    intros s1 Hs1. subst s1. exact Hall. }
Qed.

(** [kosaraju_scc_all_visited]
    After the full kosaraju_scc, all vertices are visited2.
    Proved property: forall v, visited2 s' v *)
Lemma kosaraju_scc_all_visited : forall s0,
  Hoare (fun st => st = s0) kosaraju_scc (fun _ s' => forall v, visited2 s' v).
Proof.
  intros s0.
  unfold kosaraju_scc.
  apply Hoare_normal_LFix with (Q := fun (_:unit) (s0':St) (_:unit) (s':St) => forall v, visited2 s' v).
  intros W IH s0' u.
  apply kosaraju_scc_all_visited_aux.
  intro s0''; apply (IH s0'' tt).
Qed.

(** [kosaraju_scc_preserves_ForwardReachClosed]
    The outer loop kosaraju_scc preserves ForwardReachClosed.
    Each round: set_scc_root_id touches neither visited2 nor visited1;
    DFS_scc preserves it (DFS_scc_preserves_ForwardReachClosed).
    Proved property: ForwardReachClosed s' *)
Lemma kosaraju_scc_preserves_ForwardReachClosed : forall s0,
  ForwardReachClosed s0 ->
  Hoare (fun st => st = s0) kosaraju_scc (fun _ s' => ForwardReachClosed s').
Proof.
  intros s0 Hclosed.
  unfold kosaraju_scc.
  apply Hoare_normal_LFix_closed with
    (R := ForwardReachClosed)
    (Q := fun (_:unit) (_:St) (_:unit) (s':St) => ForwardReachClosed s').
  { intros W IH s0' u0 Hclosed'.
    unfold kosaraju_scc_f.
    apply Hoare_choice.
    { (* recursive branch: pick root -> set_scc_root_id -> DFS_scc -> W *)
      apply Hoare_bind with (Q := fun (u:V) (s':St) => s' = s0' /\ ~ visited2 s' u).
      { unfold Hoare. split.
        - intros s1 a s2 Hs1 Hprog.
          rewrite Hs1 in *.
          cbv beta iota delta [pick_unvisited2 MonadErr.nrm_nrm get] in Hprog.
          destruct Hprog as [[_ [Hnot_vis _]] Hsame].
          rewrite Hsame in Hnot_vis.
          split; [symmetry; exact Hsame | exact Hnot_vis].
        - intros s1 Hs1 Herr. exfalso.
          cbv beta iota delta [pick_unvisited2 MonadErr.nrm_err get] in Herr.
          sets_unfold in Herr. firstorder. }
      { intro root.
        apply Hoare_normalize.
        intros s1 [Hs1_eq Hunvis]; subst s1.
        eapply Hoare_bind with (Q := fun (_:unit) (s':St) => visited2 s' = visited2 s0' /\ scc_id s' root = scc_next s0' /\ scc_next s' = S (scc_next s0')).
        { apply Hoare_set_scc_root_id with (P := fun s' => visited2 s' = visited2 s0' /\ scc_id s' root = scc_next s0' /\ scc_next s' = S (scc_next s0')).
          intros s' [Hroot_id [Hscc_next [Hother [Htimer [Hfin [Hv1 Hv2]]]]]].
          repeat split; auto. }
        { intro junk. apply Hoare_normalize; intros s2 [Hv2_eq [Hroot_id Hscc_next]].
          assert (Hclosed2 : ForwardReachClosed s2). {
            unfold ForwardReachClosed in *.
            intros v w Hvis Hreach.
            rewrite Hv2_eq in Hvis.
            specialize (Hclosed' v w Hvis Hreach) as Hw.
            rewrite Hv2_eq; exact Hw.
          }
          eapply Hoare_bind with (Q := fun (_:unit) (s':St) => ForwardReachClosed s').
          { apply (DFS_scc_preserves_ForwardReachClosed s2 root root).
            - rewrite Hv2_eq; exact Hunvis.
            - exact Hclosed2. }
          { intro junk2. apply Hoare_normalize; intros s3 Hclosed3.
            exact (IH s3 tt Hclosed3). } } } }
    { (* non-recursive branch: all visited, skip *)
      apply Hoare_normal_assume_bind with
        (P := fun st => forall v, visited2 st v)
        (f := skip)
        (Q := fun (_:unit) (s':St) => ForwardReachClosed s')
        (s0 := s0').
      intros Hall.
      apply Hoare_ret; intros s Hs; subst s; exact Hclosed'. } }
  { exact Hclosed. }
Qed.

Lemma round_preserves_R : forall s0 root,
  R s0 -> ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (set_scc_root_id root ;; DFS_scc root root) (fun _ s' => R s').
Proof.
  intros s0 root HR Hnot_root Hmax.
  destruct HR as [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]].
  eapply Hoare_bind.
  - apply (set_scc_root_id_R s0 root (conj Hclosed (conj Hphase (conj Hvis1 (conj Hscclt Hcorrect)))) Hnot_root).
  - intro junk. apply Hoare_normalize.
    intros s1 [Hv2_eq [Hv1_eq [Hfin_eq [HR1 [Hroot_id [Hscc_next Hother]]]]]].
    assert (Hnot_root' : ~ visited2 s1 root). { rewrite Hv2_eq; exact Hnot_root. }
    assert (Hmax' : forall w, ~ visited2 s1 w -> finish s1 root >= finish s1 w). {
      intros w Hw. rewrite Hv2_eq in Hw. rewrite Hfin_eq. apply Hmax; exact Hw. }
    assert (Hlt_root : forall v, visited2 s1 v -> scc_id s1 v < scc_id s1 root). {
      intros v Hv. rewrite Hv2_eq in Hv.
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst v. exfalso. apply Hnot_root. exact Hv.
      - rewrite (Hother v Hv_ne). rewrite Hroot_id. pose proof (Hscclt v Hv). lia. }
    assert (Hroot_lt : scc_id s1 root < scc_next s1). {
      rewrite Hroot_id, Hscc_next. abstract lia. }
    apply (DFS_scc_R s1 root HR1 Hnot_root' Hmax' Hlt_root Hroot_lt).
Qed.

Lemma round_W_R : forall s0' root (W : unit -> program St unit),
  R s0' -> ~ visited2 s0' root ->
  (forall w, ~ visited2 s0' w -> finish s0' root >= finish s0' w) ->
  (forall s, R s -> Hoare (fun st => st = s) (W tt) (fun _ s' => R s')) ->
  Hoare (fun st => st = s0') (set_scc_root_id root ;; (DFS_scc root root ;; W tt)) (fun _ s' => R s').
Proof.
  intros s0' root W HR' Hnot_root2 Hmax2 IHW.
  destruct HR' as [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]].
  eapply Hoare_bind.
  - apply (set_scc_root_id_R s0' root (conj Hclosed (conj Hphase (conj Hvis1 (conj Hscclt Hcorrect)))) Hnot_root2).
  - intro junk. apply Hoare_normalize.
    intros s1 [Hv2_eq [Hv1_eq [Hfin_eq [HR1 [Hroot_id [Hscc_next Hother]]]]]].
    assert (Hnot_root' : ~ visited2 s1 root). { rewrite Hv2_eq; exact Hnot_root2. }
    assert (Hmax' : forall w, ~ visited2 s1 w -> finish s1 root >= finish s1 w). {
      intros w Hw. rewrite Hv2_eq in Hw. rewrite Hfin_eq. apply Hmax2; exact Hw. }
    assert (Hlt_root : forall v, visited2 s1 v -> scc_id s1 v < scc_id s1 root). {
      intros v Hv. rewrite Hv2_eq in Hv.
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst v. exfalso. apply Hnot_root2. exact Hv.
      - rewrite (Hother v Hv_ne). rewrite Hroot_id. pose proof (Hscclt v Hv). lia. }
    assert (Hroot_lt : scc_id s1 root < scc_next s1). {
      rewrite Hroot_id, Hscc_next. abstract lia. }
    eapply Hoare_bind.
    * apply (DFS_scc_R s1 root HR1 Hnot_root' Hmax' Hlt_root Hroot_lt).
    * intro junk2. apply Hoare_normalize. intros s2 HR2. apply IHW; exact HR2.
Qed.

Lemma kosaraju_scc_preserves_R : forall s0,
  R s0 -> Hoare (fun st => st = s0) kosaraju_scc (fun _ s' => R s').
Proof.
  intros s0 HR0.
  unfold kosaraju_scc.
  set (Q := fun (_:unit) (_:St) (_:unit) (s':St) => R s').
  apply Hoare_normal_LFix_closed with (R := R) (Q := Q).
  { intros W IH s0' u0 HR'.
    unfold Q; simpl. unfold kosaraju_scc_f.
    apply Hoare_choice.
    { apply Hoare_bind with (Q := fun (u:V) (s':St) =>
        s' = s0' /\ ~ visited2 s' u /\
        (forall w, ~ visited2 s' w -> finish s' u >= finish s' w)).
      { unfold Hoare. split.
        - intros s1 a s2 Hs1 Hprog. rewrite Hs1 in *.
          cbv beta iota delta [pick_unvisited2 MonadErr.nrm_nrm get] in Hprog.
          destruct Hprog as [[_ [Hnot_vis Hmax2]] Hsame].
          rewrite Hsame in Hnot_vis, Hmax2.
          repeat split; [symmetry; exact Hsame | exact Hnot_vis | exact Hmax2].
        - intros s1 Hs1 Herr. exfalso.
          cbv beta iota delta [pick_unvisited2 MonadErr.nrm_err get] in Herr.
          sets_unfold in Herr. firstorder. }
      { intro root. apply Hoare_normalize.
        intros s1 [Hs1_eq [Hnot_root2 Hmax2]]; subst s1.
        apply (round_W_R s0' root W HR' Hnot_root2 Hmax2).
        intros s HRs. exact (IH s tt HRs). } }
    { apply Hoare_normal_assume_bind with
        (P := fun st => forall v, visited2 st v) (f := skip)
        (Q := fun (_:unit) (s':St) => R s') (s0 := s0').
      intros Hall. apply Hoare_ret; intros s Hs; subst s; exact HR'. } }
  { exact HR0. }
Qed.

Lemma DFS_finish_preserves_visited2 : forall s0 u,
  DFSFinishInv s0 ->
  ~ visited1 s0 u -> vvalid g u ->
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' => visited2 s' = visited2 s0).
Proof.
  intros s0 u Hinv Hnot Hvalid.
	  eapply Hoare_imp_post.
	  - eapply DFS_finish_fixpoint_ind_strong with
	      (Q := fun root _ _ st => visited1 st root);
	      try exact Hinv; try exact Hnot; try exact Hvalid.
	    intros W IH s1 v Hinv1 Hnot1 Hvalid1.
	    apply (DFS_finish_f_preserves_inv W IH s1 v Hinv1 Hnot1 Hvalid1).
  - intros r s' [Hframe _].
    destruct Hframe as [_ [_ [_ [Hv2 _]]]].
    exact Hv2.
Qed.

Lemma kosaraju_finish_preserves_visited2 : forall s0,
  DFSFinishInv s0 ->
  Hoare (fun st => st = s0) kosaraju_finish (fun _ s' => visited2 s' = visited2 s0).
Proof.
  intros s0 Hinv_s0. unfold kosaraju_finish.
  apply Hoare_normal_LFix_closed with
    (R := DFSFinishInv)
    (Q := fun (_:unit) (s0':St) (_:unit) (s':St) => visited2 s' = visited2 s0').
  + intros W IH s0' u Hinv_s0'. simpl.
    unfold kosaraju_finish_f.
    apply Hoare_choice.
    { apply Hoare_bind with (Q := fun (u0:V) (s':St) => s' = s0' /\ vvalid g u0 /\ ~ visited1 s' u0).
      { unfold Hoare. split.
        - intros s1 a s2 Hs1 Hprog. rewrite Hs1 in *.
          cbv beta iota delta [pick_unvisited1 MonadErr.nrm_nrm get] in Hprog.
          destruct Hprog as [[Hvv Hnot_vis] Hsame].
          rewrite Hsame in Hnot_vis.
          split; [symmetry; exact Hsame | split; [exact Hvv | exact Hnot_vis]].
        - intros s1 Hs1 Herr. exfalso.
          cbv beta iota delta [pick_unvisited1 MonadErr.nrm_err get] in Herr.
          sets_unfold in Herr. firstorder. }
      { intro u0. apply Hoare_normalize. intros s1 [Hs1_eq [Hvv Hunvis]]; subst s1.
        apply Hoare_bind with
          (Q := fun (_:unit) (s':St) => visited2 s' = visited2 s0' /\ DFSFinishInv s').
        - apply Hoare_conj.
          + apply (DFS_finish_preserves_visited2 s0' u0 Hinv_s0' Hunvis Hvv).
          + eapply Hoare_imp_post.
	            { eapply DFS_finish_fixpoint_ind_strong
	                with (Q := fun root _ _ st => visited1 st root);
	              try exact Hinv_s0'; try exact Hunvis; try exact Hvv.
	              intros W0 IH0 s00 u00 Hinv00 Hnot00 Hvalid00.
	              apply (DFS_finish_f_preserves_inv W0 IH0 s00 u00 Hinv00 Hnot00 Hvalid00). }
	            { intros _ s' [Hframe _]. exact (DFSFinishFrame_inv _ _ _ Hframe). }
        - intro junk.
          apply Hoare_normalize. intros s3 [Hv2_eq3 Hinv_s3].
          eapply Hoare_imp_post.
          { apply (IH s3 tt Hinv_s3). }
          { simpl. intros _ s' Hv2'. rewrite Hv2'. exact Hv2_eq3. } } }
    { apply Hoare_normal_assume_bind; intros _.
      apply Hoare_ret. intros s1 Hs1. subst s1. reflexivity. }
  + exact Hinv_s0.
Qed.

Lemma kosaraju_finish_R : Hoare (fun st => st = init_st) kosaraju_finish (fun _ s' => R s').
Proof.
  unfold R.
  eapply Hoare_imp_post.
  - apply Hoare_conj.
    + apply kosaraju_finish_phase1_order.
    + apply Hoare_conj.
      * apply (kosaraju_finish_visited_all init_st).
        apply DFSFinishInv_init.
      * apply (kosaraju_finish_preserves_visited2 init_st).
        apply DFSFinishInv_init.
  - simpl. intros _ s' [Hphase [Hvis1 Hv2_eq]].
    split; [| split; [| split; [| split]]].
    { intros u v Hvis _. rewrite Hv2_eq in Hvis. exfalso; exact Hvis. }
    { exact Hphase. }
    { exact Hvis1. }
    { intros v Hvis. rewrite Hv2_eq in Hvis. exfalso; exact Hvis. }
    { intros u v Hvis _. rewrite Hv2_eq in Hvis. exfalso; exact Hvis. }
Qed.

Lemma kosaraju_correct :
  Hoare (fun st => st = init_st) kosaraju
    (fun _ s' =>
       (forall v, visited2 s' v) /\
       (forall u v, scc_id s' u = scc_id s' v <-> mutually_reachable u v)).
Proof.
  unfold kosaraju.
  eapply Hoare_bind.
  - apply kosaraju_finish_R.
  - intro a. apply Hoare_normalize. intros s HR.
    eapply Hoare_imp_post.
    + apply Hoare_conj.
      * apply kosaraju_scc_all_visited.
      * apply (kosaraju_scc_preserves_R s HR).
    + simpl. intros _ s' [Hvisited2 HR'].
      destruct HR' as [_ [_ [_ [_ Hcorrect]]]].
      split; [exact Hvisited2 | exact (fun u v => Hcorrect u v (Hvisited2 u) (Hvisited2 v))].
Qed.

Lemma R_all_visited_correct : forall st,
  R st ->
  (forall v, visited2 st v) ->
  forall u v, scc_id st u = scc_id st v <-> mutually_reachable u v.
Proof.
  intros st HR Hall u v.
  destruct HR as [_ [_ [_ [_ Hcorrect]]]].
  apply Hcorrect; apply Hall.
Qed.

Definition AntiTopo (s : St) : Prop :=
  forall a b, visited2 s a -> visited2 s b ->
    reachable_rev a b -> ~reachable_rev b a ->
    scc_id s a < scc_id s b.

Lemma kosaraju_anti_topological :
  Hoare (fun st => st = init_st) kosaraju
    (fun _ s' =>
       (forall v, visited2 s' v) /\
       (forall u v, scc_id s' u = scc_id s' v <-> mutually_reachable u v) /\
       AntiTopo s').
Proof.
  unfold kosaraju.
  eapply Hoare_bind.
  - apply Hoare_conj.
    + apply kosaraju_finish_R.
    + apply (kosaraju_finish_preserves_visited2 init_st).
       apply DFSFinishInv_init.
  - intro junk. apply Hoare_normalize.
    intros s1 [HR Hv2_eq].
    assert (HAT0 : AntiTopo s1).
    { unfold AntiTopo. intros a b Ha. exfalso. revert Ha. rewrite Hv2_eq. cbn. auto. }
    eapply Hoare_imp_post.
    + apply Hoare_conj.
      * apply Hoare_conj.
        -- apply kosaraju_scc_all_visited.
        -- apply (kosaraju_scc_preserves_R s1 HR).
      * unfold kosaraju_scc.
        apply Hoare_normal_LFix_closed with
          (R := fun s => R s /\ AntiTopo s)
          (Q := fun _ _ _ s' => AntiTopo s').
        2: { exact (conj HR HAT0). }
        intros W IH s0' u0 [HR' HAT'].
        destruct HR' as [HFC [Hphase [Hvis1 [Hscclt Hcorrect]]]].
        unfold kosaraju_scc_f.
        apply Hoare_choice.
        { apply Hoare_bind with (Q := fun (u:V) (s':St) =>
            s' = s0' /\ ~visited2 s' u /\
            (forall w, ~visited2 s' w -> finish s' u >= finish s' w)).
          { unfold Hoare. split.
            - intros ss uu ss2 Hss Hprog. rewrite Hss in *.
              cbv beta iota delta [pick_unvisited2 MonadErr.nrm_nrm get] in Hprog.
              destruct Hprog as [[_ [Hn Hm]] Hsame].
              rewrite Hsame in Hn, Hm.
              repeat split; [symmetry; exact Hsame | exact Hn | exact Hm].
            - intros ss Hss Herr. exfalso.
              cbv beta iota delta [pick_unvisited2 MonadErr.nrm_err get] in Herr.
              sets_unfold in Herr. firstorder. }
          intro root. apply Hoare_normalize.
          intros sx [Hsx [Hnot_root Hmax]]; subst sx.
          assert (HR_full : R s0') by exact (conj HFC (conj Hphase (conj Hvis1 (conj Hscclt Hcorrect)))).
          eapply Hoare_bind.
          { exact (set_scc_root_id_R s0' root HR_full Hnot_root). }
          { intro jk. apply Hoare_normalize.
            intros sx2 [Hv2_eq2 [_ [Hfin_eq2 [HR1 [Hroot_id1 [Hscc_next1 Hother1]]]]]].
            assert (Hnr : ~visited2 sx2 root) by (rewrite Hv2_eq2; exact Hnot_root).
            assert (Hmx : forall w, ~visited2 sx2 w -> finish sx2 root >= finish sx2 w)
              by (intros w Hw; rewrite Hv2_eq2 in Hw; rewrite Hfin_eq2; exact (Hmax w Hw)).
            assert (Hlt_root : forall v0, visited2 sx2 v0 -> scc_id sx2 v0 < scc_id sx2 root).
            { intros v0 Hv0. rewrite Hv2_eq2 in Hv0.
              destruct (classic (v0 = root)) as [->|Hne];
                [exfalso; exact (Hnot_root Hv0)|].
              rewrite (Hother1 v0 Hne), Hroot_id1. exact (Hscclt v0 Hv0). }
            assert (Hroot_lt : scc_id sx2 root < scc_next sx2)
              by (rewrite Hroot_id1, Hscc_next1; lia).
            eapply Hoare_bind.
            { apply Hoare_conj.
              - exact (DFS_scc_R sx2 root HR1 Hnr Hmx Hlt_root Hroot_lt).
              - apply Hoare_conj.
                + apply Hoare_conj.
                  * exact (DFS_scc_same_root_id sx2 root root).
                  * assert (HFC2 : ForwardReachClosed sx2)
                      by (intros x0 y0 Hv; rewrite Hv2_eq2 in Hv;
                          intros Hr; rewrite Hv2_eq2; exact (HFC x0 y0 Hv Hr)).
                    assert (Hphase2 : Phase1_Order sx2).
                    { intros aa bb Hrr Hnrr.
                      destruct (Hphase aa bb Hrr Hnrr) as [c [Hm Hf]].
                      exists c; split; [exact Hm|rewrite Hfin_eq2; exact Hf]. }
                    exact (DFS_scc_mutually_reachable_root sx2 root HFC2 Hphase2 Hnr Hmx).
                + exact (DFS_scc_preserves_scc_next sx2 root root). }
            { intro jk2. apply Hoare_normalize.
              intros s2 [HR2 [[Hid_props Hmut_root] Hscc_next_eq]].
              destruct Hid_props as [Hsame_id [Hpres_id [Hroot_id2 Hsub2]]].
              assert (HAT2 : AntiTopo s2).
              { unfold AntiTopo. intros a b Ha Hb Hrev Hnrev.
                destruct (classic (visited2 sx2 a)) as [Ha0|Ha1];
                destruct (classic (visited2 sx2 b)) as [Hb0|Hb1].
                - assert (Ha_ne : a <> root) by (intro; subst; exact (Hnr Ha0)).
                  assert (Hb_ne : b <> root) by (intro; subst; exact (Hnr Hb0)).
                  rewrite (Hpres_id a Ha0 Ha_ne), (Hpres_id b Hb0 Hb_ne),
                         (Hother1 a Ha_ne), (Hother1 b Hb_ne).
                  apply HAT'; try (rewrite <- Hv2_eq2; assumption). exact Hrev. exact Hnrev.
                - assert (Ha_ne : a <> root) by (intro; subst; exact (Hnr Ha0)).
                  rewrite (Hpres_id a Ha0 Ha_ne), (Hsame_id b Hb Hb1),
                         Hroot_id2, Hroot_id1, (Hother1 a Ha_ne).
                  apply Hscclt. rewrite <- Hv2_eq2. exact Ha0.
                - exfalso. apply Ha1. rewrite Hv2_eq2.
                  apply (HFC b a). { rewrite <- Hv2_eq2; exact Hb0. }
                  apply reachable_iff_reachable_rev. exact Hrev.
                - exfalso. apply Hnrev.
                  pose proof (Hmut_root a Ha Ha1) as [Hra Har].
                  pose proof (Hmut_root b Hb Hb1) as [Hrb Hbr].
                  apply reachable_rev_intro.
                  unfold reachable; etransitivity; [exact Har | exact Hrb]. }
              eapply Hoare_imp_post.
              { exact (IH s2 tt (conj HR2 HAT2)). }
              { intros jk4 s' H; exact H. } } } }
        { apply Hoare_normal_assume_bind with
            (P := fun st => forall v, visited2 st v)
            (f := skip)
            (Q := fun _ s' => AntiTopo s')
            (s0 := s0').
          intros _. apply Hoare_ret; intros s Hs; subst; exact HAT'. }
    + intros _ s' [[Hvisited HR'] HAT'].
      destruct HR' as [_ [_ [_ [_ Hcorrect']]]].
      split; [exact Hvisited|split].
      * exact (fun u v => Hcorrect' u v (Hvisited u) (Hvisited v)).
      * exact HAT'.
Qed.

(* ================================================================= *)
(* mono_cont + BW_fix unfold lemmas for DFS_finish_f / DFS_scc_f.       *)
(* These let the cursor continuations in the refinement lib relate    *)
(* dfs_finish_from/dfs_scc_from to the abstract DFS step behaviour.   *)
(* Mirrors DFS.DFS_mono_cont / DFS_unfold in algorithms/DFS/DFS.v.    *)
(* ================================================================= *)

(** [mono_cont_at]: if [f] is mono_cont as a function producing a
    pointwise-included value (codomain [C -> program Σ B]), then for any
    fixed [a : C] the specialisation [fun W => f W a] is also mono_cont.
    This bridges the gap left by [mono_cont_auto], which does not descend
    through applications of an [BW_fix]-producing function to a concrete
    argument (the [repeat_break (...) ∅] shape in DFS_finish_f). *)

Lemma mono_cont_at {Σ A B C: Type}
      (f: (A -> program Σ B) -> C -> program Σ B) (a: C) :
  mono_cont f -> mono_cont (fun W => f W a).
Proof.
  intro Hf. unfold mono_cont in Hf. destruct Hf as [Hmono Hcont]. split.
  - unfold mono, Proper, respectful. intros W1 W2 HW.
    apply Hmono. exact HW.
  - unfold continuous in *. intros T HT.
    unfold seq_continuous in Hcont.
    apply (Hcont T HT).
Qed.

Lemma mono_cont_pointwise {Σ A B C: Type}
      (f: (A -> program Σ B) -> C -> program Σ B) :
  (forall c, mono_cont (fun W => f W c)) -> mono_cont f.
Proof.
  intro Hf. unfold mono_cont. split.
  - unfold mono, Proper, respectful. intros W1 W2 HW c.
    destruct (Hf c) as [Hmono _]. apply Hmono. exact HW.
  - unfold continuous. intros T HT c.
    destruct (Hf c) as [_ Hcont]. apply Hcont. exact HT.
Qed.

Lemma DFS_finish_f_mono_cont : mono_cont DFS_finish_f.
Proof.
  unfold DFS_finish_f.
  apply mono_cont_intro.
  intros.
  apply mono_cont_bind; [apply mono_cont_const | intros].
  unfold repeat_break.
  match goal with
  | |- mono_cont (fun (W : V -> program St unit) => ?F ?X) =>
      apply (mono_cont_at (fun (W : V -> program St unit) => F) X)
  end.
  apply mono_cont_BW_fix; intros; unfold repeat_break_f.
  all: (apply mono_cont_pointwise; intro; mono_cont_auto).
Qed.

Lemma DFS_scc_f_mono_cont : forall root, mono_cont (DFS_scc_f root).
Proof.
  intro root. unfold DFS_scc_f.
  apply mono_cont_intro; intros.
  apply mono_cont_bind; [apply mono_cont_const | intros].
  apply mono_cont_bind; [apply mono_cont_const | intros].
  unfold repeat_break.
  match goal with
  | |- mono_cont (fun (W : V -> program St unit) => ?F ?X) =>
      apply (mono_cont_at (fun (W : V -> program St unit) => F) X)
  end.
  apply mono_cont_BW_fix; intros; unfold repeat_break_f.
  all: (apply mono_cont_pointwise; intro; mono_cont_auto).
Qed.

Lemma DFS_finish_unfold (u : V) :
  @PartialOrder_Setoid.equiv (MonadErr.M St unit) _ (DFS_finish u) (DFS_finish_f DFS_finish u).
Proof.
  unfold DFS_finish. revert u.
  change (@PartialOrder_Setoid.equiv (V -> MonadErr.M St unit) _ DFS_finish (DFS_finish_f DFS_finish)).
  apply BW_fixpoint'. exact DFS_finish_f_mono_cont.
Qed.

Lemma DFS_scc_unfold (root u : V) :
  @PartialOrder_Setoid.equiv (MonadErr.M St unit) _ (DFS_scc root u) (DFS_scc_f root (DFS_scc root) u).
Proof.
  unfold DFS_scc. revert u.
  change (@PartialOrder_Setoid.equiv (V -> MonadErr.M St unit) _ (DFS_scc root) (DFS_scc_f root (DFS_scc root))).
  apply BW_fixpoint'. apply DFS_scc_f_mono_cont.
Qed.

Lemma repeat_break_break_step :
  forall (Σ: Type) {A: Type} {B: Type}
         (body: A -> program Σ (CntOrBrk A B)) (a: A) (b: B) (σ: Σ),
    (body a).(MonadErr.nrm) σ (@by_break A B b) σ ->
    (repeat_break body a).(MonadErr.nrm) σ b σ.
Proof.
  intros Σ A B body a b σ Hbodystep.
  pose proof (repeat_break_unfold body) as Hunf.
  unfold PartialOrder_Setoid.equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  specialize (Hunf a) as Hpt.
  destruct Hpt as [Hnrmpt _].
  sets_unfold in Hnrmpt.
  specialize (Hnrmpt σ b σ) as [_ Hbwd].
  apply Hbwd.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists (by_break b). exists σ. split.
  - exact Hbodystep.
  - simpl. split; reflexivity.
Qed.

(** [DFS_scc_absorb] — no-op transition.  When DFS_scc root u is started from
    a state where u is visited2, all of u's forward out-neighbours are
    visited2, and [scc_id st u = scc_id st root], then [DFS_scc root u] may
    take the no-op transition (tt, st): visit2 u and set_scc_id are absorbed
    (idempotent / already-set), and the repeat_break immediately breaks.  The
    sid-equality is exactly the [assertS (scc_id st u = scc_id st root)] guard
    that was added to DFS_scc_f's break branch — so the absorb is now
    contingent on the same fact the assertS checks.
    This is the engine for closing the dfs2 loop-exit / visited-skip gaps on
    the C-refinement side (lib: dfs_scc_absorb / dfs_scc_safe_return /
    dfs2_return_close).  *)
Lemma DFS_scc_absorb : forall root u (st: St),
  (forall v, step g u v -> visited2 st v) ->
  visited2 st u ->
  scc_id st u = scc_id st root ->
  (DFS_scc root u).(MonadErr.nrm) st tt st.
Proof.
  intros root u st Hneigh Hvis_u Hsid_eq.
  pose proof (DFS_scc_unfold root u) as Hunf.
  unfold PartialOrder_Setoid.equiv in Hunf. simpl in Hunf.
  unfold Equiv_lift, LiftConstructors.lift_rel2 in Hunf.
  destruct Hunf as [Hnrm _].
  sets_unfold in Hnrm.
  apply Hnrm.
  unfold DFS_scc_f.
  simpl.
  unfold MonadErr.bind. simpl.
  eexists tt. exists st. split.
  - unfold visit2, custom. simpl.
    split.
    + hnf. intros x. split; intros Hx.
      * left. exact Hx.
      * destruct Hx as [Hx | Hu]; [exact Hx | rewrite <- Hu; exact Hvis_u].
    + repeat split; reflexivity.
  - eexists tt. exists st. split.
    + unfold set_scc_id, custom. simpl.
      split; [exact Hsid_eq|].
      split; [intros v _; reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      reflexivity.
    + eapply repeat_break_break_step.
      unfold choice. simpl.
      right.
      unfold MonadErr.bind. simpl.
      eexists tt. exists st. split.
      * split.
        -- reflexivity.
        -- intros e v Hstep_aux.
           right. apply Hneigh. unfold step. eexists; exact Hstep_aux.
      * eexists tt. exists st. split.
        -- split; [reflexivity | exact Hsid_eq].
        -- simpl. split; reflexivity.
Qed.

End Kosaraju.
