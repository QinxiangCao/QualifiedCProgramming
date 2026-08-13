Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import TraceBasic TraceLogic CommonTactics.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From GraphLib Require Import floyd dijkstra.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib Algorithms.Dijkstra.Dijkstra. 

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.

Section Dijkstra.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {step_valid: StepValid G V E}
        {step_aux_unique: StepUniqueDirected G V E}
        {simple_graph: SimpleGraph G V E}
        (g: G)
        {g_valid: gvalid g}
        {eq_dec: EqDec V eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

(* 源点：算法开始执行的顶点 *)
Context (src: V) 
        (valid_src: vvalid g src).

(* Dijkstra成立的充分条件：没有负边 *)
Context {weight_nonneg: forall e, Z_op_le (Some 0) (weight g e)}.

(* Context {weight_valid: forall e, } *)

Record St: Type := mkSt {
  visited: V -> Prop;
  dist: V -> option Z;
}.

Instance: Settable St := settable! mkSt <visited; dist>.


Definition initSt: St := {|
  visited := ∅;
  dist := fun v => 
    if eq_dec v src then Some 0 else None
|}.


Definition visit (u: V): program St unit :=
  update' (fun s => s <| visited ::= fun vs => vs ∪ [u] |>).

Definition relax_edge (u: V) (e: E): program St unit :=
  assume (fun s => exists v, step_aux g e u v);;
  v <- get (fun s v => step_aux g e u v);;
  update' (fun s => s <| dist ::= fun dist0 =>
    v !-> (Z_op_min (dist0 v) (Z_op_plus (dist0 u) (weight g e))); dist0 |>).

Definition process_vertex (u: V): program St unit :=
  forset (fun e => exists v, step_aux g e u v) 
    (relax_edge u).

Definition unvisited (s: St) (u: V): Prop :=
  ~ u ∈ s.(visited).

Definition select_min_vertex: program St V :=
  get (fun s u => min_object_of_subset Z_op_le (fun v => unvisited s v) (s.(dist)) u).

Definition unvisited_no_reachable (s : St): Prop :=
  forall v, unvisited s v -> ~ reachable src v.

Definition body: program St (CntOrBrk unit unit) :=
  choice
    (assume (fun s => ~ unvisited_no_reachable s);;
      u <- select_min_vertex;;
      visit u;;
      process_vertex u;;
      ret (by_continue tt))
    (assume (fun s => unvisited_no_reachable s);;
      ret (by_break tt)).

Definition Dijkstra: program St unit :=
  repeat_break (fun _ => body) tt.

Local Open Scope ghost. 

Inductive Tag: Type :=
| In: V -> Tag
| Out: V -> Tag.

Definition body': programT St Tag (CntOrBrk unit unit) := 
  choice
    (↑(assume (fun s => ~ unvisited_no_reachable s));;
      u <- ↑(select_min_vertex);;
      ↑(visit u);;
      track (In (u));;
      ↑(process_vertex u);; 
      track (Out (u));;
      ret (by_continue tt))
    (↑(assume (fun s => unvisited_no_reachable s));;
      ret (by_break tt)). 

Definition Dijkstra': programT St Tag unit :=
  repeat_break (fun _ => body') tt.

Lemma Gequiv_Dijkstra: 
    Gequiv (Dijkstra) (Dijkstra'). 
Proof. 
  unfold Dijkstra, Dijkstra', body, body'. 
  Gequiv_autoT. 
Qed. 

Local Open Scope trace_scope.

Definition visited_in: St * (@TR Tag St) -> Prop :=
  fun '(s, tr) => forall v: V, v ∈ s.(visited) -> tr |= have (t↑(In v)). 

Definition visited_in_except_u (u: V): St * (@TR Tag St) -> Prop :=
  fun '(s, tr) => forall v: V, v <> u -> s.(visited) v -> tr |= have (tAtom (In v)).

Definition visited_persist: St * (@TR Tag St) -> Prop :=
  fun '(s, tr) => forall v: V, tr |= have (tAtom (In v)) -> s.(visited) v.

Definition visited_persist_within (u: V): St * (@TR Tag St) -> Prop :=
  fun '(s, tr) => (forall v: V, tr |= have (tAtom (In v)) -> s.(visited) v) /\ s.(visited) u.


#[export]Instance visited_in_proper: 
  forall tr,
    Proper (Sets.equiv ==> eq ==> iff) (fun (_: E -> Prop) s => visited_in (s, tr)).
Proof.
  unfold Proper, respectful, visited_in.
  intros tr s1 s2 Hs Heq v Hv.
  subst; split; auto.
Qed.

Lemma initSt_visited_in:
  visited_in (initSt, nil).
Proof.
  unfold visited_in.
  intros v Hv.
  subst; contradiction.
Qed.


Lemma initSt_visited_persist:
  visited_persist (initSt, nil).
Proof.
  intros v Hv.
  exfalso.
  eapply not_nil_have; eauto.
Qed.

Lemma Dijkstra_track_in_visited_in (u: V):
  Hoare (visited_in_except_u u)
        (track (In u))
        (fun _ => visited_in).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  destruct (classic (v = u)) as [-> | Hneq].
  - apply app_have_atom; right.
    apply singleton_have_atom; reflexivity.
  - apply app_have_atom; left.
    apply H; auto.
Qed.

Theorem Dijkstra_forset_visited_in: 
  forall u,
  Hoare (visited_in)
        (↑ (forset (fun e : E => exists v : V, step_aux g e u v) (relax_edge u)))%ghost
        (fun _ => visited_in).
Proof. 
  intros; intro_state_pair.
  eapply Hoare_liftG'; intros tr. 
  hoare_cons_pre (Hoare_forset (fun done s => visited_in (s, tr))). 
  * intros; inversion H0; subst; auto. 
  * apply visited_in_proper. 
  * intros; unfold relax_edge; intro_state; hoare_auto_s; subst; auto. 
Qed. 

Theorem Dijkstra_track_out_visited_in: 
  forall u,
  Hoare (visited_in)
        (track (Out u))
        (fun _ => visited_in).
Proof.
  intros; intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  rewrite app_have_atom; left; auto.
Qed.


Lemma Dijkstra_track_in_visited_persist (u: V):
  Hoare (visited_persist_within u)
        (track (In u))
        (fun _ => visited_persist).
Proof.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  destruct (classic (v = u)) as [-> | Hneq].
  - apply H.
  - apply app_have_atom in Hv as [Hv | Hv].
    + apply H; auto.
    + rewrite singleton_have_atom in Hv.
      inversion Hv; subst.
      contradiction.
Qed. 

Lemma Dijkstra_forset_visited_persist: 
  forall u,
  Hoare (visited_persist)
        (↑ (forset (fun e : E => exists v : V, step_aux g e u v) (relax_edge u)))%ghost
        (fun _ => visited_persist).
Proof.
  intros; intro_state_pair.
  eapply Hoare_liftG'; intros tr. 
  hoare_cons_pre (Hoare_forset (fun done s => visited_persist (s, tr))). 
  { intros; inversion H0; subst; auto. } 
  { intros set1 set2 Hseteq s1 s2 Hseq; subst; tauto. } 
  { intros; unfold relax_edge; intro_state; hoare_auto_s; subst; simpl; auto. }
Qed. 

Lemma Dijkstra_track_out_visited_persist: 
  forall u,
  Hoare (visited_persist)
        (track (Out u))
        (fun _ => visited_persist).
Proof.
  intros; intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros; subst; intros v Hv.
  apply app_have_atom in Hv as [Hv | Hv].
  + apply H; auto.
  + rewrite singleton_have_atom in Hv.
    inversion Hv.
Qed.



Lemma initSt_visited_dist_soundess:
  forall u, u ∈ initSt.(visited) -> min_value_weight_epath g src u (initSt.(dist) u).
Proof.
  unfold initSt. 
  intros u Hv; simpl in Hv. 
  contradiction. 
Qed.

(* 证明的右半部分：所有有效的的dist都对应着一条路径 *)

Definition dist_has_path (s: St): Prop :=
  forall v z,
    s.(dist) v = Some z ->
    exists p, valid_epath g src p v /\ epath_weight g p = Some z.

#[export] Instance dist_has_path_proper:
  Proper (Sets.equiv ==> eq ==> iff) (fun (_: E -> Prop) s => dist_has_path s).
Proof.
  unfold Proper, respectful, dist_has_path.
  intros done1 done2 _ s1 s2 Hs.
  subst.
  split; auto.
Qed.

Lemma initSt_dist_has_path:
  dist_has_path initSt.
Proof.
  unfold dist_has_path, initSt.
  intros v z Hv. simpl in Hv.
  destruct (eq_dec v src) as [Heq | Hneq].
  * assert (Heq': v = src) by congruence; subst; clear Heq. 
    exists nil; split; [apply valid_epath_empty|inversion Hv; subst].
    rewrite epath_weight_nil.
    reflexivity.
  * discriminate.
Qed.

Lemma Dijkstra_track_in_dist_has_path:
  forall u,
    Hoare (fun '(s, tr) => dist_has_path s)
          (track (In u))
          (fun _ '(s, tr) => dist_has_path s).
Proof.
  intros u.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros _ [] H0; inversion H0; subst; clear H0.
  auto.
Qed. 

Lemma Dijkstra_forset_dist_has_path:
  forall u,
    Hoare ((fun '(s, tr) => dist_has_path s)
          : (St * (list (Tag * St))) -> Prop)
          (↑ (forset (fun e : E => exists v : V, step_aux g e u v) (relax_edge u)))%ghost
          (fun _ '(s, tr) => dist_has_path s).
Proof.
  intros u.
  eapply Hoare_liftG; intros tr.
  hoare_cons_post (Hoare_forset (fun _ s => dist_has_path s)).
  { intros set1 set2 Hseteq s1 s2 Hseq; subst; tauto. }
  { intros done e _ _ _. 
    unfold relax_edge; intro_state; hoare_auto_s; subst.
    rename H1 into Hstep; rename a into v; 
    rename s0 into s; rename H into Hpath.
    simpl; intros x z Hx. 
    simpl in Hx. 
    unfold t_set in Hx.
    destruct (equiv_dec v x) as [<- | Hneq]. 
    2:{ eapply Hpath; auto. }

    destruct (dist s v) as [zv|] eqn:Hv; 
    destruct (dist s u) as [zu|] eqn:Hu; 
    destruct (weight g e) as [we|] eqn:Hew. 
    * inversion Hx; subst z; clear Hx.
      destruct (Hpath v zv Hv) as [pv [Hpv Hwv]].
      destruct (Z_le_dec zv (zu + we)).
      + exists pv; split; auto.
        rewrite Z.min_l by lia; auto.
      + destruct (Hpath u zu Hu) as [p [Hp Hw]].
        exists (p ++ e :: nil); split; 
        [eapply valid_epath_snoc; eauto|].
        rewrite epath_weight_app_assoc.
        rewrite epath_weight_single.
        rewrite Hw, Hew; simpl; f_equal; lia.
    * inversion Hx; subst z; clear Hx.
      destruct (Hpath v zv Hv) as [pv [Hpv Hwv]].
      exists pv. split; auto.
    * inversion Hx; subst z; clear Hx.
      destruct (Hpath v zv Hv) as [pv [Hpv Hwv]].
      exists pv. split; auto.
    * inversion Hx; subst z; clear Hx.
      destruct (Hpath v zv Hv) as [pv [Hpv Hwv]].
      exists pv. split; auto.
    * inversion Hx; subst z; clear Hx.
      destruct (Hpath u zu Hu) as [p [Hp Hw]].
      exists (p ++ e :: nil); split; 
      [eapply valid_epath_snoc; eauto|].
      rewrite epath_weight_app_assoc.
      rewrite epath_weight_single.
      rewrite Hw, Hew; simpl; reflexivity. 
    * discriminate. 
    * discriminate. 
    * discriminate. }
Qed.

Lemma Dijkstra_track_out_dist_has_path:
  forall u,
    Hoare (fun '(s, tr) => dist_has_path s)
          (track (Out u))
          (fun _ '(s, tr) => dist_has_path s).
Proof.
  intros u.
  intro_state_pair.
  hoare_cons_post Hoare_track_s.
  intros _ [] H0; inversion H0; subst; clear H0.
  auto.
Qed.


Lemma valid_epath_cut: 
  forall u v p S, 
    valid_epath g u p v -> 
    u ∈ S -> 
    ~ v ∈ S -> 
    exists x y e p1 p2, 
      x ∈ S /\
      ~ y ∈ S /\ 
      valid_epath g u p1 x /\
      step_aux g e x y /\
      valid_epath g y p2 v /\
      p = p1 ++ e :: p2.
Proof. 
  intros u v p S. 
  revert u v S.
  induction p.
  - intros;exfalso. 
    apply valid_epath_nil_inv in H; subst; auto. 
  - intros u v S H Hu Hv. 
    pose proof H as H'. 
    apply valid_epath_cons_inv in H as [w [Hstep Hvalid]]. 
    destruct (classic (w ∈ S)) as [Hwin|Hwnotin]. 
    * pose proof IHp w v S Hvalid Hwin Hv as [x [y[e [p1 [p2]]]]]. 
      destruct H as [Hx [Hy [Hp1 [He [Hp2 Hpeq]]]]].
      exists x, y, e, (a :: p1), p2. 
      repeat split; auto. 
      + eapply valid_epath_cons; eauto.  
      + subst; reflexivity. 
    * exists u, w, a, nil, p. 
      repeat split; auto. 
      apply valid_epath_empty.  
Qed.

(* 有效的路径都存在有限的距离。这一性质在原来的证明中并不需要，但在这里却显得很不可或缺。这是为什么？ *)
Context {valid_epath_have_dist: forall u p v, valid_epath g u p v -> exists z, epath_weight g p = Some z}.

Lemma min_valid_epath_cut: 
  forall u v w p1 p2, 
    min_object_weight_epath g u v (p1 ++ p2) -> 
    valid_epath g u p1 w -> 
    valid_epath g w p2 v -> 
    min_object_weight_epath g u w p1 /\ 
    min_object_weight_epath g w v p2.
Proof.
  intros u v w p1 p2 Hmin Hvalid1 Hvalid2.
  destruct Hmin as [Hpvalid Hpmin].  
  split. 
  - split; auto. 
    intros q Hq. 
    pose proof Hpmin (q ++ p2) ltac:(eapply valid_epath_app; eauto; tauto). 
    rewrite ! epath_weight_app_assoc in H. 
    pose proof valid_epath_have_dist w p2 v Hvalid2 as [z Hz]. 
    destruct (epath_weight g p1); 
    destruct (epath_weight g p2); 
    destruct (epath_weight g q); simpl in *; auto; try lia; try discriminate. 
  - split; auto. 
    intros q Hq. 
    pose proof Hpmin (p1 ++ q) ltac:(eapply valid_epath_app; eauto; tauto). 
    rewrite ! epath_weight_app_assoc in H. 
    pose proof valid_epath_have_dist u p1 w Hvalid1 as [z Hz]. 
    destruct (epath_weight g p1); 
    destruct (epath_weight g p2); 
    destruct (epath_weight g q); simpl in *; auto; try lia; try discriminate. 
Qed. 

Definition all_neighbor_relax (u: V) (s: St): Prop := 
  forall v e z, 
    step_aux g e u v -> 
    min_value_weight_epath g src u z -> 
    Z_op_le (s.(dist) v) (Z_op_plus z (weight g e)). 

Theorem Dijkstra_track_in_all_neighbor_relax:  
  forall a, 
    Hoare (fun '(s, tr) => forall u, tr |= have (t↑ (In (u))) -> tr |= have (s↑ (all_neighbor_relax u)))
        (track (In a))
        (fun _ '(s, tr) => forall u, u <> a -> tr |= have (t↑ (In (u))) -> tr |= have (s↑ (all_neighbor_relax u))).
Proof.
  intros a.
  intro_state_pair. 
  hoare_cons_post Hoare_track_s. 
  intros _ [] H0; inversion H0; subst; clear H0. 
  intros. rewrite app_have_atom in *. destruct H1 as [Hall|Hu]. 
  * left; apply H; auto. 
  * exfalso; rewrite singleton_have_atom in Hu; inversion Hu; auto. 
Qed. 

Theorem Dijkstra_forset_all_neighbor_relax: 
  forall a,
    Hoare (fun '(_, tr) => forall u , u <> a -> (tr |= have ↑ (t↑ (In u))) -> tr |= have ↑ (s↑ (all_neighbor_relax u)))
          (↑ (forset (fun e : E => exists v : V, step_aux g e a v) (relax_edge a)))%ghost
          (fun (_ : unit) '(s0, tr) =>
          (forall u, u <> a -> (tr |= have ↑ (t↑ (In u))) -> tr |= have ↑ (s↑ (all_neighbor_relax u))) /\
          (forall v e, step_aux g e a v -> Z_op_le (dist s0 v) (Z_op_plus (dist s0 a) (weight g e)))).
Proof.
  intros. 
  eapply Hoare_liftG'; intros tr.   
  eapply Hoare_conseq.
  3: {
    eapply Hoare_forset with (P:= fun done s => 
    (forall u, u <> a -> tr |= have (t↑ (In (u))) -> tr |= have (s↑ (all_neighbor_relax u))) /\ 
    forall v e, e ∈ done -> step_aux g e a v -> Z_op_le (s.(dist) v) (Z_op_plus (s.(dist) a) (weight g e))). 
    * intros eset1 eset2 Heset x y Hxy; subst; split; intros []; split; auto;
      intros; apply H0; try rewrite Heset in *; auto. 
    * intros done e Hdone He Hnotin. 
      intro_state; destruct H as [Hold Hnew]. 
      unfold relax_edge; hoare_auto_s. 
      rename a0 into v.
      split; [tauto|intros; subst; simpl; unfold t_set]. 
      destruct (equiv_dec v a) as [Heq|_]; auto. 
      { assert (v = a) by congruence; subst; clear Heq.  
        exfalso; eapply no_self_loop; eauto. } 
      destruct (equiv_dec v v0) as [Heq|Hneq]; auto. 
      { assert (v = v0) by congruence; subst; clear Heq. 
        eapply no_multiple_edge in H0; eauto; subst. 
        eapply Z_op_le_min_le_r. }
      destruct (classic (e0 ∈ done)). 
      { apply Hnew; auto. }
      { destruct H2; [contradiction|sets_unfold in H2; subst]. 
        eapply step_aux_unique in H0 as []; eauto; subst. 
        exfalso; apply Hneq; reflexivity. } 
  } 
  { intros; split; intros; [auto|contradiction]. }
  { intros; split; [apply H|intros; apply H; [eexists|]; eauto]. } 
Qed. 

Theorem Dijkstra_track_out_all_neighbor_relax: 
  forall a,
    Hoare (fun '(s, tr) => 
          (forall u, u <> a -> (tr |= have ↑ (t↑ (In u))) -> tr |= have ↑ (s↑ (all_neighbor_relax u))) /\
          (forall v e, step_aux g e a v -> Z_op_le (dist s v) (Z_op_plus (dist s a) (weight g e))) /\ 
          (forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u)) /\ 
          (forall u, tr |= have (t↑ (In (u))) -> s.(visited) u))
          (track (Out a))
          (fun _ '(s, tr) => forall u, tr |= have (t↑ (In (u))) -> tr |= have (s↑ (all_neighbor_relax u))).
Proof.
  intros a.
  intro_state_pair.  
  destruct H as [Hold [Hnew [Hvisited Hpersist]]].
  hoare_cons_post Hoare_track_s. 
  intros _ [] H0; inversion H0; subst; clear H0. 
  intros. rewrite app_have_atom in *. 
  destruct H; [|rewrite singleton_have_atom in H; inversion H]. 
  destruct (classic (u = a)); [subst; right|left].   
  * rewrite singleton_have_atom; intros v e z Hstep Hz. 
    assert (visited s a) by auto. 
    apply Hvisited in H0. 
    apply Hnew in Hstep. 
    eapply min_value_weight_epath_unique in Hz; eauto. 
    rewrite <- Hz; auto. 
  * apply Hold; auto.
Qed.


Theorem Dijkstra_track_in_dist_monotonic: 
  forall a, 
    Hoare (fun '(s, tr) => forall u z, tr |= have (s↑ (fun s => Z_op_le (s.(dist) u) z)) -> Z_op_le (s.(dist) u) z)
          (track (In a))
          (fun _ '(s, tr) => forall u z, tr |= have (s↑ (fun s => Z_op_le (s.(dist) u) z)) -> Z_op_le (s.(dist) u) z).
Proof.
  intros a.
  intro_state_pair. 
  hoare_cons_post Hoare_track_s. 
  intros _ [] H0; inversion H0; subst; clear H0. 
  intros. rewrite app_have_atom in *. destruct H0 as [Hall|Hu]; auto. 
  rewrite singleton_have_atom in Hu; auto. 
Qed.

Theorem Dijkstra_forset_dist_monotonic: 
  forall a,
    Hoare ((fun '(s0, tr) => 
          forall u z, (tr |= have ↑ (s↑ (fun s1 : St => Z_op_le (dist s1 u) z))) -> Z_op_le (dist s0 u) z) 
          : St * (list (Tag * St)) -> Prop)
          (↑ (forset (fun e : E => exists v : V, step_aux g e a v) (relax_edge a)))%ghost
          (fun (_ : unit) '(s0, tr) => 
          forall u z, (tr |= have ↑ (s↑ (fun s1 : St => Z_op_le (dist s1 u) z))) -> Z_op_le (dist s0 u) z).
Proof.
  intros a. 
  eapply Hoare_liftG; intros tr.
  eapply Hoare_forset with 
  (P:= fun done s => forall u z, tr |= have (s↑ (fun s1 : St => Z_op_le (dist s1 u) z)) -> Z_op_le (dist s u) z). 
  * intros eset1 eset2 Heset x y Hxy; subst; split; intros; auto;
    intros; apply H0; try rewrite Heset in *; auto. 
  * intros. 
    intro_state_pair. 
    unfold relax_edge; hoare_auto_s. 
    subst; simpl in *. 
    unfold t_set; destruct (equiv_dec a1 u) as [Heq|_]; auto. 
    assert (a1 = u) by congruence; subst; clear Heq. 
    eapply Z_op_le_trans. 
    apply Z_op_le_min_le_l. 
    auto. 
Qed. 

Theorem Dijkstra_track_out_dist_monotonic: 
  forall a,
    Hoare (fun '(s, tr) => forall u z, tr |= have (s↑ (fun s1 : St => Z_op_le (dist s1 u) z)) -> Z_op_le (dist s u) z)
          (track (Out a))
          (fun _ '(s, tr) => forall u z, tr |= have (s↑ (fun s1 : St => Z_op_le (dist s1 u) z)) -> Z_op_le (dist s u) z).
Proof.
  intros a.
  intro_state_pair. 
  hoare_cons_post Hoare_track_s. 
  intros _ [] H0; inversion H0; subst; clear H0. 
  intros. rewrite app_have_atom in *. destruct H0 as [Hall|Hu]; auto. 
  rewrite singleton_have_atom in Hu; auto. 
Qed. 


Theorem Dijkstra_track_in_dist_soundness: 
  forall a,
    Hoare (fun '(s, tr) => forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u))
          (track (In a))
          (fun _ '(s, tr) => forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u)).
Proof.
  intros a.
  intro_state_pair. 
  hoare_cons_post Hoare_track_s. 
  intros _ [] H0; inversion H0; subst; clear H0; auto.
Qed. 


Theorem Dijkstra_forset_dist_soundness:  
  forall w,
  Hoare ((fun '(s, tr) => w ∈ visited s /\ forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u))
        : St * (list (Tag * St)) -> Prop)
        (↑ (forset (fun e : E => exists v : V, step_aux g e w v) (relax_edge w)))%ghost
        (fun _ '(s, tr) => forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u)). 
Proof.
  intros a. 
  eapply Hoare_liftG; intros tr.
  hoare_cons_post (Hoare_forset (fun _ s => a ∈ visited s /\ forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u))).
  { intros set1 set2 Hseteq s1 s2 Hseq; subst; tauto. }
  { 
    intros. intro_state; unfold relax_edge; hoare_auto_s; subst; simpl in *.
    split; [tauto|intros]. 
    rename a0 into e; rename a into v; rename a1 into w. 
    destruct H2 as [Hv Hvisited]; rename H5 into Hu. 
    destruct (classic (w ∈ visited s0)) as [Hw|];
    unfold t_set; destruct (equiv_dec w u); auto;
    assert (w = u) by auto; subst; try contradiction.
    pose proof Hvisited u Hw as [[[p [[Hpvalid Hpmin] Hpeq]] _]|[Hpcut Hpnone]]. 
    * left; split; [exists p; split; [split|]|apply Z_op_le_none_r]; auto.
      rewrite Hpeq.  
      assert (Z_op_le (dist s0 u) (Z_op_plus (dist s0 v) (weight g e))) as Hle. {
        pose proof Hvisited v Hv as [[[q [[Hqvalid Hqmin] Hqeq]] _]|[_ Hqnone]]. 
        + pose proof Hpmin (q ++ e :: nil) 
          ltac:(eapply valid_epath_snoc; eauto; tauto) as Hle. 
          rewrite <- Hpeq; rewrite <- Hqeq. 
          rewrite epath_weight_app_assoc in Hle. 
          rewrite epath_weight_single in Hle. auto. 
        + rewrite Hqnone. 
          simpl. 
          apply Z_op_le_none_r.  
      } rewrite Z_op_le_min_l; auto. 
    * rewrite Hpnone. 
      pose proof Hvisited v Hv as [[[q [[Hqvalid Hqmin] Hqeq]] _]|[_ Hqnone]]. 
      2:{ rewrite Hqnone; simpl; right; split; auto. } 
      destruct (dist s0 v). 
      2:{ simpl; right; split; auto. } 
      destruct (weight g e) eqn: He. 
      2:{ simpl; right; split; auto. } 
      pose proof Hpcut (q ++ e :: nil) 
      ltac:(eapply valid_epath_snoc; eauto; tauto) as Hcontr. 
      rewrite epath_weight_app_assoc in Hcontr.
      rewrite epath_weight_single in Hcontr.
      rewrite Hqeq, He in Hcontr; simpl in Hcontr. contradiction. 
  }
Qed.

Theorem Dijkstra_track_out_dist_soundness: 
  forall a,
    Hoare (fun '(s, tr) => forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u))
          (track (Out a))
          (fun _ '(s, tr) => forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u)).
Proof.
  intros a.
  intro_state_pair. 
  hoare_cons_post Hoare_track_s. 
  intros _ [] H0; inversion H0; subst; clear H0; auto.
Qed. 

Theorem Dijkstra_forset_keep_visited: 
  forall x u,
    Hoare ((fun '(s, tr) => x ∈ visited s): 
          St * (list (Tag * St)) -> Prop)
          (↑ (forset (fun e : E => exists v : V, step_aux g e u v) (relax_edge u)))%ghost
          (fun _ '(s, tr) => x ∈ visited s).
Proof.
  intros x u.
  eapply Hoare_liftG; intros tr.
  hoare_cons_post (Hoare_forset (fun _ s => x ∈ visited s)).
  { intros set1 set2 Hseteq s1 s2 Hseq; subst; tauto. }
  { intros. intro_state; unfold relax_edge; hoare_auto_s; subst; auto. }
Qed.

Theorem Dijkstra_first_step: 
  Hoare (fun '(s, tr) => s = initSt /\ tr = nil)
        (body')
        (fun _ '(s, tr) => 
        (forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u)) /\ 
        (forall u, s.(visited) u -> tr |= have (t↑ (In (u)))) /\ 
        (forall u, tr |= have (t↑ (In (u))) -> s.(visited) u) /\ 
        (forall u, tr |= have (t↑ (In (u))) -> tr |= have (s↑ (all_neighbor_relax u))) /\ 
        (forall u z, (tr |= have ↑ (s↑ (fun s1 : St => Z_op_le (dist s1 u) z))) -> Z_op_le (dist s u) z) /\ 
        (dist_has_path s) /\ 
        (src ∈ s.(visited))). 
Proof.
  unfold body'.  
  intro_state_pair; destruct H as [Hs Hl]. 
  hoare_auto_G.
  2: { 
    destruct H; subst; repeat split. 
    * apply initSt_visited_dist_soundess; auto.
    * intros; simpl in H; contradiction. 
    * intros; exfalso; eapply not_nil_have; eauto. 
    * intros; exfalso; eapply not_nil_have; eauto. 
    * intros; exfalso; eapply not_nil_have; eauto. 
    * apply initSt_dist_has_path. 
    * eapply init_unvisited_reachable; eauto. 
  } destruct H; subst. 
  unfold select_min_vertex, visit, process_vertex; hoare_auto_G. 
  destruct H; subst.

  assert (a = src). {
  destruct H1 as [_ H1].  
  unfold unvisited, initSt in H1; simpl in H1.
  pose proof H1 src ltac:(sets_unfold; intros; auto) as Hcon. 
  destruct (eq_dec src src); 
  [|exfalso; apply c; reflexivity]. 
  destruct (eq_dec a src); auto. 
  contradiction. } subst a.  

  intro_state_pair.

  eapply Hoare_bind. { 
    do 3 eapply Hoare_conj. 
    * hoare_cons_pre Dijkstra_track_in_dist_soundness. 
      simpl; intros; inversion H; subst; intros; destruct H2; [contradiction|sets_unfold in H2; subst]; simpl. 
      destruct (eq_dec src src); [|exfalso; apply c; reflexivity]. 
      eapply min_value_weight_epath_refl; eauto. 
    * hoare_cons_pre Dijkstra_track_in_visited_in. 
      intros; inversion H; subst; simpl; intros; destruct H3; [contradiction|sets_unfold in H3; subst; contradiction]. 
    * hoare_cons_pre Dijkstra_track_in_visited_persist. 
      simpl; intros; inversion H; subst; simpl; intros; split; [intros; exfalso; eapply not_nil_have; eauto|right; reflexivity]. 
    * hoare_cons_pre Dijkstra_track_in_all_neighbor_relax. 
      simpl; intros; inversion H; subst; simpl; intros; exfalso; eapply not_nil_have; eauto. 
    * hoare_cons_pre Dijkstra_track_in_dist_monotonic. 
      simpl; intros; inversion H; subst; simpl; intros; exfalso; eapply not_nil_have; eauto. 
    * hoare_cons_pre Dijkstra_track_in_dist_has_path. 
      simpl; intros; inversion H; subst; unfold dist_has_path; simpl; intros. 
      destruct (eq_dec v src); inversion H2. 
      assert (v = src) by auto; subst. 
      exists nil; split; [apply valid_epath_empty|rewrite epath_weight_nil; auto]. 
    * apply Hoare_track_s. 
    * instantiate (1 := fun _ '(s, tr) => src ∈ s.(visited)).  
      hoare_cons_post Hoare_track_s. 
      intros; subst; inversion H; subst; right; reflexivity. 
  } simpl; intros _. 
  eapply Hoare_bind. {
    do 2 eapply Hoare_conj. 
    apply Hoare_conj. apply Hoare_conj. apply Hoare_conj. 
    * hoare_cons_pre Dijkstra_forset_dist_soundness. 
      intros. destruct s0; split; inversion H; subst;
      my_destruct H2; inversion H7; subst; simpl; [right; reflexivity|auto].
    * hoare_cons_pre Dijkstra_forset_visited_in. 
    * hoare_cons_pre Dijkstra_forset_visited_persist. 
    * hoare_cons_pre Dijkstra_forset_all_neighbor_relax. 
    * hoare_cons_pre Dijkstra_forset_dist_monotonic. 
    * hoare_cons_pre Dijkstra_forset_dist_has_path.  
    * instantiate (1 := fun _ '(s, tr) => src ∈ s.(visited)). 
      hoare_cons_pre Dijkstra_forset_keep_visited.    
  } simpl; intros _. 
  eapply Hoare_bind. {
    do 2 eapply Hoare_conj. 
    apply Hoare_conj. apply Hoare_conj. apply Hoare_conj. 
    * hoare_cons_pre Dijkstra_track_out_dist_soundness. 
    * hoare_cons_pre Dijkstra_track_out_visited_in. 
    * hoare_cons_pre Dijkstra_track_out_visited_persist. 
    * hoare_cons_pre Dijkstra_track_out_all_neighbor_relax. 
      intros; destruct s0; my_destruct H2; repeat split; auto.
    * hoare_cons_pre Dijkstra_track_out_dist_monotonic. 
    * hoare_cons_pre Dijkstra_track_out_dist_has_path. 
    * instantiate (1 := fun _ '(s, tr) => src ∈ s.(visited)). 
      intro_state_pair. 
      hoare_cons_post Hoare_track_s. 
      intros; subst; inversion H; subst; tauto. 
  } simpl; intros _. 
  hoare_auto_s; destruct s0; repeat split; try tauto. 
Qed.
    


Lemma Dijkstra_visited_dist_soundess: 
  Hoare (fun '(s, tr) => s = initSt /\ tr = nil)
        Dijkstra' 
        (fun _ '(s, tr) => 
        (forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u)) /\ 
        (forall u, s.(visited) u -> tr |= have (t↑ (In (u)))) /\ 
        (forall u, tr |= have (t↑ (In (u))) -> s.(visited) u) /\ 
        (forall u, tr |= have (t↑ (In (u))) -> tr |= have (s↑ (all_neighbor_relax u))) /\ 
        (forall u z, (tr |= have ↑ (s↑ (fun s1 : St => Z_op_le (dist s1 u) z))) -> Z_op_le (dist s u) z) /\ 
        (dist_has_path s) /\ 
        (src ∈ s.(visited))). 
Proof.
  unfold Dijkstra'.
  eapply (proj2 (Hoare_equiv_iff _ _ _ _ (repeat_break_unfold _ tt))). 
  eapply Hoare_bind. { apply Dijkstra_first_step. } 
  intros [[]| []].
  2: { apply Hoare_ret'; auto. }
  hoare_cons_pre (Hoare_repeat_break' _ (fun _ '(s, tr) => 
  (forall u, s.(visited) u -> min_value_weight_epath g src u (s.(dist) u)) /\  
  (forall u, s.(visited) u -> tr |= have (t↑ (In (u)))) /\ 
  (forall u, tr |= have (t↑ (In (u))) -> s.(visited) u) /\ 
  (forall u, tr |= have (t↑ (In (u))) -> tr |= have (s↑ (all_neighbor_relax u))) /\ 
  (forall u z, (tr |= have ↑ (s↑ (fun s1 : St => Z_op_le (dist s1 u) z))) -> Z_op_le (dist s u) z) /\ 
  (dist_has_path s) /\ 
  (src ∈ s.(visited)))). 
  - intros _. 
    intro_state_pair; destruct H as [Hvisited [Hback [Hpersist [Hneighbor [Hmono [Hpath Hsrc]]]]]]. 
    unfold body', select_min_vertex, visit, process_vertex; hoare_auto_G.
    destruct H, H0; subst. 
    2:{ hoare_auto_s. } 
    intro_state_pair.
    assert (forall u, u ∈ visited s0 -> min_value_weight_epath g src u (dist s0 u)). {
      intros u Hu; inversion H; subst; clear H. 
      destruct Hu as [|Hu]; [simpl; auto|sets_unfold in Hu; subst a; simpl].
      pose proof @min_value_weight_epath_exist _ _ _ pg gv g
      _ _ _ _ _ _ _ weight_nonneg src u as [zsu Hzsu]. 
      destruct (classic (visited s u)) as [|Hunotin]; auto. 
      replace (dist s u) with zsu; auto. 
      assert (Z_op_le zsu (dist s u) /\ Z_op_le (dist s u) zsu). 
      2:{ destruct zsu, (dist s u); simpl in *; try lia; auto; f_equal; lia. } split. 
      * assert (dist_has_path s) by auto. 
        destruct (dist s u) eqn:Hdistu; [|apply Z_op_le_none_r]. 
        apply H in Hdistu as [q [Hqvalid Hqeq]]. 
        destruct Hzsu as [[[p [[Hpvalid Hpmin] Hpeq]] _]|[]]. 
        + pose proof Hpmin q Hqvalid. 
          rewrite <- Hpeq, <- Hqeq; auto. 
        + pose proof H0 q Hqvalid as Hcontr. 
          rewrite Hqeq in Hcontr; inversion Hcontr.
      * apply NNPP; intros Hgt.
        destruct Hzsu as [[[p Hp] _]|[]]. 
        2:{ subst; exfalso. apply Hgt; apply Z_op_le_none_r. } 
        pose proof Hp as [[Hpvalid Hpmin] Hpzsu].
        pose proof valid_epath_cut src u p (visited s) Hpvalid Hsrc Hunotin 
        as [x [y [e [p1 [p2 [Hx [Hy [Hp1 [He [Hp2 Hpeq]]]]]]]]]]. 

        assert (Z_op_le (dist s u) (dist s y)) as Hle1. 
        {
          destruct H2 as [Huvalid Humin]. 
          pose proof Humin y Hy. 
          assumption. 
        }

        assert (Z_op_le (epath_weight g (p1 ++ e :: nil)) zsu) as Hle2. 
        {
          rewrite <- Hpzsu. 
          subst. 
          rewrite ! epath_weight_app_assoc.
          apply Z_op_plus_mono.
          apply Z_op_le_refl.
          rewrite ! epath_weight_cons. 
          apply Z_op_plus_mono.  
          apply Z_op_le_refl. 
          rewrite epath_weight_nil. 
          eapply non_neg_epath; eauto. 
        } 

        assert (Z_op_le (dist s y) (epath_weight g (p1 ++ e :: nil))) as Hle3. 
        {
          assert (l |= have (t↑ (In (x)))) as Hxhave by auto.
          pose proof Hneighbor x Hxhave.
          unfold all_neighbor_relax in H. 
          pose proof min_valid_epath_cut src u x p1 (e :: p2)
          ltac:(rewrite <- Hpeq; split; auto) Hp1 ltac:(eapply valid_epath_cons; eauto) as [Hp1min _]. 
          assert (l |= have (s↑ (fun s => Z_op_le (dist s y) (Z_op_plus (epath_weight g p1) (weight g e))))).
          {
            unfold last, have, sAtom, lift in *. 
            destruct H as [j []]. 
            exists j; split; auto.
            destruct (nth_error l (j - 1)) as [[]|] eqn:Heq; auto.
            apply H0; auto. 
            left; split; [exists p1; split; auto|apply Z_op_le_none_r].
          } clear H.
          apply Hmono in H0. 
          rewrite epath_weight_app_assoc; rewrite epath_weight_single; auto.
        } 
        apply Hgt. 
        do 2 (eapply Z_op_le_trans; eauto).
    }
    eapply Hoare_bind. {  
      do 3 eapply Hoare_conj. 
      * hoare_cons_pre Dijkstra_track_in_dist_soundness. 
        intros; subst; auto. 
      * hoare_cons_pre Dijkstra_track_in_visited_in. 
        intros; subst; auto.  
        unfold visited_in_except_u; inversion H; subst; intros. 
        destruct H4; [auto|sets_unfold in H4; subst; contradiction]. 
      * hoare_cons_pre Dijkstra_track_in_visited_persist. 
        intros; subst; auto. 
        unfold visited_persist_within; inversion H; subst; intros. 
        split; [simpl; intros; left; auto|right; reflexivity]. 
      * hoare_cons_pre Dijkstra_track_in_all_neighbor_relax. 
        intros; inversion H; subst; auto. 
      * hoare_cons_pre Dijkstra_track_in_dist_monotonic. 
        intros; inversion H; subst; auto. 
      * apply Hoare_track_s. 
      * hoare_cons_pre Dijkstra_track_in_dist_has_path. 
        intros; inversion H; subst; auto. 
      * instantiate (1 := fun _ '(s, tr) => src ∈ s.(visited)). 
        hoare_cons_post Hoare_track_s. 
        intros; subst; inversion H; subst; left; auto. 
    } simpl; intros _.
    rewrite bind_assoc. 
    eapply Hoare_bind. {
      do 2 eapply Hoare_conj. 
      apply Hoare_conj. apply Hoare_conj. apply Hoare_conj. 
      * hoare_cons_pre Dijkstra_forset_dist_soundness. 
        intros; destruct s1; split; inversion H; subst;
        my_destruct H3; inversion H9; subst; simpl; [right; reflexivity|auto].
      * hoare_cons_pre Dijkstra_forset_visited_in. 
      * hoare_cons_pre Dijkstra_forset_visited_persist. 
      * hoare_cons_pre Dijkstra_forset_all_neighbor_relax. 
      * hoare_cons_pre Dijkstra_forset_dist_monotonic. 
      * hoare_cons_pre Dijkstra_forset_dist_has_path. 
      * hoare_cons_pre (Dijkstra_forset_keep_visited src). 
    } simpl; intros _. 
    rewrite bind_assoc. 
    eapply Hoare_bind. {
      do 2 eapply Hoare_conj.   
      apply Hoare_conj. apply Hoare_conj. apply Hoare_conj. 
      * hoare_cons_pre Dijkstra_track_out_dist_soundness. 
      * hoare_cons_pre Dijkstra_track_out_visited_in. 
      * hoare_cons_pre Dijkstra_track_out_visited_persist. 
      * hoare_cons_pre Dijkstra_track_out_all_neighbor_relax. 
        intros; destruct s1; my_destruct H3; repeat split; auto.
      * hoare_cons_pre Dijkstra_track_out_dist_monotonic. 
      * hoare_cons_pre Dijkstra_track_out_dist_has_path. 
      * instantiate (1 := fun _ '(s, tr) => src ∈ s.(visited)). 
        intro_state_pair. hoare_cons_post Hoare_track_s. 
        intros; subst; inversion H; subst; tauto. 
    } simpl; intros _.  
    hoare_auto_s; destruct s1; repeat split; try tauto. 
  - intros _. 
    intro_state_pair; destruct H as [Hvisited [Hback [Hpersist [Hneighbor [Hmono [Hpath Hsrc]]]]]]. 
    unfold body', select_min_vertex, visit, process_vertex; hoare_auto_G.
    destruct H, H0; subst. 
    2:{ hoare_auto_s; destruct H; subst; repeat split; auto. } 
    intro_state_pair.
    assert (forall u, u ∈ visited s0 -> min_value_weight_epath g src u (dist s0 u)). {
      intros u Hu; inversion H; subst; clear H. 
      destruct Hu as [|Hu]; [simpl; auto|sets_unfold in Hu; subst a; simpl].
      pose proof @min_value_weight_epath_exist _ _ _ pg gv g
      _ _ _ _ _ _ _ weight_nonneg src u as [zsu Hzsu]. 
      destruct (classic (visited s u)) as [|Hunotin]; auto. 
      replace (dist s u) with zsu; auto. 
      assert (Z_op_le zsu (dist s u) /\ Z_op_le (dist s u) zsu). 
      2:{ destruct zsu, (dist s u); simpl in *; try lia; auto; f_equal; lia. } split. 
      * assert (dist_has_path s) by auto. 
        destruct (dist s u) eqn:Hdistu; [|apply Z_op_le_none_r]. 
        apply H in Hdistu as [q [Hqvalid Hqeq]]. 
        destruct Hzsu as [[[p [[Hpvalid Hpmin] Hpeq]] _]|[]]. 
        + pose proof Hpmin q Hqvalid. 
          rewrite <- Hpeq, <- Hqeq; auto. 
        + pose proof H0 q Hqvalid as Hcontr. 
          rewrite Hqeq in Hcontr; inversion Hcontr.
      * apply NNPP; intros Hgt.
        destruct Hzsu as [[[p Hp] _]|[]]. 
        2:{ subst; exfalso. apply Hgt; apply Z_op_le_none_r. } 
        pose proof Hp as [[Hpvalid Hpmin] Hpzsu].
        pose proof valid_epath_cut src u p (visited s) Hpvalid Hsrc Hunotin 
        as [x [y [e [p1 [p2 [Hx [Hy [Hp1 [He [Hp2 Hpeq]]]]]]]]]]. 

        assert (Z_op_le (dist s u) (dist s y)) as Hle1. 
        {
          destruct H2 as [Huvalid Humin]. 
          pose proof Humin y Hy. 
          assumption. 
        }

        assert (Z_op_le (epath_weight g (p1 ++ e :: nil)) zsu) as Hle2. 
        {
          rewrite <- Hpzsu. 
          subst. 
          rewrite ! epath_weight_app_assoc.
          apply Z_op_plus_mono.
          apply Z_op_le_refl.
          rewrite ! epath_weight_cons. 
          apply Z_op_plus_mono.  
          apply Z_op_le_refl. 
          rewrite epath_weight_nil. 
          eapply non_neg_epath; eauto. 
        } 

        assert (Z_op_le (dist s y) (epath_weight g (p1 ++ e :: nil))) as Hle3. 
        {
          assert (l |= have (t↑ (In (x)))) as Hxhave by auto.
          pose proof Hneighbor x Hxhave.
          unfold all_neighbor_relax in H. 
          pose proof min_valid_epath_cut src u x p1 (e :: p2)
          ltac:(rewrite <- Hpeq; split; auto) Hp1 ltac:(eapply valid_epath_cons; eauto) as [Hp1min _]. 
          assert (l |= have (s↑ (fun s => Z_op_le (dist s y) (Z_op_plus (epath_weight g p1) (weight g e))))).
          {
            unfold last, have, sAtom, lift in *. 
            destruct H as [j []]. 
            exists j; split; auto.
            destruct (nth_error l (j - 1)) as [[]|] eqn:Heq; auto.
            apply H0; auto. 
            left; split; [exists p1; split; auto|apply Z_op_le_none_r].
          } clear H.
          apply Hmono in H0. 
          rewrite epath_weight_app_assoc; rewrite epath_weight_single; auto.
        } 
        apply Hgt. 
        do 2 (eapply Z_op_le_trans; eauto).
    }
    eapply Hoare_bind. {  
      do 3 eapply Hoare_conj. 
      * hoare_cons_pre Dijkstra_track_in_dist_soundness. 
        intros; subst; auto. 
      * hoare_cons_pre Dijkstra_track_in_visited_in. 
        intros; subst; auto.  
        unfold visited_in_except_u; inversion H; subst; intros. 
        destruct H4; [auto|sets_unfold in H4; subst; contradiction]. 
      * hoare_cons_pre Dijkstra_track_in_visited_persist. 
        intros; subst; auto. 
        unfold visited_persist_within; inversion H; subst; intros. 
        split; [simpl; intros; left; auto|right; reflexivity]. 
      * hoare_cons_pre Dijkstra_track_in_all_neighbor_relax. 
        intros; inversion H; subst; auto. 
      * hoare_cons_pre Dijkstra_track_in_dist_monotonic. 
        intros; inversion H; subst; auto. 
      * apply Hoare_track_s. 
      * hoare_cons_pre Dijkstra_track_in_dist_has_path. 
        intros; inversion H; subst; auto. 
      * instantiate (1 := fun _ '(s, tr) => src ∈ s.(visited)). 
        hoare_cons_post Hoare_track_s. 
        intros; subst; inversion H; subst; left; auto. 
    } simpl; intros _.
    rewrite bind_assoc. 
    eapply Hoare_bind. {
      do 2 eapply Hoare_conj. 
      apply Hoare_conj. apply Hoare_conj. apply Hoare_conj. 
      * hoare_cons_pre Dijkstra_forset_dist_soundness. 
        intros; destruct s1; split; inversion H; subst;
        my_destruct H3; inversion H9; subst; simpl; [right; reflexivity|auto].
      * hoare_cons_pre Dijkstra_forset_visited_in. 
      * hoare_cons_pre Dijkstra_forset_visited_persist. 
      * hoare_cons_pre Dijkstra_forset_all_neighbor_relax. 
      * hoare_cons_pre Dijkstra_forset_dist_monotonic. 
      * hoare_cons_pre Dijkstra_forset_dist_has_path. 
      * hoare_cons_pre (Dijkstra_forset_keep_visited src). 
    } simpl; intros _. 
    rewrite bind_assoc. 
    eapply Hoare_bind. {
      do 2 eapply Hoare_conj.   
      apply Hoare_conj. apply Hoare_conj. apply Hoare_conj. 
      * hoare_cons_pre Dijkstra_track_out_dist_soundness. 
      * hoare_cons_pre Dijkstra_track_out_visited_in. 
      * hoare_cons_pre Dijkstra_track_out_visited_persist. 
      * hoare_cons_pre Dijkstra_track_out_all_neighbor_relax. 
        intros; destruct s1; my_destruct H3; repeat split; auto.
      * hoare_cons_pre Dijkstra_track_out_dist_monotonic. 
      * hoare_cons_pre Dijkstra_track_out_dist_has_path. 
      * instantiate (1 := fun _ '(s, tr) => src ∈ s.(visited)). 
        intro_state_pair. hoare_cons_post Hoare_track_s. 
        intros; subst; inversion H; subst; tauto. 
    } simpl; intros _.  
    hoare_auto_s; destruct s1; repeat split; try tauto. 
Qed.

Definition reachable_visited (s: St): Prop :=  
  forall v, reachable src v -> v ∈ s.(visited).
  
Definition distance_correct (s: St): Prop :=
  forall u, 
    reachable src u -> 
    min_value_weight_epath g src u (s.(dist) u).

Lemma break_cond_implies_reachable_visited: 
  forall s, unvisited_no_reachable s -> reachable_visited s.
Proof.
  unfold unvisited_no_reachable, reachable_visited, unvisited.
  intros s Hbreak v Hreach.
  apply NNPP. 
  intro Hnot_vis.
  pose proof (Hbreak v Hnot_vis) as Hnot_reach.
  contradiction.
Qed.

Theorem Dijkstra_reachable_visited: 
  Hoare (fun s => s = initSt) 
        Dijkstra 
        (fun _ s => reachable_visited s).
Proof.
  unfold Dijkstra.
  eapply Hoare_conseq_pre; [intros; exact I |].
  eapply Hoare_repeat_break with (P := fun _ _ => True).
  intros _.
  unfold body.
  apply Hoare_choice.
  - apply Hoare_assume_bind; intros.
    eapply Hoare_bind; [apply Hoare_post_true |].
    intros. 
    eapply Hoare_bind; [apply Hoare_post_true |]. 
    intros.
    eapply Hoare_bind; [apply Hoare_post_true |]. 
    intros.
    apply Hoare_ret'; intros; exact I.
  - apply Hoare_assume_bind.
    apply Hoare_ret'.
    intros s [Hcond _].
    apply break_cond_implies_reachable_visited; auto. 
Qed.

Lemma Dijkstra_visited_dist_soundess': 
  Hoare (fun '(s, tr) => s = initSt /\ tr = nil)
        Dijkstra' 
        (fun _ '(s, tr) => reachable_visited s -> distance_correct s). 
Proof. 
  hoare_cons Dijkstra_visited_dist_soundess. 
  intros; destruct s; subst; simpl; auto. 
  my_destruct H. 
  intros Hp u Hu. 
  apply H. 
  apply Hp. 
  auto.
Qed.

Theorem Dijkstra_correct: 
  Hoare (fun s => s = initSt)
        Dijkstra
        (fun _ s => distance_correct s). 
Proof. 
  eapply Hoare_conseq_post. 
  2:{
    apply Hoare_conj. 
    apply Dijkstra_reachable_visited. 
    eapply Hoare_fromG. 
    apply Gequiv_Dijkstra. 
    apply Dijkstra_visited_dist_soundess'. 
    intros; subst; exists nil; split; auto. 
  } 
  simpl; intros. 
  tauto. 
Qed.

End Dijkstra.
