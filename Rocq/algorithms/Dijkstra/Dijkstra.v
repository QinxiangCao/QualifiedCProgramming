Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From GraphLib Require Import floyd dijkstra.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

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
  visit u;;
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
      process_vertex u;;
      ret (by_continue tt))
    (assume (fun s => unvisited_no_reachable s);;
      ret (by_break tt)).

Definition Dijkstra: program St unit :=
  repeat_break (fun _ =>
    body) tt.

Definition distance_correct (s: St): Prop :=
  forall u, 
    reachable src u -> 
    min_value_weight_epath g src u (s.(dist) u).

Definition visited_dist_final (s: St): Prop :=
  forall v, v ∈ s.(visited) -> 
    min_value_weight_epath g src v (s.(dist) v) /\ 
    min_value_weight_epath_in_vset g src v (s.(visited)) (s.(dist) v).

Definition unvisited_dist_optimal (s: St): Prop :=
  forall v, ~ v ∈ s.(visited) ->
    min_value_weight_epath_in_vset g src v (s.(visited)) (s.(dist) v). 

Definition visited_le_unvisited (s: St): Prop :=
  forall u v, u ∈ s.(visited) -> ~ v ∈ s.(visited) ->
    Z_op_le (s.(dist) u) (s.(dist) v).

Definition reachable_visited (s: St): Prop :=  
  forall v, reachable src v -> v ∈ s.(visited).

(* 初始条件不满足循环不变量，存第一次循环之后才开始满足循环不变量 *)


Lemma init_unvisited_reachable: 
  ~ unvisited_no_reachable initSt. 
Proof. 
  unfold not; intros. 
  specialize (H src). 
  unfold unvisited, initSt in H; simpl in H. 
  pose proof H ltac:(try split; auto). 
  apply H0; reflexivity. 
Qed. 

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

Definition first_step_invariant (done: E -> Prop) (s: St): Prop :=  
  s.(visited) == [src] /\ 
  s.(dist) src = Some 0 /\ 
  (forall v e, v <> src -> e ∈ done -> step_aux g e src v -> s.(dist) v = (weight g e)) /\ 
  (forall v, v <> src -> (forall e, e ∈ done -> ~ step_aux g e src v) -> s.(dist) v = None).

#[export]Instance step_invariant_proper: 
  Proper (Sets.equiv ==> eq ==> iff) (fun done s => first_step_invariant done s). 
Proof. 
  unfold Proper, respectful, first_step_invariant.
  intros done1 done2 Heq s1 s2 ?; subst s2.
  split; intros; auto.
  - destruct H as [Hvisited [Hdist [Hstep Hcut]]].
    split; [|split;[|split]]; auto.
    + intros v e Hneq Hein Hstep'.
      apply Hstep; auto. 
      rewrite Heq; auto.
    + intros v Hneq Hnotin.
      apply Hcut; auto. 
      intros; apply Hnotin.
      rewrite <- Heq; auto. 
  - destruct H as [Hvisited [Hdist [Hstep Hcut]]].
    split; [|split;[|split]]; auto.
    + intros v e Hneq Hein Hstep'.
      apply Hstep; auto. 
      rewrite <- Heq; auto.
    + intros v Hneq Hnotin.
      apply Hcut; auto. 
      intros; apply Hnotin.
      rewrite Heq; auto.
Qed.

Theorem Dijkstra_first_step: 
  Hoare (fun s => s = initSt) 
        body 
        (fun _ s => visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s). 
Proof. 
  unfold body. 
  intro_state; hoare_auto_s. 
  2: { subst; exfalso; eapply init_unvisited_reachable; eauto. } subst.  
  unfold select_min_vertex. 
  hoare_auto_s; rename a into u.  
  unfold process_vertex, visit. 
  hoare_auto_s; intro_state. 
  eapply Hoare_bind with (Q := fun _ s => 
  visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s). 
  2: { intros _; intro_state; hoare_auto_s; subst; auto. }
  assert (u = src). {
    destruct H as [_ H].  
    unfold unvisited, initSt in H; simpl in H.
    pose proof H src ltac:(sets_unfold; intros; auto) as Hcon. 
    destruct (eq_dec src src); 
    [|exfalso; apply c; reflexivity]. 
    destruct (eq_dec u src); auto. 
    contradiction. } subst u. 
  hoare_cons (Hoare_forset first_step_invariant _ _ _).  
  {
    (* 初始状态满足循环不变量 *)
    intros; subst; split; [|split; [|split]]; simpl. 
    apply Sets_empty_union. 
    destruct (eq_dec src src); [auto|exfalso; apply c; reflexivity]. 
    intros; contradiction.
    intros; destruct (eq_dec v src); [contradiction|auto]. 
  }
  {
    (* 循环不变量足够证明后条件 *)
    intros; split; [|split]; 
    destruct H2 as [Heq [Hdist [Hinv Hex]]].
    
    - intros v Hv; rewrite Heq in Hv;
      sets_unfold in Hv; subst. 
      rewrite Hdist; split; 
      [eapply min_value_weight_epath_refl; eauto|
      eapply min_value_weight_epath_in_vset_refl]; eauto. 
    - intros v Hv; rewrite Heq in Hv;
      sets_unfold in Hv; subst. 
      destruct (classic (forall e, ~ step_aux g e src v)). 
      + pose proof Hex v ltac:(symmetry; auto)
        ltac:(intros e [x He]; unfold not; intros; 
           eapply step_aux_unique in He; eauto; 
           destruct He; subst; pose proof H1 e; auto). 
        right; split; auto. 
        intros a Ha; exfalso. 
        (* 关于从src出发的限制在[src]顶点集合上的性质1 *)
        destruct Ha as [Hpath Hvalid].  
        apply valid_epath_inv_n1 in Hpath as [[]|[p [u [e [Hcons [Hp Hstep]]]]]]; auto. 
        destruct p; [apply valid_epath_nil_inv in Hp; subst; eapply H1; eauto|].
        pose proof Hvalid (e0 :: p) (e :: nil) u
        ltac:(symmetry; apply nil_cons) ltac:(symmetry; apply nil_cons) Hcons Hp as Hu. 
        rewrite Heq in Hu; sets_unfold in Hu; subst. 
        eapply H1; eauto. 

      + apply not_all_ex_not in H1.   
        destruct H1 as [e He]. 
        apply NNPP in He. 
        pose proof Hinv v e ltac:(symmetry; auto) 
        ltac:(exists v; auto) He. 
        left; split; [|destruct (dist s v); simpl; auto]. 
        exists (e::nil); split; [|unfold epath_weight; simpl; rewrite Z_op_plus_O_r; auto].

        (* 关于从src出发的限制在[src]顶点集合上的性质2 *)
        split; [apply is_epath_through_vset_single; auto|intros q Hq].
        destruct Hq as [Hpath Hvalid].  
        apply valid_epath_inv_n1 in Hpath as [[]|[p [u [a [Hcons [Hp Hstep]]]]]]; subst; auto. 
        contradiction.
        destruct p; [apply valid_epath_nil_inv in Hp; subst|]. 
        eapply no_multiple_edge in He; eauto; subst; apply le_refl. 
        pose proof Hvalid (e0 :: p) (a :: nil) u
        ltac:(symmetry; apply nil_cons) ltac:(symmetry; apply nil_cons) ltac:(auto) Hp as Hu. 
        rewrite Heq in Hu; sets_unfold in Hu; subst. 
        eapply no_multiple_edge in He; eauto; subst; simpl. 
        rewrite app_comm_cons. 
        rewrite epath_weight_app_assoc. 
        rewrite <- Z_op_plus_O_l at 1. 
        eapply Z_op_plus_mono; [eapply valid_epath_non_neg; eauto|apply Z_op_le_refl]. 
    - intros u v Hu Hv. 
      rewrite Heq in Hu; sets_unfold in Hu; subst. 
      rewrite Hdist. 
      destruct (classic (v = src)); [subst; rewrite Hdist; simpl; lia|]. 
      destruct (classic (exists e, step_aux g e src v)) as [[e He] | Hno_edge]. 
      + pose proof Hinv v e ltac:(symmetry; auto)
        ltac:(exists v; auto) He as Hs2v; rewrite Hs2v. 
        apply weight_nonneg. 
      + pose proof Hex v ltac:(symmetry; auto)
        ltac:(unfold not; intros; eapply Hno_edge; eauto) as Hs2v. 
        rewrite Hs2v; simpl; auto. 
  }
  {
    (* 不变性 *)
    intros done e Hdone Hstep Hnotin.
    intro_state; destruct H2 as [Heq [Hdist [Hinv Hex]]]. 
    unfold relax_edge. 
    hoare_auto_s. subst.
    split; [|split; [|split]]. 
    * simpl; auto. 
    * simpl; unfold t_set. 
      destruct (equiv_dec a src); auto.
      assert (a = src) by apply e0; subst.
      exfalso; eapply no_self_loop; eauto.
    * intros v e' Hneq He' Hstep'. 
      simpl. 
      destruct (classic (e = e')); [subst|]. 
      + assert (a = v) by (eapply step_aux_unique; eauto); subst. 
        unfold t_set; destruct (equiv_dec v v); [clear e|exfalso; apply c; reflexivity]. 
        rewrite Hdist. 
        rewrite Z_op_plus_O_l. 
        destruct (classic (forall e, e ∈ done -> ~ step_aux g e src v)). 
        - rewrite Hex; auto. 
          apply Z_op_min_le_l. 
        - apply not_all_ex_not in H1 as [e H1].
          apply imply_to_and in H1 as [Hein H1]; apply NNPP in H1.
          assert (e = e') by (eapply no_multiple_edge; eauto); subst.
          erewrite Hinv; eauto. 
          destruct (weight g e'); simpl in *; [contradiction|auto]. 

      + assert (a <> v) by (unfold not; intros; subst; exfalso; 
      apply H1; eapply no_multiple_edge; eauto). 
        unfold t_set; destruct (equiv_dec a v); 
        [exfalso; apply H4; apply e0|apply Hinv; auto]. 
        destruct He'; [auto|contradiction].
    * intros v Hneq Hcut. 
      simpl. unfold t_set. 
      destruct (equiv_dec a v); auto. 
      + rewrite Hdist. 
        rewrite Z_op_plus_O_l. 
        assert (a = v) by apply e0; subst. 
        pose proof Hcut e ltac:(right; reflexivity). 
        contradiction.
      + apply Hex; intros; auto. 
        apply (Hcut e0 ltac:(left; auto)).
  } 
Qed.

Definition relax_step_invariant (u: V) (s0: St) (done: E -> Prop) (s: St): Prop := 
  s.(visited) == s0.(visited) /\ 
  s.(dist) u = s0.(dist) u /\ 
  (forall v e, v <> u -> e ∈ done -> step_aux g e u v -> 
    s.(dist) v = Z_op_min (s0.(dist) v) (Z_op_plus (s0.(dist) u) (weight g e))) /\ 
  (forall v, v <> u -> (forall e, e ∈ done -> ~ step_aux g e u v) -> 
    s.(dist) v = s0.(dist) v).  

#[export]Instance relax_step_invariant_proper (u: V) (s0: St): 
  Proper (Sets.equiv ==> eq ==> iff) (relax_step_invariant u s0). 
Proof. 
  unfold Proper, respectful, relax_step_invariant.
  intros done1 done2 Heq s1 s2 ?; subst s2.
  split; intros; auto.
  - destruct H as [Hvisited [Hdist [Hstep Hcut]]].
    split; [|split;[|split]]; auto.
    + intros v e Hneq Hein Hstep'.
      apply Hstep; auto. 
      rewrite Heq; auto.
    + intros v Hneq Hnotin.
      apply Hcut; auto. 
      intros; apply Hnotin.
      rewrite <- Heq; auto. 
  - destruct H as [Hvisited [Hdist [Hstep Hcut]]].
    split; [|split;[|split]]; auto.
    + intros v e Hneq Hein Hstep'.
      apply Hstep; auto. 
      rewrite <- Heq; auto.
    + intros v Hneq Hnotin.
      apply Hcut; auto. 
      intros; apply Hnotin.
      rewrite Heq; auto.
Qed.

(* 循环不变量足够推出后条件 *)
Theorem invariant_implies_final: 
  forall u s0 s1,
    visited_dist_final s0 -> 
    unvisited_dist_optimal s0 -> 
    visited_le_unvisited s0 -> 
    min_object_of_subset Z_op_le (fun v : V => unvisited s0 v) (dist s0) u ->
    s1 = s0 <| visited ::= (fun vs : V -> Prop => vs ∪ [u]) |> ->
    forall s, 
      relax_step_invariant u s1 (fun e : E => exists v : V, step_aux g e u v) s ->
      visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s.
Proof.  
  intros u s0 s1 Hfinal Hoptimal Hcross Hmin Hs1 s2 [Hvu [Hdu [Hinv Hex]]]. 
  (* 第一个后条件 *)
  assert (visited_dist_final s2) as Hfinal'.
  {
    intros v Hv. 
    assert (min_value_weight_epath g src v (dist s2 v)) as Hpre. {
    (* 前项：是全局最小值 *)
    rewrite Hvu, Hs1 in Hv.
    destruct Hv as [Hv_old | Hv_new].
    + destruct (classic (v = u)); [subst; rewrite Hdu; apply Hfinal; auto |].
      destruct (classic (exists e, step_aux g e u v)) as [[e He] | Hno_edge].
      * (* 我们需要说明已经被访问过的点v，在u的松弛操作中，不会变得更小。 *)
        pose proof Hinv v e H ltac:(exists v; auto) He as Hs2v. 
        pose proof Hfinal v Hv_old as [Hs0v _]. 
        rewrite Hs1 in Hs2v; simpl in Hs2v. 
        assert (Z_op_le (dist s0 v) (Z_op_plus (dist s0 u) (weight g e))) as Hle. {
          pose proof Hoptimal u (ltac:(unfold not; intros; apply Hmin; auto)). 
          eapply dijkstra_visited_keep; eauto. 
        }  
        rewrite Hs2v.
        rewrite (Z_op_le_min_l _ _ Hle); apply Hfinal; auto.  

      * assert (H_no: forall e, e ∈ (fun e0 : E => exists v0 : V, step_aux g e0 u v0) -> ~ step_aux g e u v).
        { intros e_any _ H_step; apply Hno_edge; exists e_any; auto. }
        pose proof (Hex v H H_no) as H_eq.
        rewrite H_eq. 
        rewrite Hs1; simpl; apply Hfinal; auto. 
        
    + sets_unfold in Hv_new; subst. 
      rewrite Hdu; simpl.
      eapply dijkstra_greedy_choice_correct; eauto. 
      (* 这里是贪心选择正确性的图论引理 *) }
    split; auto.
    (* 后项：也是已访问集合上的最小值 *)
    rewrite Hvu in Hv; rewrite Hs1 in Hv; simpl in Hv. 
    destruct Hv; [|sets_unfold in H; subst v].  
    * pose proof Hfinal v H as []. 
      eapply min_value_weight_epath_unique in Hpre; eauto. 
      rewrite <- Hpre. 
      pose proof @min_value_weight_epath_in_vset_exist _ _ _ pg gv g
      _ _ _ _ _ _ _ weight_nonneg src v (visited s2) as [z Hz]. 
      eapply min_value_weight_epath_in_vset_determin in Hz as Heq; eauto. 
      subst; auto. 
      rewrite Hvu; rewrite Hs1; simpl; left; auto. 
    * assert (~ visited s0 u) by (apply Hmin). 
      pose proof Hoptimal u H. 
      rewrite Hdu. 
      rewrite Hs1; simpl. 
      erewrite floyd_warshall_update_end in H0.
      rewrite Hvu, Hs1; simpl; auto. 
      Unshelve. auto. 
      intros; eapply valid_epath_non_neg; eauto. 
  } 
  (* 第二个后条件 *)
  assert (unvisited_dist_optimal s2) as Hoptimal'.
  { 
    unfold unvisited_dist_optimal. intros v Hv_unvis.       
    pose proof Hoptimal v 
    ltac:(unfold not; intros; apply Hv_unvis; rewrite Hvu, Hs1; left; auto).
    assert (Hneq: v <> u). 
    { unfold not; intro; subst. apply Hv_unvis. rewrite Hvu. right. reflexivity. }
    
    destruct (classic (exists e, step_aux g e u v)) as [[e He] | Hno_edge].
    + assert (He_in: e ∈ (fun e => exists v, step_aux g e u v)) by (exists v; auto).
      pose proof (Hinv v e Hneq He_in He) as H_update.
      rewrite H_update. 
      rewrite Hvu; rewrite Hs1; simpl.
      eapply dijkstra_relax_edge_correct; eauto. 
      destruct Hmin; auto. 
      rewrite Hvu in Hv_unvis; rewrite Hs1 in Hv_unvis; simpl in Hv_unvis. 
      unfold not; intros; apply Hv_unvis; left; auto. 
      
    + assert (H_no: forall e, e ∈ (fun e0 : E => exists v0 : V, step_aux g e0 u v0) -> ~ step_aux g e u v).
      { intros e_any _ H_step; apply Hno_edge; exists e_any; auto. }
      pose proof (Hex v Hneq H_no) as H_eq.
      rewrite H_eq.
      rewrite Hvu; rewrite Hs1; simpl; auto.
      eapply dijkstra_relax_edge_correct'; eauto. 
      destruct Hmin; auto. 
      rewrite Hvu in Hv_unvis; rewrite Hs1 in Hv_unvis; simpl in Hv_unvis. 
      unfold not; intros; apply Hv_unvis; left; auto. 
  } 
  split; [|split]; auto.
  (* 第三个后条件，可以用到前两个条件的结论简化证明 *)
  intros x y Hx Hy. 
  rewrite Hvu in Hx, Hy. 
  rewrite Hs1 in Hx, Hy; simpl in Hx, Hy. 
  destruct Hmin as [Huvalid Huismin]. 
  pose proof Huismin y
  ltac:(unfold unvisited; unfold not; sets_unfold; intros; apply Hy; left; auto). 
  assert (Z_op_le (dist s2 u) (dist s2 y)). 
  {
    rewrite Hdu; rewrite Hs1; simpl. 
    assert (Hneq: y <> u) by (unfold not; intros; subst; apply Hy; right; reflexivity). 
    destruct (classic (exists e, step_aux g e u y)) as [[e He] | Hno_edge]. 
    + pose proof Hinv y e Hneq ltac:(exists y; auto) He as H_update.
      rewrite H_update.
      rewrite Hs1; simpl; auto.
      apply Z_op_le_min_imply; auto. 
      rewrite <- Z_op_plus_O_r at 1. 
      apply Z_op_plus_mono; auto.
    + pose proof Hex y Hneq ltac:(unfold not; intros; eapply Hno_edge; eauto) as H_eq.
      rewrite H_eq.
      rewrite Hs1; simpl; auto. 
  } 
  destruct (classic (x = u)); [subst; auto|]. 
  eapply Z_op_le_trans; eauto. 
  rewrite Hdu; rewrite Hs1; simpl; auto. 
  assert (x ∈ visited s0) as Hxvis 
  by (destruct Hx; [auto|sets_unfold in H2; subst; contradiction]). 
  pose proof Hfinal x Hxvis as [Hxold _]. 
  pose proof Hfinal' x ltac:(rewrite Hvu; rewrite Hs1; simpl; left; auto) as [Hxnew _]. 
  eapply min_value_weight_epath_unique in Hxold; eauto. 
  rewrite Hxold. 
  pose proof Hcross x u Hxvis Huvalid. auto. 
Qed. 

Theorem Dijkstra_visited_dist_final: 
  Hoare (fun s => s = initSt) 
        Dijkstra 
        (fun _ s => visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s). 
Proof. 
  unfold Dijkstra. 
  eapply (proj2 (Hoare_equiv_iff _ _ _ _ (repeat_break_unfold _ tt))).
  eapply Hoare_bind with (Q := fun _ s => visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s). 
  apply Dijkstra_first_step. 
  intros [[]| []].
  unfold body. 
  2: { apply Hoare_ret'; auto. }
  eapply Hoare_repeat_break' with 
  (P := fun _ s => visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s); intros _ . 
  - hoare_auto_s. 
    * intro_state. 
      hoare_auto_s. 
      unfold select_min_vertex. 
      hoare_auto_s; rename a into u. 
      unfold process_vertex, visit. 
      hoare_auto_s; intro_state. 
      rename H1 into Hmin; rename H2 into Hs1. 
      eapply Hoare_bind with (Q := fun _ s => visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s). 
      2: { intros _; intro_state; hoare_auto_s; subst; auto.  } 
      destruct H as [Hfinal [Hoptimal Hcross]].
      hoare_cons (Hoare_forset (relax_step_invariant u s1) _ _ _).
      {
        (* 初始状态满足循环不变量 *)
        intros; subst; split; [|split; [|split]]; simpl; auto.
        reflexivity.
        intros; contradiction.
      }
      { 
        (* 不变量足够证明后条件 *)
        intros; eapply invariant_implies_final; eauto. 
      }
      {
        (* 不变性 *)
        intros done e Huniv Hein Hnotin.
        intro_state. 
        destruct H as [Hvu [Hdu [Hinv Hex]]].
        unfold relax_edge. hoare_auto_s. subst.
        split; [|split; [|split]].
        - simpl; auto.
        - simpl; unfold t_set; destruct (equiv_dec a u).
          + assert (a = u) by apply e0; subst. 
            exfalso; eapply no_self_loop; eauto.
          + auto.
        - intros v e' Hneq He'in Hstep'.
          simpl; unfold t_set.
          destruct (classic (e = e')); subst.
          + assert (a = v) by (eapply step_aux_unique_end; eauto); subst a. 
            destruct (equiv_dec v v); [|exfalso; apply c; reflexivity].
            assert (dist s2 v = dist s0 v) as Hveq. 
            { apply Hex; auto; unfold not; intros; 
              eapply no_multiple_edge in Hstep'; eauto; subst; auto. }
            rewrite Hveq; rewrite Hdu. 
            reflexivity.
          + assert (a <> v). 
            { unfold not; intros; subst. 
              eapply no_multiple_edge in Hstep'; eauto; subst; auto. }
            destruct (equiv_dec a v); [exfalso; auto|].
            apply Hinv; auto. 
            destruct He'in; auto; contradiction.
        - intros v Hneq Hnot.
          simpl; unfold t_set; destruct (equiv_dec a v).
          + assert (a = v) by apply e0; subst a.
            exfalso. apply (Hnot e); auto. right; reflexivity.
          + apply Hex; auto. intros e' He'in Hstep'.
            eapply Hnot; eauto. left; auto.
      }
    * intro_state. 
      hoare_auto_s. 
  - hoare_auto_s. 
    * intro_state. 
      hoare_auto_s. 
      unfold select_min_vertex. 
      hoare_auto_s; rename a into u. 
      unfold process_vertex, visit. 
      hoare_auto_s; intro_state. 
      eapply Hoare_bind with (Q := fun _ s => visited_dist_final s /\ unvisited_dist_optimal s /\ visited_le_unvisited s). 
      2: { intros _; intro_state; hoare_auto_s; subst; auto.  } 
      destruct H as [Hfinal [Hoptimal Hcross]].
      hoare_cons (Hoare_forset (relax_step_invariant u s1) _ _ _).
      {
        (* 初始状态满足循环不变量 *)
        intros; subst; split; [|split; [|split]]; simpl; auto.
        reflexivity.
        intros; contradiction.
      }
      { 
        (* 不变量足够证明后条件 *)
        intros; eapply invariant_implies_final; eauto. 
      }
      {
        (* 不变性 *)
        intros done e Huniv Hein Hnotin.
        intro_state. 
        destruct H as [Hvu [Hdu [Hinv Hex]]].
        unfold relax_edge. hoare_auto_s. subst.
        split; [|split; [|split]].
        - simpl; auto.
        - simpl; unfold t_set; destruct (equiv_dec a u).
          + assert (a = u) by apply e0; subst. 
            exfalso; eapply no_self_loop; eauto.
          + auto.
        - intros v e' Hneq He'in Hstep'.
          simpl; unfold t_set.
          destruct (classic (e = e')); subst.
          + assert (a = v) by (eapply step_aux_unique_end; eauto); subst a. 
            destruct (equiv_dec v v); [|exfalso; apply c; reflexivity].
            assert (dist s2 v = dist s0 v) as Hveq. 
            { apply Hex; auto; unfold not; intros; 
              eapply no_multiple_edge in Hstep'; eauto; subst; auto. }
            rewrite Hveq; rewrite Hdu. 
            reflexivity.
          + assert (a <> v). 
            { unfold not; intros; subst. 
              eapply no_multiple_edge in Hstep'; eauto; subst; auto. }
            destruct (equiv_dec a v); [exfalso; auto|].
            apply Hinv; auto. 
            destruct He'in; auto; contradiction.
        - intros v Hneq Hnot.
          simpl; unfold t_set; destruct (equiv_dec a v).
          + assert (a = v) by apply e0; subst a.
            exfalso. apply (Hnot e); auto. right; reflexivity.
          + apply Hex; auto. intros e' He'in Hstep'.
            eapply Hnot; eauto. left; auto.
      }
    * intro_state. 
      hoare_auto_s; subst; auto. 
  Unshelve. auto. auto.
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
    apply Hoare_ret'; intros; exact I.
  - apply Hoare_assume_bind.
    apply Hoare_ret'.
    intros s [Hcond _].
    apply break_cond_implies_reachable_visited; auto. 
Qed.

Theorem Dijkstra_correct: 
  Hoare (fun s => s = initSt) 
        Dijkstra 
        (fun _ s => distance_correct s). 
Proof.   
  eapply Hoare_conseq_post. 
  2: {
    apply Hoare_conj.
    apply Dijkstra_reachable_visited.
    apply Dijkstra_visited_dist_final.
  }
  simpl; intros _ s [Hreachable [Hfinal [Hoptimal Hcross]]]. 
  intros u Hu. 
  apply Hfinal; auto.
Qed.

End Dijkstra.
