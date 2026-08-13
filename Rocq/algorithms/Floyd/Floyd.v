Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From GraphLib Require Import floyd.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.


Section Floyd.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {step_valid: StepValid G V E}
        {step_aux_unique: StepUniqueDirected G V E}
        (g: G)
        {g_valid: gvalid g}
        {eq_dec: EqDec (V * V) eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

(* floyd算法允许存在负权，但是不允许存在负权回路 *)

Context {non_neg_loop: forall u p, valid_epath g u p u -> Z_op_le (Some 0) (epath_weight g p)}.

Record St: Type := mkSt {
  dist: (V * V) -> option Z;
}.

Instance: Settable St := settable! mkSt <dist>.


(** 松弛操作：dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]) *)
Definition update_dist (i j k: V): program St unit :=
  update' (fun s => s <| dist ::= fun dist0 =>
    (i, j) !-> (Z_op_min (dist0 (i, j)) (Z_op_plus (dist0 (i, k)) (dist0 (k, j)))); dist0 |>).

Definition Floyd_j (k: V) (j: V): program St unit :=
  forset (fun v => vvalid g v) (fun i =>
    update_dist i j k).

(** 对于固定的中间点k，遍历所有顶点对(i,j)进行松弛 *)
Definition Floyd_k (k: V): program St unit :=
  forset (fun v => vvalid g v) (Floyd_j k).

(** Floyd主算法：遍历所有可能的中间点k *)
Definition Floyd: program St unit :=
  forset (fun v => vvalid g v) Floyd_k.

Definition Floyd_loop_invariant (done: V -> Prop) (s: St): Prop :=
  forall u v,
    vvalid g u -> vvalid g v ->
    min_value_weight_epath_in_vset g u v done (s.(dist) (u, v)).

Definition distance_correct (s: St): Prop :=
  forall u v, vvalid g u -> vvalid g v -> min_value_weight_epath g u v (s.(dist) (u, v)).

(* 一般用邻接矩阵储存的图数据能够满足前条件 *)
Definition initialized_state (s: St): Prop := 
  Floyd_loop_invariant ∅ s.

#[export] Instance Floyd_loop_invariant_Proper:
  Proper (Sets.equiv ==> eq ==> iff) Floyd_loop_invariant.
Proof.
  unfold Proper, respectful, Floyd_loop_invariant.
  intros done1 done2 Heq s1 s2 ?; subst s2.
  split; intros H u v Hu Hv; specialize (H u v Hu Hv); 
  (unfold min_value_weight_epath_in_vset in *; 
   eapply min_default_eq_forward; eauto; 
   [apply Z_op_le_TotalOrder| 
   intros p Hp; exists p; split; auto; 
   [try rewrite Heq; auto; try rewrite <- Heq; auto|
   destruct (epath_weight g p); simpl; [lia|auto]]|
   intros p Hp; exists p; split; auto; 
   [try rewrite Heq; auto; try rewrite <- Heq; auto|
   destruct (epath_weight g p); simpl; [lia|auto]]]).
Qed.

(*          
                            Column index
             0 ----------------- j ----------------- n
          ┌─────────────────────┬─────┬─────────────────────┐
          │ ################### │  #  │  . . . . . . . . .  │ 
   done_i │ ####### (2) ####### │ (1) │  . . .  (3)  . . .  │ <- done_i(已处理行)
          │ ################### │  #  │  . . . . . . . . .  │
          ├─────────────────────┼─────┼─────────────────────┤
Row index │ ####### (2) ####### │ ★  │  . . . (3) . . . .  │ <- i(当前处理行)
          ├─────────────────────┼─────┼─────────────────────┤
          │ ################### │  .  │  . . . . . . . . .  │
          │ ####### (2) ####### │ (4) │  . . .  (3)  . . .  │
   todo_i │ ################### │  .  │  . . . . . . . . .  │ <- 未处理行
          └─────────────────────┴─────┴─────────────────────┘
                   ^                ^
                done_j(已处理行)     j(当前处理列)

   图例说明:
   [★] : 当前单元格 (u, v) 即 (i, j)
   [#] : 已处理区域 
   [.] : 待处理区域
   (1) : 第j列中已经处理完成的区域
   (2) : 已经处理完成的列区域
   (3) : 尚未处理的列区域
   (4) : 第j列中尚未处理的区域 

   循环不变量定义：
   i-循环不变量：
    (1) (2) 区域是已经处理完成的 done_k ∪ [k] 上的最小值，(3) (4) 区域是未处理的 done_k 上的最小值，★是单步更新。
   j-循环不变量：
    (2) 区域是已经处理完成的 done_k ∪ [k] 上的最小值，(1) (3) (4) 区域是未处理的 done_k 上的最小值，j列是单步更新。
   k-循环不变量:
    (1) (2) (3) (4)区域是 done_k 上的最小值。
    
*)

Definition Floyd_i_loop_invariant 
  (done_k: V -> Prop) (k: V) (done_j: V -> Prop) (j: V) (done_i: V -> Prop) (s: St): Prop :=
  forall u v,
    vvalid g u -> vvalid g v ->
    (* 区域 (1) *)
    (u ∈ done_i /\ v = j -> 
      min_value_weight_epath_in_vset g u v (done_k ∪ [k]) (s.(dist) (u, v))) /\
    (* 区域 (2) *)
    (v ∈ done_j -> 
      min_value_weight_epath_in_vset g u v (done_k ∪ [k]) (s.(dist) (u, v))) /\
    (* 区域(3) (4) *)
    ((~ u ∈ done_i \/ v <> j) /\ ~ v ∈ done_j -> 
      min_value_weight_epath_in_vset g u v done_k (s.(dist) (u, v))).

#[export] Instance Floyd_i_loop_invariant_Proper k done_j j done_k:
  Proper (Sets.equiv ==> eq ==> iff) (Floyd_i_loop_invariant done_k k done_j j).
Proof.
  unfold Proper, respectful, Floyd_loop_invariant.
  intros done1 done2 Heq s1 s2 ?; subst s2.
  split; intros H u v Hu Hv; specialize (H u v Hu Hv).
  - destruct H as [Hcase1 [Hcase2 Hcase3]]. 
    repeat split; intros; auto. 
    * apply Hcase1; rewrite Heq; auto. 
    * apply Hcase3; rewrite Heq; auto. 
  - destruct H as [Hcase1 [Hcase2 Hcase3]]. 
    repeat split; intros; auto. 
    * apply Hcase1; rewrite <- Heq; auto. 
    * apply Hcase3; rewrite <- Heq; auto. 
Qed. 

Definition Floyd_j_loop_invariant 
  (done_k: V -> Prop) (k: V) (done_j: V -> Prop) (s: St): Prop :=
  forall u v,
    vvalid g u -> vvalid g v ->
    (*区域 (2) *)
    (v ∈ done_j -> 
      min_value_weight_epath_in_vset g u v (done_k ∪ [k]) (s.(dist) (u, v))) /\
    (*区域 (1) (3) (4) *)
    (~ v ∈ done_j -> 
      min_value_weight_epath_in_vset g u v done_k (s.(dist) (u, v))).

#[export] Instance Floyd_j_loop_invariant_Proper k done_k:
  Proper (Sets.equiv ==> eq ==> iff) (Floyd_j_loop_invariant done_k k).
Proof.
  unfold Proper, respectful, Floyd_loop_invariant.
  intros done1 done2 Heq s1 s2 ?; subst s2.
  split; intros H u v Hu Hv; specialize (H u v Hu Hv);
  (split; intros; auto;
  try apply H; try rewrite Heq; auto; try rewrite <- Heq; auto).
Qed. 

(** ===== i循环的正确性 ===== *)

Theorem Floyd_i_body_correct:
  forall done_k k done_j j done_i i,
    vvalid g i -> vvalid g j -> vvalid g k ->
    ~ i ∈ done_i ->
    ~ j ∈ done_j ->
    Hoare (fun s => Floyd_i_loop_invariant done_k k done_j j done_i s)
          (update_dist i j k)
          (fun _ s => Floyd_i_loop_invariant done_k k done_j j (done_i ∪ [i]) s).
Proof.
  intros done_k k done_j j done_i i Hi Hj Hk Hnotin_i Hnotin_j.
  unfold update_dist.
  intro_state.
  hoare_auto_s.
  subst; rename s0 into s.
  unfold Floyd_i_loop_invariant in *. 
  intros u v Hu Hv.
  repeat split; intros.
  - destruct H0 as [Hin Heq]; subst v. 
    destruct (classic (u = i)) as [Heq | Hneq]; 
    [subst|destruct Hin; try congruence].
    + (* 区域 ★ *) (* 这是最困难的进行了松弛的单步，需要用到松弛定理 *)
      (* 要获取ik和kj的最小值，需要对k的取值范围进行讨论 *)
      simpl; unfold t_set; destruct (equiv_dec (i, j) (i, j)); [clear e|congruence].

      pose proof (H i j Hu Hv) as [_ [_ Hij_old]]. 
      pose proof (Hij_old ltac:(tauto)) as Hij_done_k; clear Hij_old.
      
      pose proof (H i k Hi Hk) as [Hij_ik_1 [Hij_ik_2 Hij_ik_3]].
      (* 提取出ik的距离 *)
      assert (Hik_dk_union_k: min_value_weight_epath_in_vset g i k (done_k) (s.(dist) (i, k))).
      { destruct (classic (k ∈ done_j)).
        * eapply floyd_warshall_update_end. 
          apply Hij_ik_2; auto.
        * apply Hij_ik_3; split; [left|]; auto. }
      
      (* 提取出kj的距离 *)
      pose proof (H k j Hk Hv) as [Hkj_1 [Hkj_2 Hkj_3]].
      assert (Hkj_dk_union_k: min_value_weight_epath_in_vset g k j (done_k) (s.(dist) (k, j))).
      { destruct (classic (k ∈ done_i)).
        * eapply floyd_warshall_update_start. 
          apply Hkj_1; split; auto.
        * apply Hkj_3; split; [left|]; auto. }
      
      eapply floyd_warshall_step_spec; eauto.

    + (* 区域(1) *)
      pose proof (H u j Hu Hv) as [Huj _]. 
      pose proof Huj ltac:(split; auto). 
      simpl; unfold t_set; destruct (equiv_dec (i, j) (u, j)) eqn: Heq; [congruence|auto].
  - (* 区域(2) *)
    pose proof (H u v Hu Hv) as [_ [Huv _]]. 
    simpl; unfold t_set; destruct (equiv_dec (i, j) (u, v)) eqn: Heq; [congruence|auto].
  
  - (* 区域(3) (4) *)
    destruct H0 as [H1 H2]. 
    assert (Hneq_uv: u <> i \/ v <> j). {
      destruct H1; [left|right]; unfold not; intros; subst. 
      apply H0; right; reflexivity. congruence. }
    simpl; unfold t_set.
    destruct (equiv_dec (i, j) (u, v)) eqn: Heq; 
    [destruct Hneq_uv; congruence|clear Heq c].
    pose proof (H u v Hu Hv) as [_ [_ Huv]]. 
    assert (Hpre1: (~ u ∈ done_i \/ v <> j)). {
      destruct H1; [|auto]. 
      left; unfold not; intros; apply H0; left; auto. } 
    apply Huv; auto.
  Unshelve. auto. auto. auto. auto. auto. auto.
Qed.

(** ===== j循环的正确性 ===== *)

Theorem Floyd_j_body_correct:
  forall done_k k done_j j,
    vvalid g j -> vvalid g k ->
    ~ j ∈ done_j ->
    Hoare (fun s => Floyd_j_loop_invariant done_k k done_j s)
          (Floyd_j k j)
          (fun _ s => Floyd_j_loop_invariant done_k k (done_j ∪ [j]) s).
Proof.
  intros done_k k done_j j Hj Hk Hnotin_j.
  unfold Floyd_j.
  hoare_cons (Hoare_forset (Floyd_i_loop_invariant done_k k done_j j) _ _ _).
  
  - intros s Hinv u v Hu Hv; repeat split; intros;
    [| destruct (Hinv u v Hu Hv) as [Huv _]|destruct (Hinv u v Hu Hv) as [_ Huv]]; tauto.
  
  - intros _ s Hinv u v Hu Hv; split; intros.
    + destruct H as [H | H].
      * destruct (Hinv u v Hu Hv) as [_ [Huv _]]; auto.
      * sets_unfold in H; subst.
        destruct (Hinv u v Hu Hv) as [Huv _].
        apply Huv; split; [| reflexivity].
        sets_unfold; auto.
    + sets_unfold in H. 
      destruct (Hinv u v Hu Hv) as [_ [_ Huv]].
      apply Huv; split; auto.
  - intros done_i i Hsub Hi Hnotin_i.
    apply Floyd_i_body_correct; auto.
Qed.

(** ===== k循环的正确性 ===== *)
Theorem Floyd_k_body_correct:
  forall done_k k,
    k ∈ (fun v => vvalid g v) ->
    Hoare (fun s => Floyd_loop_invariant done_k s)
          (Floyd_k k)
          (fun _ s => Floyd_loop_invariant (done_k ∪ [k]) s).
Proof.
  intros done_k k Hk. 
  sets_unfold in Hk. 
  unfold Floyd_k.
  hoare_cons (Hoare_forset (Floyd_j_loop_invariant done_k k) _ _ _). 
  - intros s Hinv u v Hu Hv.
    split; intros; [sets_unfold in H; tauto|apply Hinv; auto].
  - intros _ s Hinv u v Hu Hv; destruct (Hinv u v Hu Hv) as [H _]; auto. 
  - intros done_j j Hsub Hj Hnotin.
    sets_unfold in Hj.
    apply Floyd_j_body_correct; auto.
Qed.

(* 终止状态的对齐 *)

Lemma valid_epath_end_valid: 
  forall u p v,
    p <> nil ->
    valid_epath g u p v ->
    vvalid g v.
Proof.
  intros.
  apply exists_last in H as [q []]; subst. 
  apply valid_epath_snoc_inv in H0 as [? [_ ?]]. 
  eapply step_vvalid2; eauto. 
Qed.

Lemma is_epath_through_universal:
  forall u v,
    (fun p => is_epath_through_vset g u p v (vvalid g)) == 
    (fun p => valid_epath g u p v).
Proof.
  intros.
  split; intros.
  - destruct H; auto.
  - split; auto.
    intros.
    apply (valid_epath_end_valid u p1); auto.
Qed.

Theorem final_state_correct:
  forall s u v,
    vvalid g u -> vvalid g v ->
    min_value_weight_epath_in_vset g u v (vvalid g) (s.(dist) (u, v)) ->
    min_value_weight_epath g u v (s.(dist) (u, v)).
Proof.
  intros s u v Hu Hv H.
  unfold min_value_weight_epath_in_vset in H.
  destruct H as [[[p []]]|[]].
  * left; split; auto.
    exists p; split; auto.
    rewrite <- is_epath_through_universal.
    auto.
  * right; split; auto.
    intros; apply H.
    rewrite is_epath_through_universal.
    auto.
Qed.

(** ===== 主定理 =====
    
    证明 Floyd 算法的正确性：
    如果初始状态满足空集上的循环不变量，
    则算法结束后，dist 数组正确记录了所有点对之间的最短距离。
*)

Theorem Floyd_correct: 
  Hoare initialized_state
        Floyd
        (fun _ s => distance_correct s).
Proof.
  unfold Floyd.
  hoare_cons (Hoare_forset Floyd_loop_invariant _ _ _).
  - intros _ s Hinit u v Hu Hv; apply final_state_correct; auto.
  - intros done k Hsub Hk Hnotin.
    apply Floyd_k_body_correct; auto.
Qed.


End Floyd.