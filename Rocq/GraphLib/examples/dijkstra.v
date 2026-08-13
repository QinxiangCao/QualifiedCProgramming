Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From GraphLib Require Import floyd.
From MaxMinLib Require Import MaxMin Interface.
From ListLib Require Import Base.Inductive.

Import SetsNotation.

Local Open Scope sets.
Local Open Scope Z.

Section dijkstra.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {step_valid: StepValid G V E}
        {step_aux_unique: StepUniqueDirected G V E}
        {simple_graph: SimpleGraph G V E}
        (g: G)
        {g_valid: gvalid g}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

Context {src: V}.

(* Dijkstra成立的充分条件：没有负边 *)
Context {weight_nonneg: forall e, Z_op_le (Some 0) (weight g e)}. 

(* 基于没有负边的一些简单事实 *)
Lemma non_neg_epath: 
  forall u p v, valid_epath g u p v -> Z_op_le (Some 0) (epath_weight g p).
Proof.
  intros u p v Hvalid. 
  revert u v Hvalid.
  induction p; intros.
  - simpl. lia.
  - apply valid_epath_cons_inv in Hvalid as [w [Hstep Hrest]]. 
    pose proof IHp w v Hrest. 
    pose proof weight_nonneg a. 
    rewrite epath_weight_cons.
    destruct (epath_weight g p); destruct (weight g a); simpl in *; try lia.
Qed.

Lemma non_neg_loop: 
  forall u p, valid_epath g u p u -> Z_op_le (Some 0) (epath_weight g p). 
Proof. intros; eapply non_neg_epath; eauto. Qed.

Lemma valid_epath_non_neg:
  forall u p v, 
    valid_epath g u p v ->  
    Z_op_le (Some 0) (epath_weight g p).
Proof.  
  eapply valid_epath_ind_1n; eauto. 
  - intros; simpl; lia.
  - intros; rewrite epath_weight_cons.
    pose proof weight_nonneg e. 
    destruct (weight g e); destruct (epath_weight g p); simpl in *; auto. 
    lia. 
Qed.

Lemma min_value_weight_epath_refl: 
  forall v, 
    min_value_weight_epath g v v (Some 0). 
Proof.
  intros; left; split; [|simpl; auto]. 
  exists nil; split; [|unfold epath_weight; simpl; auto]. 
  split; [apply valid_epath_empty|].
  intros. 
  rewrite epath_weight_nil. 
  apply (valid_epath_non_neg v _ v); auto. 
Qed. 

Lemma min_value_weight_epath_in_vset_refl: 
  forall v vset,
    min_value_weight_epath_in_vset g v v vset (Some 0).
Proof.
  intros; left; split; [|simpl; auto].
  exists nil; split; [|unfold epath_weight; simpl; auto].
  split; [split; [apply valid_epath_empty|]|].
  * intros.
    destruct p1; destruct p2; try contradiction. 
    exfalso; eapply nil_cons; eauto. 
  * intros. 
    rewrite epath_weight_nil. 
    apply (valid_epath_non_neg v _ v). 
    destruct H; auto. 
Qed.


Fact nat_min_bounded: forall n (P: nat -> Prop),
  (exists m, (m <= n)%nat /\ P m /\ forall k, (k < m)%nat -> ~ P k) \/ 
  (forall m, (m <= n)%nat -> ~ P m).
Proof.
  intros n P0.
  induction n as [|n IH].
  - destruct (classic (P0 0%nat)) as [H0 | H0].
    + left. exists 0%nat. split; [lia|]. split; [exact H0|]. 
      intros k Hk; lia.
    + right. intros m Hm. assert (m = 0%nat) by lia. subst. exact H0.
  - destruct IH as [[m [Hle [Hpm Hmin]]] | Hnone].
    + left. exists m. split; [lia|]. split; [exact Hpm|]. exact Hmin.
    + destruct (classic (P0 (S n))) as [Hsn | Hsn].
      { left. exists (S n). split; [lia|]. split; 
        [exact Hsn|intros; apply Hnone; lia]. }
      { right. intros m Hm. destruct (classic (m = S n)) as [Heq | Hneq]; 
        [subst; auto|apply Hnone; lia]. }
Qed.

Fact nat_min_strong: forall n (P: nat -> Prop), 
  P n -> exists m, P m /\ forall x, P x -> (m <= x)%nat.
Proof.
  intros n P0 Hn.
  destruct (nat_min_bounded n P0) as [[m [_ [Hpm Hmin]]] | Hnone].
  - exists m. split; auto. intros x Hx.
    destruct (classic (m <= x)%nat) as [Hle | Hgt]; auto.
    assert (Hlt: (x < m)%nat) by lia.
    apply Hmin in Hlt. contradiction.
  - exfalso. apply (Hnone n); auto. 
Qed.

Fact Z_min_strong: 
  forall (z: Z) (P: Z -> Prop), 
  P z -> 
  (forall x, P x -> 0 <= x) -> 
  exists m, P m /\ forall x, P x -> m <= x.
Proof.
  intros z P0 Hz Hpos.
  set (Q := fun n => P0 (Z.of_nat n)).
  assert (HQ: Q (Z.to_nat z)).
  { unfold Q. rewrite Z2Nat.id; auto. }
  destruct (nat_min_strong (Z.to_nat z) Q HQ) as [m_nat [Hm1 Hm2]].
  exists (Z.of_nat m_nat). split; auto.
  intros x Hx. 
  pose proof (Hpos x Hx) as Hx0.
  assert (HQx: Q (Z.to_nat x)).
  { unfold Q. rewrite Z2Nat.id; auto. }
  pose proof (Hm2 (Z.to_nat x) HQx) as Hle.
  lia.
Qed.

(* 在*没有负边*的图中，任意两点之间的最短距离一定存在 *)
Theorem min_value_weight_epath_in_vset_exist: 
  forall u v S, exists z, min_value_weight_epath_in_vset g u v S z. 
Proof. 
  intros. 
  set (X := fun p => is_epath_through_vset g u p v S).
  set (f := epath_weight g).
  destruct (classic (exists p, X p /\ exists w, f p = Some w)) as [H_ex | H_none].
  
  - destruct H_ex as [p0 [Hp0 [w0 Hw0]]].
    set (P_Z := fun w => exists p, X p /\ f p = Some w).
    assert (HP0: P_Z w0).
    { exists p0. split; auto. }
    assert (Hpos: forall w, P_Z w -> 0 <= w).
    { intros w [p [Hp Hpw]].
      destruct Hp as [Hp_valid _]. 
      pose proof (valid_epath_non_neg u p v Hp_valid).
      unfold f in Hpw. rewrite Hpw in H.
      simpl in H. lia. } 
    destruct (Z_min_strong w0 P_Z HP0 Hpos) as [m [Hm_prop Hm_min]].
    destruct Hm_prop as [p_min [Hp_min Hf_min]].

    exists (Some m).
    unfold min_value_of_subset_with_default.
    left. split.
    + unfold min_value_of_subset.
      exists p_min. split; auto.
      unfold min_object_of_subset.
      split; auto.
      intros b Hb.
      destruct (f b) as [wb |] eqn:Hfb.
      * assert (Hb_PZ: P_Z wb) by (exists b; split; auto).
        pose proof (Hm_min wb Hb_PZ) as Hle.
        subst f.
        rewrite Hf_min, Hfb. 
        simpl. lia.
      * subst f.
        rewrite Hf_min, Hfb.
        apply Z_op_le_none_r. 
    + apply Z_op_le_none_r.
  - exists None.
    right; split; auto.
    intros a Ha.
    destruct (f a) as [wa |] eqn:Hfa.
    + exfalso. apply H_none.
      exists a. split; auto. exists wa. auto.
    + apply Z_op_none_le_iff. 
      subst f; auto.
Qed. 

Theorem min_value_weight_epath_exist: 
  forall u v, exists z, min_value_weight_epath g u v z. 
Proof.
  intros.
  pose proof min_value_weight_epath_in_vset_exist u v (fun x => True) as [z Hz].
  exists z. 
  destruct Hz as [[[p [[Hp_valid Hp_min] Hp_eq]] _]|[]].
  - left; split; [exists p; split; auto|destruct z; simpl; auto].
    split; [destruct Hp_valid; auto|intros q Hq; apply Hp_min]. 
    split; [auto|intros; exact I].
  - right; split; auto.
    intros p Hp.
    pose proof H p ltac:(split; [auto|intros; exact I]).
    auto.
Qed.

Theorem dijkstra_greedy_choice_correct: 
  forall u S dist, 
    (forall v, ~ v ∈ S -> min_value_weight_epath_in_vset g src v S (dist v)) ->  
    min_object_of_subset Z_op_le (fun v => ~ v ∈ S) dist u -> 
    min_value_weight_epath g src u (dist u).
(*
Visited Set (S)                       Unvisited Set (V \ S)
  ┌───────────────────────┐             ┌──────────────────────────────────┐
  │                       │             │                                  │
  │               (dist u)├─────────────────> [u] (Current min dist)       │
  │              /        │             │      ^                           │
  │ [src] ~~~~~~*         │             │      | (w >= 0)                  │
  │              \        │             │      |                           │
  │               (dist x)├────> [x] ~~~~~~~~~~+ (Hypothetical shorter path│
  │                       │      ^      │        which is impossible)      │
  └───────────────────────┘      |      └──────────────────────────────────┘
                                 |
                          Any path escaping S MUST 
                          pass through some node x.
                          Since w >= 0, dist(u) <= dist(x) <= dist(x) + w(x->u)
*)
Proof. 
  intros u S dist H_inv Hu. 
  destruct Hu as [H_uS Hu_min]. 
  pose proof H_inv u H_uS as [[[p [[Hp_valid Hp_min]]] Hpnone]|[H_min H_none]].
  - (* dist u = Some *)
    left; split; auto. 
    exists p; split; auto. 
    split; [apply Hp_valid|intros q Hq]. 
    eapply is_epath_through_vset_greedy_cut in Hq; eauto. 
    destruct Hq as [x [p_in [p_out [H_pin [H_x [H_pout H_eq]]]]]]. 
    pose proof H_inv x H_x as Hx_min. 
    destruct Hx_min as [[[r [[Hr_valid Hr_min] Hr_none]] _]|[H_none _]]. 
    * pose proof Hr_min p_in H_pin as Hr_min. 
      pose proof Hu_min x H_x as Hx_min. 
      rewrite Hr_none in Hr_min. 
      rewrite H. 
      rewrite H_eq. 
      rewrite epath_weight_app_assoc. 
      apply Z_op_le_trans with (y := dist x); auto. 
      apply Z_op_le_trans with (y := epath_weight g p_in); auto. 
      pose proof non_neg_epath _ _ _ H_pout as H_pout_pos. 
      rewrite <- Z_op_plus_O_r at 1. 
      apply Z_op_plus_mono; auto. 
      apply Z_op_le_refl. 
    * pose proof H_none p_in H_pin as Hx_none. 
      rewrite Z_op_none_le_iff in Hx_none. 
      rewrite H_eq. 
      rewrite epath_weight_app_assoc. 
      rewrite Hx_none. 
      apply Z_op_le_none_r. 
  - (* dist u = None *)
    rewrite H_none. 
    right; split; auto. 
    intros p Hp. 
    rewrite Z_op_none_le_iff. 
    eapply is_epath_through_vset_greedy_cut in Hp; eauto.  
    destruct Hp as [x [p_in [p_out [H_pin [H_x [H_pout H_eq]]]]]]. 
    pose proof Hu_min x H_x as Hx_none. 
    rewrite H_none in Hx_none. 
    rewrite Z_op_none_le_iff in Hx_none. 
    pose proof H_inv x H_x as Hx_min. 
    rewrite Hx_none in Hx_min. 
    destruct Hx_min as [[[px [[Hpxvalid Hpxmin] Hpnone]] _]|[Hnone _]]. 
    * pose proof Hpxmin p_in H_pin. 
      rewrite Hpnone in H. 
      rewrite Z_op_none_le_iff in H. 
      rewrite H_eq. 
      rewrite epath_weight_app_assoc. 
      rewrite H. 
      reflexivity. 
    * pose proof Hnone p_in H_pin. 
      rewrite Z_op_none_le_iff in H. 
      rewrite H_eq. 
      rewrite epath_weight_app_assoc. 
      rewrite H. 
      reflexivity. 
  Unshelve. auto. auto. 
Qed.


Theorem dijkstra_visited_keep: 
  forall u v S e dist, 
    min_value_weight_epath g src v (dist v) -> 
    min_value_weight_epath_in_vset g src u S (dist u) -> 
    step_aux g e u v -> 
    Z_op_le (dist v) (Z_op_plus (dist u) (weight g e)).
(* 
  [src] ~~~~(dist u)~~~> [u] --- (edge e, weight w) ---> [v] (Already Globally Min)
    |                                                      ^
    |                                                      |
    +~~~~~~~~~~~~~~~~(dist v)~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
                (Global Min Path) 
  If [v] is already known to be globally minimum, 
  Dist(v) <= Dist(u) + w(u,v) ALWAYS holds. 
  (Because otherwise, Dist(v) wasn't the global minimum to begin with!)
 *)
Proof.
  intros u v S e dist Hminv Hminu Hstep. 
  destruct Hminu as [[Hu _]|[]]; 
  destruct Hminv as [[Hv _]|[]]. 
  - destruct Hu as [Hupath [[Huvalid Humin] Hueq]].
    destruct Hv as [Hvpath [[Hvvalid Hvmin] Hveq]]. 
    pose proof Hvmin (Hupath ++ e :: nil)
    ltac:(apply valid_epath_snoc with (v:=u); eauto; apply Huvalid). 
    rewrite <- Hveq, <- Hueq. 
    rewrite epath_weight_app_assoc in H. 
    rewrite epath_weight_single in H. auto. 
  - destruct Hu as [Hupath [[Huvalid Humin] Hueq]]. 
    pose proof H (Hupath ++ e :: nil)
    ltac:(apply valid_epath_snoc with (v:=u); eauto; apply Huvalid). 
    rewrite <- Hueq, H0. 
    rewrite epath_weight_app_assoc in H1. 
    rewrite epath_weight_single in H1. auto. 
  - rewrite H0. 
    simpl. 
    destruct (dist v); simpl; auto; lia. 
  - rewrite H0. 
    simpl. 
    destruct (dist v); simpl; auto; lia. 
Qed. 

(* 这个定理是floyd-warshall的步骤定理的推论：
当u-v之间的最短路径就是边e时，计算结果已然正确；
当u-v之间的最短路径经过了集合S中的顶点x时，通过简单的数学演算和步骤定理得到的最小值可知，目标等价于证明dist(v) <= dist(u) + min_path(u,v)，这时，我们就会需要dist x不仅仅是全局的最小值，也是S上的最小值，这样才能把两边不同的最小值形式串连起来 *)
Theorem dijkstra_relax_edge_correct: 
  forall u v e S dist, 
    (forall v, v ∈ S -> min_value_weight_epath g src v (dist v) /\  
                         min_value_weight_epath_in_vset g src v S (dist v)) -> 
    (forall v, ~ v ∈ S -> min_value_weight_epath_in_vset g src v S (dist v)) ->  
    (forall u v, u ∈ S -> ~ v ∈ S -> Z_op_le (dist u) (dist v)) ->
    ~ u ∈ S -> 
    ~ v ∈ S -> 
    step_aux g e u v -> 
    min_value_weight_epath_in_vset g src v (S ∪ [u]) 
    (Z_op_min (dist v) (Z_op_plus (dist u) (weight g e))). 
(* 
   ┌──────────────────────── 集合 S ────────────────────────┐
   │                                                        │
   │                           dist(x)                      │w(x ↝ v)
   │     ┌─────────────────────────────────────────> [x] ───┼─────────[v](未访问节点)
   │     │                                            ^     │         │
   │     │                                            │     │         │
   │   [src]                                          │     │         │
   │     │                                            │     │         │
   │     │ dist(u)                                    │     │         │
   │     │                                            │     │         │
   └─────┼────────────────────────────────────────────┼─────┘         │
         v                                            │               │
        [u] ─────────────── w(u ↝ x) ────────────────┘               │
    (新加入节点)             (折返现象)                                │
         │                                                            │
         └──────────────────────── edge(u, v) ────────────────────────┘
                                 (正常松弛边)
*)
Proof.
  intros u v e S dist H_inv1 H_inv2 Hcross H_uS H_vS H_step. 

  pose proof H_inv2 u H_uS as Hdistu. 
  pose proof H_inv2 v H_vS as Hdistv.  
  pose proof min_value_weight_epath_in_vset_exist u v S as [z Hz]. 
  pose proof @floyd_warshall_step_spec _ _ _ _ _ _ g g_valid 
    _ _ _ _ _ _ _ non_neg_loop 
    S src v u (dist v) (dist u) z 
    Hdistv Hdistu Hz.
  destruct Hz as [[[p [[Hpvalid Hpmin] Hpeq]] _]|[]]. 

  - assert (Z_op_le z (weight g e)) as Hze. { 
      pose proof Hpmin (e :: nil) ltac:(eapply is_epath_through_vset_single; eauto). 
      rewrite <- Hpeq. 
      rewrite epath_weight_cons in H0.  
      rewrite epath_weight_nil in H0. 
      rewrite Z_op_plus_O_r in H0. auto. 
    }
    destruct p as [|e' p'].  
    1: { 
      (* u = v的平凡情形 *)
      destruct Hpvalid as [Hpvalid _]. 
      eapply valid_epath_nil_inv in Hpvalid; subst. 
      unfold epath_weight in H; simpl in H; rewrite Z_op_plus_O_r in H; auto. 
      assert (Z_op_min (dist v) (dist v) = dist v) by (destruct (dist v); simpl; try f_equal; lia). 
      rewrite H0 in H. 
      assert (Z_op_min (dist v) (Z_op_plus (dist v) (weight g e)) = (dist v)). 
      apply Z_op_le_min_l; rewrite <- Z_op_plus_O_r at 1; apply Z_op_plus_mono; auto. 
      destruct (dist v); simpl in *; try lia. 
      rewrite H1; auto. 
    } 
    destruct p' as [|a q]. 
    1: {
      (* u v之间的最短路径是e的简单情形 *)
      rewrite epath_weight_single in Hpeq. 
      destruct Hpvalid as [Hpvalid _]. 
      apply valid_epath_single_inv in Hpvalid. 
      eapply no_multiple_edge with (e2:=e') in H_step; eauto. 
      subst; auto.
    }
    (* u v之间的最短路径经过了S中的顶点x *)

    pose proof Hpvalid as Hpvalid'. 
    assert (e' :: a :: q = (e' :: nil) ++ (a :: q)) as Htemp by (simpl; auto); 
    rewrite Htemp in Hpvalid; clear Htemp.
    apply is_epath_through_vset_app_inv in Hpvalid as [x [Hx [Hux Hxv]]]; try (symmetry; apply nil_cons).  
    assert (Z_op_le (dist v) (Z_op_plus (dist u) z)). {
       (* 此时u到v的最短距离不大于dist u - dist v *)
      destruct Hdistu as [[Hu _]|[]];  
      destruct Hdistv as [[Hv _]|[]].
      * (* dist u = Some, dist v = Some*)
        destruct Hu as [Hupath [[Huvalid Humin] Hueq]].
        destruct Hv as [Hvpath [[Hvvalid Hvmin] Hveq]].
        (* rewrite <- Hueq, <- Hveq.  *)
        pose proof H_inv1 x Hx as [_ Hx_min].  
        pose proof Hx_min as [[[Hxpath [[Hxvalid Hxmin] Hxeq]] _]|[]]. 
        + (* dist x = Some *)
          pose proof Hvmin (Hxpath ++ a :: q). 
          assert (Hxpath ++ a :: q ∈ (fun p : list E => is_epath_through_vset g src p v S)) as Hle1
          by (eapply (is_epath_through_vset_app src); eauto; apply Hxvalid).
          apply H0 in Hle1. 
          rewrite Hveq in Hle1. 
          eapply Z_op_le_trans; eauto. 
          rewrite! epath_weight_app_assoc. 
          rewrite Hxeq. 
          rewrite <- Hpeq; rewrite! epath_weight_cons. 
          apply Z_op_plus_mono; auto.  
          rewrite <- Z_op_plus_O_l at 1. 
          apply Z_op_plus_mono; auto. 
          apply Z_op_le_refl. 
        + pose proof Hcross x u Hx H_uS. 
          rewrite H1 in H2. 
          rewrite Z_op_none_le_iff in H2. 
          rewrite H2. 
          simpl; destruct (dist v); simpl; auto. 
      * pose proof H_inv1 x Hx as [_ Hx_min].  
        pose proof Hx_min as [[[Hxpath [[Hxvalid Hxmin] Hxeq]] _]|[]]. 
        + assert (Hxpath ++ a :: q ∈ (fun p : list E => is_epath_through_vset g src p v S)) as Hle1
          by (eapply (is_epath_through_vset_app src); eauto; apply Hxvalid).
          apply H0 in Hle1. 
          rewrite <- H1 in Hle1. 
          eapply Z_op_le_trans; eauto. 
          rewrite! epath_weight_app_assoc. 
          rewrite Hxeq. 
          rewrite <- Hpeq; rewrite! epath_weight_cons. 
          apply Z_op_plus_mono; auto.  
          rewrite <- Z_op_plus_O_l at 1. 
          apply Z_op_plus_mono; auto. 
          apply Z_op_le_refl. 
        + pose proof Hcross x u Hx H_uS. 
          rewrite H3 in H4. 
          rewrite Z_op_none_le_iff in H4. 
          rewrite H4. 
          simpl; destruct (dist v); simpl; auto. 
      * rewrite H1; simpl. 
        destruct (dist v); simpl; auto. 
      * rewrite H1; simpl. 
        destruct (dist v); simpl; auto.      
    }
  rewrite Z_op_le_min_l in H by auto. 
  rewrite Z_op_le_min_l; auto. 
  eapply Z_op_le_trans; eauto. 
  apply Z_op_plus_mono; auto. 
  destruct (dist u); simpl; auto; lia. 
  - pose proof H0 (e :: nil) ltac:(eapply is_epath_through_vset_single; eauto). 
    rewrite Z_op_none_le_iff in H2. 
    rewrite epath_weight_single in H2. 
    rewrite H1 in H; rewrite H2; auto. 
  Unshelve. auto. auto. 
Qed. 

(* 这个定理可以看作是上一个定理的推论：u和v之间的边e都是+∞ 
不过为了算法那边的不同分支，我们还是没有合并这两个定理，而是用几乎相同的过程证明了两遍 *)
Theorem dijkstra_relax_edge_correct': 
  forall u v S dist, 
    (forall v, v ∈ S -> min_value_weight_epath g src v (dist v) /\  
                         min_value_weight_epath_in_vset g src v S (dist v)) -> 
    (forall v, ~ v ∈ S -> min_value_weight_epath_in_vset g src v S (dist v)) ->  
    (forall u v, u ∈ S -> ~ v ∈ S -> Z_op_le (dist u) (dist v)) ->
    ~ u ∈ S -> 
    ~ v ∈ S -> 
    (~ exists e, step_aux g e u v) -> 
    min_value_weight_epath_in_vset g src v (S ∪ [u]) (dist v). 
Proof.
  intros u v S dist H_inv1 H_inv2 Hcross H_uS H_vS H_nostep. 

  pose proof H_inv2 u H_uS as Hdistu. 
  pose proof H_inv2 v H_vS as Hdistv.  
  pose proof min_value_weight_epath_in_vset_exist u v S as [z Hz]. 
  (* 应用 Floyd-Warshall 步骤定理 *)
  pose proof @floyd_warshall_step_spec _ _ _ _ _ _ g g_valid 
    _ _ _ _ _ _ _ non_neg_loop 
    S src v u (dist v) (dist u) z 
    Hdistv Hdistu Hz.
  destruct Hz as [[[p [[Hpvalid Hpmin] Hpeq]] _]|[]]. 

  - destruct p as [|e' p'].  
    1: { 
      (* u = v的平凡情形 *)
      destruct Hpvalid as [Hpvalid _]. 
      eapply valid_epath_nil_inv in Hpvalid; subst. 
      unfold epath_weight in H; simpl in H; rewrite Z_op_plus_O_r in H; auto. 
      assert (Z_op_min (dist v) (dist v) = dist v) by (destruct (dist v); simpl; try f_equal; lia). 
      rewrite H0 in H; auto. 
    } 
    destruct p' as [|a q]. 
    1: {
      (* u v之间的最短路径是e的简单情形 *)
      rewrite epath_weight_single in Hpeq. 
      destruct Hpvalid as [Hpvalid _]. 
      apply valid_epath_single_inv in Hpvalid. 
      exfalso; apply H_nostep; exists e'; auto.
    }
    (* u v之间的最短路径经过了S中的顶点x *)

    pose proof Hpvalid as Hpvalid'. 
    assert (e' :: a :: q = (e' :: nil) ++ (a :: q)) as Htemp by (simpl; auto); 
    rewrite Htemp in Hpvalid; clear Htemp.
    apply is_epath_through_vset_app_inv in Hpvalid as [x [Hx [Hux Hxv]]]; try (symmetry; apply nil_cons).  
    assert (Z_op_le (dist v) (Z_op_plus (dist u) z)). {
       (* 此时u到v的最短距离不大于dist u - dist v *)
      destruct Hdistu as [[Hu _]|[]];  
      destruct Hdistv as [[Hv _]|[]].
      * (* dist u = Some, dist v = Some*)
        destruct Hu as [Hupath [[Huvalid Humin] Hueq]].
        destruct Hv as [Hvpath [[Hvvalid Hvmin] Hveq]].
        (* rewrite <- Hueq, <- Hveq.  *)
        pose proof H_inv1 x Hx as [_ Hx_min].  
        pose proof Hx_min as [[[Hxpath [[Hxvalid Hxmin] Hxeq]] _]|[]]. 
        + (* dist x = Some *)
          pose proof Hvmin (Hxpath ++ a :: q). 
          assert (Hxpath ++ a :: q ∈ (fun p : list E => is_epath_through_vset g src p v S)) as Hle1
          by (eapply (is_epath_through_vset_app src); eauto; apply Hxvalid).
          apply H0 in Hle1. 
          rewrite Hveq in Hle1. 
          eapply Z_op_le_trans; eauto. 
          rewrite! epath_weight_app_assoc. 
          rewrite Hxeq. 
          rewrite <- Hpeq; rewrite! epath_weight_cons. 
          apply Z_op_plus_mono; auto.  
          rewrite <- Z_op_plus_O_l at 1. 
          apply Z_op_plus_mono; auto. 
          apply Z_op_le_refl. 
        + pose proof Hcross x u Hx H_uS. 
          rewrite H1 in H2. 
          rewrite Z_op_none_le_iff in H2. 
          rewrite H2. 
          simpl; destruct (dist v); simpl; auto. 
      * pose proof H_inv1 x Hx as [_ Hx_min].  
        pose proof Hx_min as [[[Hxpath [[Hxvalid Hxmin] Hxeq]] _]|[]]. 
        + assert (Hxpath ++ a :: q ∈ (fun p : list E => is_epath_through_vset g src p v S)) as Hle1
          by (eapply (is_epath_through_vset_app src); eauto; apply Hxvalid).
          apply H0 in Hle1. 
          rewrite <- H1 in Hle1. 
          eapply Z_op_le_trans; eauto. 
          rewrite! epath_weight_app_assoc. 
          rewrite Hxeq. 
          rewrite <- Hpeq; rewrite! epath_weight_cons. 
          apply Z_op_plus_mono; auto.  
          rewrite <- Z_op_plus_O_l at 1. 
          apply Z_op_plus_mono; auto. 
          apply Z_op_le_refl. 
        + pose proof Hcross x u Hx H_uS. 
          rewrite H3 in H4. 
          rewrite Z_op_none_le_iff in H4. 
          rewrite H4. 
          simpl; destruct (dist v); simpl; auto. 
      * rewrite H1; simpl. 
        destruct (dist v); simpl; auto. 
      * rewrite H1; simpl. 
        destruct (dist v); simpl; auto.      
    }
  rewrite Z_op_le_min_l in H by auto. 
  auto.
  - rewrite H1 in H. 
    rewrite Z_op_plus_none_r in H. 
    rewrite Z_op_min_none_r in H. 
    auto. 
  Unshelve. auto. auto. 
Qed. 

End dijkstra.

