
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan Tarjan_tactics Tarjan_set_tree Tarjan_basics Tarjan_no_cross_edge Tarjan_is_dfn Tarjan_is_low Tarjan_bridge_iff.


Import SetsNotation.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope map_scope.

Section TARJAN.


Context {V E: Type}
        (root: V)
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V E)
        {origin_gvalid: OriginalGraph_gvalid g}
        (g_vvalid_root: vvalid g root).

Theorem Tarjan_judge_bridge:
  Hoare (fun s => s = initSt root)
        (tarjan g root)
        (fun _ s => forall e: E, 
        reachable_edge g (rootedtree.root (state_to_rootedtree g root s)) e ->
        List.In e s.(bridges) <-> is_bridge g e) .
Proof.
  intros.
  eapply Hoare_conseq_post.
  2: 
  {
    do 3 eapply Hoare_conj.
    apply Tarjan_dfn_valid; auto.
    apply Tarjan_no_cross_edge; auto.
    apply Tarjan_is_low; auto.
    apply Tarjan_subgraph; auto.
    apply Tarjan_bridge_iff; auto.
    apply Tarjan_reachable_visited; auto.
    apply Tarjan_bridge_is_tree_edge; auto.
    apply Tarjan_rooted_tree; auto.
  }
  simpl; intros.
  my_destruct H.
  destruct (classic ( evalid (state_to_rootedtree g root s) e)).
  - apply no_empty_edge in H8 as He.
    destruct He as [x [y He]].
    erewrite tarjan.tarjan; eauto.
    apply H7.
  - split; intros; exfalso.
    * firstorder. 
    * eapply tarjan_trivial; eauto. 
Qed.

End TARJAN.
