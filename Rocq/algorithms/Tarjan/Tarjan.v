
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib safeexec_lib.
From RecordUpdate Require Import RecordUpdate.
From TraceLib Require Import TraceBasic TraceLogic CommonTactics TraceRecur MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import DFS.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.

Section Tarjan.

Context {V E: Type}
        `{eq_dec: EqDec V eq}
        (g: OriginalGraphType V E)
        {origin_gvalid: OriginalGraph_gvalid g}.

Record St: Type := mkSt {
  visited: V -> Prop;
  timer: nat;
  fa: V -> V;
  tedge: V -> option E;
  dfn: V -> nat;
  low: V -> nat;
  bridges: list E;
}.

Instance: Settable St := settable! mkSt <visited; timer; fa; tedge; dfn; low; bridges>.


Definition is_rooted_tree (rt: RootedTreeType V E) := 
  RootedTreeProp V E rt.
  
Context (root: V)
        (g_vvalid_root: vvalid g root).

Definition state_to_rootedtree (s: St): RootedTreeType V E :=
  {| 
  tarjan.vset := s.(visited); 
  tarjan.theroot := root; 
  tarjan.parent := s.(fa); 
  tarjan.edge := s.(tedge);
  tarjan.listV := g.(original_listV);
|}.

(*defining the program*)

Definition initSt: St := {|
  visited := [root];
  timer := 1;
  fa := t_empty root; (* Dummy value, can be any default value *)
  tedge := t_empty None;
  dfn := t_empty 0; 
  low := t_empty 0;
  bridges := nil;
|}.

Definition visit (v:V): program St unit :=
  update' (fun s => s <| visited ::=  fun x => x ∪ [v] |>).

Definition set_low (v:V) (n: nat): program St unit :=
  update' (fun s => s <| low ::= fun low0 =>
    v !-> n; low0 |>).

Definition set_dfn (v:V) (n: nat): program St unit :=
  update' (fun s => s <| dfn ::= fun dfn0 =>
    v !-> n; dfn0 |>).

Definition set_tree' (u v: V) (e: E): St -> St :=
  (fun s => s 
    <| visited ::=  fun x => x ∪ [v] |> 
    <| fa ::= fun fa0 => v !-> u; fa0 |> 
    <| tedge ::= fun tedge0 => v !-> Some e; tedge0 |>).
    
Definition set_tree (u v: V) (e: E): program St unit :=
  update' (set_tree' u v e).

Definition add_bridge (e: E): program St unit :=
  update' (fun s => s <| bridges ::= fun bridges0 =>
    e :: bridges0 |> ).

Definition update_low (u: V) (n: nat) : program St unit :=
  update' (fun s => s <| low ::= fun low0 =>
    u !-> (min (low0 u) n); low0 |>).

Definition incr_timer: program St unit :=
  update' (fun s => s <| timer ::= fun t => t + 1 |>).

Ltac unfold_op :=
  unfold visit, set_low, set_dfn, set_tree, 
    add_bridge, update_low, incr_timer.

Definition preloop (u: V): program St unit:=
  t <- get (fun s t => t = s.(timer));;
  set_dfn u t;;
  set_low u t;;
  incr_timer.

Definition post_rec (e0: E) (u v: V): program St unit :=
  lowv <- get' (fun s => s.(low) v);;
  update_low u lowv;;
  If (fun s => s.(low) v > s.(dfn) u)
    (add_bridge e0).

Definition for_branch1 (e0: E) (u v: V) (W: V -> program St unit): program St unit :=
   set_tree u v e0;;
   W v;;
   post_rec e0 u v.

Definition for_branch2 (u v : V) :=
  dfnv <- get' (fun s => s.(dfn) v);;
  update_low u dfnv.

Definition forset_body (u: V) (W: V -> program St unit): E -> program St unit := 
  (fun e0 =>
    v <- get (fun _ v => step_aux g e0 u v);; 
    if_else (fun s => ~ v ∈ s.(visited))
    (for_branch1 e0 u v W)
    (If (fun s => ~ s.(tedge) u = Some e0) 
      (for_branch2 u v))).

Definition loop_body (u: V) (W: V -> program St unit) :=
  forset (fun e0 => exists v, step_aux g e0 u v)
  (forset_body u W).

Definition tarjan_f (W: V -> program St unit) (u: V) :=
  preloop u;;
  loop_body u W.

Definition tarjan :=
  Lfix tarjan_f.

  

Lemma for_branch1_mono_cont (e: E) (u v: V):
  mono_cont (for_branch1 e u v).
Proof.
  unfold for_branch1.
  mono_cont_auto.
Qed.

(** Tarjan with Tag *)

Local Open Scope ghost_scope.

Definition for_branch1' (W: V -> programT St (@Tag V) unit) (e0:E) (u v:V) :=
  ↑(set_tree u v e0);;
  W v;;
  ↑(post_rec e0 u v).

Definition loop_body' (W: V -> programT St Tag unit) (u: V) :=
  forset (fun e0 => exists v, step_aux g e0 u v)
  (fun e0 => 
    v <- ↑(get (fun _ v => step_aux g e0 u v));; 
    if_else (fun '(s, _) => ~ v ∈ s.(visited))
    (for_branch1' W e0 u v)
    ↑(If (fun s => ~ s.(tedge) u = Some e0) 
      (for_branch2 u v))).

Definition tarjan_f' (W: V -> programT St Tag unit) (u: V) :=
  ↑(preloop u);;
  loop_body' W u.

Definition tarjan' :=
  trace_call tarjan_f'.

Lemma Gequiv_tarjan (u: V):
  Gequiv (tarjan u) (tarjan' u).
Proof.
  unfold tarjan, tarjan', tarjan_f, tarjan_f', loop_body, loop_body', forset_body; unfold_call.
  Gequiv_autoT.
  unfold for_branch1, for_branch1'.
  Gequiv_autoT.
Qed.

Lemma Gequiv_preloop (u: V):
  @Gequiv _ (@TR (@Tag V) St)  _ (preloop u) (↑(preloop u))%ghost.
Proof.
  unfold preloop; unfold_op.
  Gequiv_autoT.
Qed. 

Lemma Gequiv_set_tree (u v: V) (e: E):
  @Gequiv _ (@TR (@Tag V) St) _ (set_tree u v e) (↑(set_tree u v e))%ghost.
Proof.
  unfold set_tree; unfold_op.
  Gequiv_autoT.
Qed.

Lemma Gequiv_post_rec (u v: V) (e: E):
  @Gequiv _ (@TR (@Tag V) St) _ (post_rec e u v) (↑(post_rec e u v))%ghost.
Proof.
  unfold post_rec; unfold_op.
  Gequiv_autoT.
Qed.

Lemma tarjan_keep_trace_inv:
  keep_trace_inv tarjan_f'.
Proof.
  unfold keep_trace_inv, tarjan_f', keepG; intros.
  hoare_bind Hoare_liftG_keepG; simpl; clear a0.
  unfold loop_body'.
  hoare_cons (Hoare_forset (fun _ '(_, g0) => P g0)); try easy.
  intros.
  hoare_bind Hoare_liftG_keepG; simpl.
  unfold if_else; hoare_auto.
  2:hoare_cons_pre (Hoare_liftG_keepG).
  unfold for_branch1'.
  eapply Hoare_conseq_pre.
  2:hoare_bind (Hoare_liftG_keepG P).
  intros (s, ?); tauto.
  (* hoare_bind (Hoare_liftG_keepG P). *)
  hoare_bind H; simpl.
  apply Hoare_liftG_keepG.
Qed.

#[export] Instance TraceCallTarjan: TraceCall tarjan_f' :=
{|
  trace_inv_f := tarjan_keep_trace_inv;
  origin_prog := tarjan;
  call_Gequiv := Gequiv_tarjan;
|}.

(** We prove that Tarjan is equivalent to DFS in terms of visited vertices. *)
Section Tarjan_DFS_rel.

Definition DFS_loop (u: V) :=
  whileP (fun s : DFS.St => exists v : V, step g u v /\ ~ v ∈ s)
          (v <- get (fun (s : DFS.St) (v : V) => step g u v /\ ~ v ∈ s) ;; DFS g v).

Lemma safeExec_DFS_to_loop (u: V) (s: Tarjan.St) X:
  safeExec (fun hs => hs ∪ [u] == visited s) (DFS g u) X ->
  safeExec (fun hs => hs == visited s) (DFS_loop u) X.
Proof.
  intros Hs.
  rewrite DFS_unfold in Hs; unfold DFS_f in Hs.
  eapply (safeExec_bind_high tt (fun _ hs => hs == visited s)) in Hs.
  2:{
    intros s2 Hs2; eexists.
    split.
    unfold visit, update', update.
    reflexivity. tauto.
  }
  unfold DFS_loop; tauto.
Qed.

Lemma DFS_loop_unfold (u: V):
  DFS_loop u ==
  choice
    (assume (fun s : DFS.St => exists v : V, step g u v /\ ~ v ∈ s) ;; 
      (v <- get (fun (s : DFS.St) (v : V) => step g u v /\ ~ v ∈ s) ;; DFS g v);; 
      DFS_loop u)
    (assume (fun s : DFS.St => ~ (exists v : V, step g u v /\ ~ v ∈ s)) ;; return tt).
Proof.
  unfold DFS_loop.
  rewrite while_unfold; reflexivity.
Qed.

Lemma Tarjan_rel_loop_inv (e: E) (u a: V) s done
  (Hinv: forall (e : E) (v : V),
      e ∈ done -> step_aux g e u v -> v ∈ visited s)
  (Ha: step_aux g e u a):
  forall (e0 : E) (v : V),
    e0 ∈ done ∪ [e] -> original_step_aux g e0 u v -> v ∈ visited s ∪ [a].
Proof.
  intros e0 v He0a He0b.
  destruct He0a.
  {
    left.
    eapply Hinv; eauto; tauto.
  }
  sets_unfold in H; subst e.
  pose proof step_aux_unique_undirected 
    g e0 _ _ _ _ origin_gvalid Ha He0b.
    assert (Hva: v = a).
    { do 2 destruct H; subst; easy. }
    subst v; sets_unfold; tauto.
Qed.

Lemma in_union_eq {A: Type} (s: A -> Prop) (x: A):
  x ∈ s ->
  s ∪ [x] == s.
Proof.
  intros Hx; split; intros.
  - destruct H. tauto.
    sets_unfold in H; subst x; tauto.
  - left; tauto.
Qed.
  
Theorem Tarjan_DFS_rel X:
  safeExec (fun s => s == ∅) (DFS g root) X ->
  Hoare (fun s => s = initSt) 
        (tarjan root) 
        (fun _ s => safeExec (fun dfs_s => dfs_s == s.(visited)) (ret tt) X).
Proof.
  intros HE; unfold tarjan.
  hoare_cons (Hoare_fix_logicv _ 
    (fun u '(X, vset) ls => vset == ls.(visited) /\ u ∈ ls.(visited) /\
      safeExec (fun hs => hs ∪ [u] == ls.(visited)) (DFS g u) X)
    (fun _ '(X, vset) _ ls => vset ⊆ ls.(visited) /\
      safeExec (fun hs => hs == ls.(visited)) (ret tt) X)
    root (X, [root])
  ).
  {
    intros; rewrite H; simpl; split; [easy |].
    split; [easy|].
    eapply safeExec_conseq; eauto.
    simpl; intros ? tmp; rewrite tmp; sets_unfold; tauto. 
  }
  clear X HE.
  intros W IH u (X, vset).
  intro_state.
  destruct H as [Hvset [Hu H]].
  unfold tarjan_f, preloop, loop_body.
  unfold_op.
  hoare_auto_s.
  intro_state; rename H0 into Hs1.
  apply safeExec_DFS_to_loop in H.
  hoare_cons (Hoare_forset 
    (fun Eset s => safeExec (fun hs => hs == s.(visited)) (DFS_loop u) X /\
      (forall e v, e ∈ Eset -> step_aux g e u v -> v ∈ s.(visited)) /\
      vset ⊆ s.(visited))).
  {
    intros; subst; simpl.
    repeat (split; try tauto).
    intros ? ?; sets_unfold; tauto.
    rewrite Hvset; reflexivity.
  }
  {
    clear IH.
    intros _ s [Hs [He Hvsub]].
    rewrite DFS_loop_unfold in Hs.
    safe_choice_r Hs.
    tauto.
    intros; intros [v [Hv1 Hv2]].
    destruct Hv1 as [e Hv1].
    specialize (He e v).
    rewrite H0 in Hv2.
    apply Hv2; apply He; auto.
    sets_unfold; exists v; auto.
  }
  {
    unfold Proper, respectful.
    intros; rewrite H1.
    split; intros; split; try tauto;
    split; try tauto; destruct H2 as [_ [H2 _]];
    intros ? ? Hxy; apply H2.
    - rewrite H0; auto.
    - rewrite <- H0; auto. 
  }
  clear dependent s1; clear dependent s0.
  intros done e Hd He1 He2.
  intro_state. destruct H as [Hse [Hev Hvsub]].
  unfold forset_body; hoare_auto_s.
  (** for_branch1 *)
  - unfold for_branch1; unfold_op.
    hoare_auto_s.
    rewrite DFS_loop_unfold in Hse.
    safe_choice_l Hse.
    2:{
      intros st Hst.
      exists a.
      rewrite Hst.
      split; auto.
      exists e; auto. 
    }
    prog_nf in Hse.
    apply (safeExec_get_bind a) in Hse; auto.
    apply safeExec_bind in Hse.
    destruct Hse as [X' [Hse1 Hse2]].
    hoare_bind_cons (IH a (X', visited s0 ∪ [a])).
    {
      assert (visited s = visited s0 ∪ [a]).
      { subst s; simpl; easy. }
      rewrite H2; clear H2.
      split; [easy |split].
      right; easy.
      eapply safeExec_conseq; eauto.
      simpl; intros ? tmp; rewrite tmp; easy.
    }
    simpl; clear Hse1 IH a0.
    intro_state.
    destruct H1 as [Hs1 Hse].
    apply Hse2 in Hse; clear dependent X'.
    unfold post_rec; unfold_op.
    assert (Hres1: forall (e0 : E) (v : V),
      e0 ∈ done ∪ [e] -> original_step_aux g e0 u v -> v ∈ visited s1).
    {
      intros; rewrite <- Hs1.
      eapply Tarjan_rel_loop_inv; eauto.
    }
    assert (Hres2: vset ⊆ visited s1).
    {
       rewrite Hvsub; rewrite <- Hs1.
      sets_unfold; tauto.
    }
    hoare_auto_s.
    + subst s; simpl; tauto.
    + destruct H1 as [seq _]; subst s; simpl.
      tauto.
    + intros st Hst.
      rewrite Hst.
      split; auto.
      exists e; auto.
  (** for_branch2 *)
  - unfold for_branch2; unfold_op.
    hoare_auto_s.
    subst s; simpl.
    apply NNPP in H0.
    split; [tauto |].
    split; [| tauto].
    intros.
    rewrite <- (in_union_eq (visited s0) a) by tauto.
    eapply Tarjan_rel_loop_inv; eauto.
  (** for_branch3*)
  - apply NNPP in H0.
    destruct H1; subst.
    split; [tauto |].
    split; [| tauto].
    intros.
    rewrite <- (in_union_eq (visited s0) a) by tauto.
    eapply Tarjan_rel_loop_inv; eauto.
Qed.

Theorem Tarjan_visited_reachable:
  Hoare (fun s => s = initSt) 
        (tarjan root) 
        (fun _ s => forall v, v ∈ s.(visited) <-> reachable g root v).
Proof.
  hoare_cons (Tarjan_DFS_rel).
  2:{
    apply safeExec_result_state.
    exists ∅; easy.
  }
  intros _ s Hsf v.
  pose proof (DFS_visited_reachable g root v).
  apply Hoare_result_state in H.
  rewrite H in Hsf.
  apply safeExec_ret_tt in Hsf.
  destruct Hsf as [? [H0 H1]]. 
  rewrite H0 in H1; auto.
Qed.

Theorem Tarjan_visited_reachable':
  Hoare (fun '(s, tr) => s = initSt /\ tr = nil) 
        (tarjan' root) 
        (fun _ '(s, tr) => forall v, v ∈ s.(visited) <-> reachable g root v).
Proof.
  eapply Hoare_toG.
  2: { apply Tarjan_visited_reachable. }
  apply Gequiv_tarjan.
  intros ? ? []; subst; auto.
Qed.

End Tarjan_DFS_rel.



End Tarjan.
