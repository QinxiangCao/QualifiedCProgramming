
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import TraceBasic TraceLogic CommonTactics TraceRecur.
From GraphLib Require Import graph_basic reachable_basic.


Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section DFS.
Context 
  {G V E: Type}
  `{graph: Graph G V E} 
  (g: G).

Notation step := (step g).
Notation reachable := (reachable g).

(** DFS program definition *)

Definition St: Type := V -> Prop.

Definition visit (v: V): program St unit :=
  update' (fun s1 => s1 ∪ Sets.singleton v).

Definition DFS_f (W: V -> program St unit) (u: V): program St unit :=
  visit u;;
  whileP (fun s => exists v, step u v /\ ~ v ∈ s)
    (v <- get (fun s v => step u v /\ ~ v ∈ s);; W v).

Definition DFS (u:V): program St unit :=
  Lfix DFS_f u.

Lemma DFS_mono_cont:
  mono_cont DFS_f.
Proof.
  unfold DFS_f.
  unfold whileP, whileP_f.
  mono_cont_auto.
Qed.

Lemma DFS_unfold (u:V):
  DFS u == DFS_f DFS u.
Proof.
  unfold DFS.
  revert u.
  change (DFS == DFS_f DFS).
  apply Lfix_fixpoint'.
  unfold DFS_f.
  unfold whileP, whileP_f.
  mono_cont_auto.
Qed.

Local Open Scope ghost.

Definition DFS_f' (W: V -> programT St (@Tag V) unit) (u: V): programT St (@Tag V) unit :=
  ↑(visit u);;
  whileP (fun '(s, _) => exists v, step u v /\ ~ v ∈ s)
    (v <- ↑(get (fun s v => step u v /\ ~ v ∈ s));; W v).

Definition DFS' (u: V): programT St (@Tag V) unit :=
  trace_call DFS_f' u.

Lemma Gequiv_DFS (u:V):
  Gequiv (DFS u) (DFS' u).
Proof.
  unfold DFS, DFS', DFS_f, DFS_f'; unfold_call.
  Gequiv_autoT.
Qed.

Lemma DFS_keep_trace_inv:
  keep_trace_inv DFS_f'.
Proof.
  unfold keep_trace_inv, DFS_f', keepG.
  intros.
  hoare_bind Hoare_liftG_keepG.
  simpl; clear a0.
  hoare_cons_post (Hoare_whileP _ _ (fun '(_, tr) => P tr)).
  apply Hoare_conseq_pre with (P2:= fun '(_, tr) => P tr).
  intros (s, tr); tauto.
  hoare_bind Hoare_liftG_keepG.
  auto.
Qed.

#[local] Instance TraceCallDFS: TraceCall DFS_f' :=
{|
  trace_inv_f := DFS_keep_trace_inv;
  origin_prog := DFS;
  call_Gequiv := Gequiv_DFS
|}.

(** DFS basic Prop *)
Lemma DFS_keep_visit (u v: V):
  Hoare (fun s => v ∈ s)
        (DFS u)
        (fun _ s => v ∈ s).
Proof.
  unfold DFS.
  apply Hoare_fix with
    (P:= fun _ s => v ∈ s)
    (Q:= fun _ _ s => v ∈ s).
  intros; unfold DFS_f; clear u; rename a into u.
  intro_state.
  unfold visit.
  hoare_auto_s.
  hoare_cons (Hoare_whileP _ _ (fun s => v ∈ s)).
  {
    intros; subst.
    left; auto. 
  }
  hoare_auto; simpl.
  hoare_cons_pre H.
Qed.

Definition neighbor_visit (u: V) (s: St) : Prop :=
  forall v, step u v -> v ∈ s.

Lemma DFS_visit_neighbor (u: V):
  Hoare ATrue
        (DFS u)
        (fun _ s => u ∈ s /\ neighbor_visit u s).
Proof.
  unfold DFS.
  hoare_fix_lv_auto_conj V unit tt.
  apply DFS_keep_visit.
  simpl; intros; clear c u; rename a into u.
  unfold DFS_f.
  intro_state; clear H1.
  unfold visit; hoare_auto_s.
  hoare_cons (Hoare_whileP _ _ (fun s => u ∈ s)).
  {
    intros; subst.
    right; easy.
  }
  {
    simpl; intros; split; try tauto.
    unfold neighbor_visit; destruct H1.
    intros; apply NNPP; intros con.
    apply H2.
    exists v; tauto.
  }
  hoare_auto; simpl.
  hoare_cons_pre (H a u).
Qed.

Lemma DFS_visit_self (u: V):
  Hoare ATrue
        (DFS u)
        (fun _ s => u ∈ s).
Proof.
  unfold DFS.
  hoare_fix_lv_auto_conj V unit tt.
  apply DFS_keep_visit.
  simpl; clear u; intros W IH _ u _.
  unfold DFS_f.
  intro_state; clear H.
  unfold visit; hoare_auto_s.
  hoare_cons (Hoare_whileP _ _ (fun s => u ∈ s)).
  intros; subst; right; easy.
  hoare_auto; simpl.
  hoare_cons_pre IH.
Qed.

Definition visited_reachable (u: V) (s: St) : Prop :=
  forall v, v ∈ s -> reachable u v.

Lemma visited_reachable_add (u v: V) (s1 s2: St):
  visited_reachable u s1 ->
  reachable u v ->
  s2 = s1 ∪ Sets.singleton v ->
  visited_reachable u s2.
Proof.
  unfold visited_reachable; intros.
  rewrite H1 in H2; destruct H2.
  apply H; auto.
  inversion H2; subst; easy.
Qed.

Lemma DFS_visit_reachable (u: V):
  Hoare (fun s => s == ∅)
        (DFS u)
        (fun _ => visited_reachable u).
Proof.
  unfold DFS.
  hoare_cons (Hoare_fix 
    (fun v s => reachable u v /\ visited_reachable u s)
    (fun _ _ => visited_reachable u)).
  {
    split; try easy.
    unfold visited_reachable.
    intros v; rewrite H. 
    sets_unfold; tauto.
  }
  intros W IH v.
  unfold DFS_f.
  intro_state; destruct H.
  unfold visit; hoare_auto_s; simpl.
  hoare_cons (Hoare_whileP _ _ (visited_reachable u)).
  intros; eapply visited_reachable_add; eauto.
  intro_state.
  destruct H1 as [_ Hs1].
  hoare_auto_s.
  hoare_cons_pre IH.
  intros; subst.
  split; auto.
  eapply reachable_step_reachable; eauto; tauto.
Qed.

Local Open Scope trace_scope.
Definition visited_in : (St * (@TR Tag St)) -> Prop :=
  fun '(s, tr) => forall v, v ∈ s -> tr |= have (t↑(In v)).

(** DFS Trace Prop *)
Lemma DFS_visited_In (u v: V):
  Hoare (fun '(s, tr) => s == ∅ /\ tr = nil)
        (DFS' u)
        (fun _ '(s, tr) => v ∈ s -> tr |= have (t↑(In v))).
Proof.
  unfold DFS'.
  apply Hoare_conseq_post with 
    (Q2:= fun _ => visited_in).
  { intros _ (s, tr) H; apply H. }
  clear v.
  hoare_cons_pre (Hoare_fix 
    (fun _ => visited_in) (fun _ _ => visited_in)).
  {
    intros (s, tr) [H _] v.
    unfold visited_in; rewrite H.
    sets_unfold; tauto.
  }
  clear u; intros W IH u.
  unfold trace_call_f, DFS_f'.
  intro_state_pair.
  hoare_bind' Hoare_track_s.
  unfold visit.
  hoare_auto_G.
  apply Hoare_conseq_pre with (P2 := visited_in).
  {
    intros (s0, tr) Hs0; inversion Hs0; subst; clear Hs0.
    intros v Hv; subst.
    apply app_have_atom.
    destruct Hv.
    - left; apply H; auto.
    - right; sets_unfold in H0; subst.
      apply singleton_have_atom.
      simpl; auto.
  }
  clear s H l.
  hoare_bind Hoare_whileP.
  {
    intro_state_pair.
    hoare_auto_G.
    my_destruct H0; subst.
    hoare_cons_pre IH.
    intros (?, ?) ?. 
    inversion H0; subst; tauto.
  }
  simpl; clear a.
  hoare_cons_pre (Hoare_track_inv); intros. 
  apply app_have_atom; left.
  apply H; auto.
Qed.

Lemma DFS_in_then_visited (u v: V):
  Hoare (fun '(s, tr) => tr = nil)
        (DFS' u)
        (fun _ '(_, tr) => trace_in_implies (fun _ => ATrue) neighbor_visit v tr).
Proof.
  eapply Hoare_trace_in_implies; simpl.
  clear u v; intros u.
  hoare_cons_post DFS_visit_neighbor.
Qed.

Definition visit_persist (v: V) :St * (TR (@Tag V) St) -> Prop :=
  fun '(s, tr) =>
  tr |= have (s↑(fun s => v ∈ s)) -> v ∈ s.

Lemma visit_persist_track (v: V) (s: St) (t: Tag) (tr: TR (@Tag V) St):
  visit_persist v (s, tr) ->
  visit_persist v (s, tr ++ (t , s) :: nil).
Proof.
  unfold visit_persist; intros.
  rewrite app_have_atom in H0; destruct H0.
  - auto.
  - apply @singleton_have_atom with (T:= Tag) in H0.
    simpl in H0; auto.
Qed.

Lemma DFS_visit_persist (u v: V):
  Hoare (fun '(s, tr) => s == ∅ /\ tr = nil)
        (DFS' u)
        (fun _ => visit_persist v).
Proof.
  match goal with 
  | |- Hoare _ _ ?Q => apply Hoare_conseq_pre with (P2 := Q tt)
  end.
  {
    intros (s, tr) [_ H].
    subst; unfold visit_persist; intros.
    apply not_nil_have in H; tauto.
  }
  unfold DFS', trace_call.
  hoare_fix_nolv_auto V; clear u.
  intros W IH u.
  unfold trace_call_f, DFS_f'.
  hoare_bind Hoare_track_inv.
  apply visit_persist_track; auto.
  simpl; clear a.
  intro_state_pair.
  unfold visit; hoare_auto_G.
  apply Hoare_conseq_pre with (P2 := visit_persist v).
  {
    intros (?, ?) Hs.
    inversion Hs; subst.
    unfold visit_persist; intros.
    left; apply H; auto.
  }
  hoare_bind Hoare_whileP.
  {
    intro_state_pair.
    hoare_auto_G.
    my_destruct H1; subst.
    hoare_cons_pre IH.
    intros ? ?; subst; tauto. 
  }
  hoare_cons_pre Hoare_track_inv.
  intros ? ?; apply visit_persist_track.
Qed.

Lemma DFS_neighbor_visited' (u v: V):
  Hoare (fun '(s, tr) => s == ∅ /\ tr = nil)
        (DFS' u)
        (fun _ '(s, tr) => v ∈ s -> neighbor_visit v s).
Proof.
  unfold neighbor_visit.
  apply Hoare_conseq_post with (Q2:= fun a x => 
    forall v0, (fun v0 (a:unit) '(s, _) => v ∈ s -> step v v0 -> v0 ∈ s) v0 a x).
  intros _ (s, tr); intros; auto.
  apply (hoare_bind_forall); intros v0.
  eapply Hoare_conseq_post.
  2:{
    do 2 (apply Hoare_conj).
    apply DFS_visited_In with (v:=v).
    hoare_cons_pre (DFS_in_then_visited _ v).
    intros (s, tr); tauto.
    apply DFS_visit_persist with (v:=v0).
    hoare_cons_pre trace_call_local_out.
    unfold ATrue; tauto.
  }
  simpl; unfold trace_in_implies, visit_persist, neighbor_visit.
  intros _ (s, tr); intros.
  my_destruct H.
  apply H2.
  unfold trace_in_implies in H3.
  apply have_tsatom_satom in H3.
  eapply have_atom_conseq. 2: apply H3. 
  unfold sAtom; intros (?, ?); intros; auto.
  eapply have_atom_conseq. 2: apply H; auto. 
  unfold tsAtom, ATrue; intros (?, ?); intros; auto.
Qed.

Theorem DFS_neighbor_visited (u: V):
  Hoare (fun s => s == ∅)
        (DFS u)
        (fun _ s => forall v, v ∈ s -> neighbor_visit v s).
Proof.
  apply hoare_bind_forall; intros v.
  eapply Hoare_fromG.
  apply Gequiv_DFS.
  apply DFS_neighbor_visited'.
  intros; exists nil; auto.
Qed.

(** Static Proof for reachable_visited *)

Lemma path_exists_pair: forall v u (P: V -> Prop),
  reachable v u -> P v -> ~ P u -> 
    exists w z, reachable v z /\ step z w /\ P z /\ ~ P w.
Proof.
  intros.
  apply NNPP; intros Hnot.
  assert 
  (Hs: forall w z, reachable v z -> step z w -> P z -> P w).
  {
    intros.
    apply NNPP; intros wnot.
    apply Hnot.
    exists w, z; tauto.
  }
  clear Hnot.
  assert 
  (HP: forall w, reachable v w -> P w).
  {
    intros w Hr.
    induction Hr.
    change (nsteps (step) x v w) with ((v, w) ∈ nsteps (step) x) in H2.
    rewrite nsteps_nsteps' in H2.
    sets_unfold in H2.
    revert H2; revert w.
    rename x into n; induction n; simpl; intros.
    - inversion H2.
      subst; auto.
    - sets_unfold in H2.
      destruct H2 as [z [? ?]].
      pose proof (IHn _ H2).
      change (nsteps' (step) n v z) with ((v, z) ∈ (nsteps' (step) n)) in H2.
      rewrite <- nsteps_nsteps' in H2.
      assert (reachable v z).
      { 
         sets_unfold in H2; unfold reachable, clos_refl_trans; sets_unfold.
         exists n; auto. 
      }
      eapply Hs; eauto. 
  }
  apply HP in H; tauto.
Qed.

Lemma pair_contra: forall v u s,
  reachable v u -> v ∈ s -> ~ u ∈ s ->
  (forall v, v ∈ s -> neighbor_visit v s) -> False.
Proof.
  intros.
  pose proof (path_exists_pair v u s H H0 H1).
  destruct H3 as (w & z & ?).
  unfold neighbor_visit in H2.
  destruct H3 as (? & ? & ? & ?).
  apply H6.
  apply (H2 z); tauto.
Qed.

Theorem DFS_visited_reachable:
  forall (v u: V),
    Hoare (fun s => s == ∅)
          (DFS v)
          (fun _ s => u ∈ s <-> reachable v u).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:{
    eapply Hoare_conj.
    eapply Hoare_conj.
    hoare_cons_pre DFS_visit_self.
    unfold ATrue; tauto. 
    apply DFS_visit_reachable.
    apply DFS_neighbor_visited. 
  }
  simpl; intros.
  split; intros.
  - destruct H.
    apply H; auto. 
  - apply NNPP; intros Hu.
    sets_unfold in H; sets_unfold in Hu; sets_unfold.
    my_destruct H.
    eapply pair_contra; sets_unfold; eauto; auto.
Qed.

End DFS.
