Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Require Import Recdef.
Require Import SetsClass.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.Syntax.
From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import SCC.
Import ListNotations.

Local Open Scope Z_scope.

(* ================================================================ *)
(* DiGraph: proof-carrying class for directed graphs, used by Kosaraju.SCC *)
(* ================================================================ *)

Class DiGraph (V E : Type) : Type := {
  dig_vvalid : V -> Prop;
  dig_evalid : E -> Prop;
  dig_fst : E -> V;
  dig_snd : E -> V;
  dig_listV : list V;
  dgp_fst_valid     : forall e, dig_evalid e -> dig_vvalid (dig_fst e);
  dgp_snd_valid     : forall e, dig_evalid e -> dig_vvalid (dig_snd e);
  dgp_list_complete : forall v, dig_vvalid v -> In v dig_listV;
}.

Arguments dig_vvalid {V E} _ _.
Arguments dig_evalid {V E} _ _.
Arguments dig_fst {V E} _ _.
Arguments dig_snd {V E} _ _.
Arguments dig_listV {V E} _.

Record dig_step_aux {V E} (g : DiGraph V E) (e : E) (x y : V) : Prop := DigStepAux {
  dsa_valid_edge : dig_evalid g e;
  dsa_valid_src  : dig_vvalid g x;
  dsa_valid_tgt  : dig_vvalid g y;
  dsa_fst_eq     : dig_fst g e = x;
  dsa_snd_eq     : dig_snd g e = y;
}.

Arguments dig_step_aux {V E} _ _ _ _.

#[export] Instance dig_Graph (V E : Type) : Graph (DiGraph V E) V E := {|
  vvalid   := fun g v   => dig_vvalid g v;
  evalid   := fun g e   => dig_evalid g e;
  step_aux := fun g e x y => dig_step_aux g e x y;
|}.

#[export] Instance dig_GValid (V E : Type) : GValid (DiGraph V E) :=
  fun _ => True.

#[export] Instance dig_StepValid (V E : Type) : StepValid (DiGraph V E) V E.
Proof.
  split; intros g e x y Hstep.
  - destruct Hstep as [He Hx Hy Hfx Hsy]; exact Hx.
  - destruct Hstep as [He Hx Hy Hfx Hsy]; exact Hy.
  - destruct Hstep as [He Hx Hy Hfx Hsy]; exact He.
Defined.

#[export] Instance dig_FiniteGraph (V E : Type) : FiniteGraph (DiGraph V E) V E.
Proof.
  refine {| listV := dig_listV; |}.
  intros g Hg Hv.
  apply dgp_list_complete; auto.
Defined.

(* ================================================================ *)
(* Section 1: 2-SAT Syntax                                          *)
(* ================================================================ *)

Definition literal : Type := (Z * bool)%type.

Definition negate (l : literal) : literal :=
  (fst l, negb (snd l)).

Lemma negate_involutive : forall l, negate (negate l) = l.
Proof.
  destruct l as [v b]; unfold negate; simpl.
  rewrite Bool.negb_involutive; auto.
Qed.

Lemma negate_injective : forall l1 l2, negate l1 = negate l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  apply (f_equal negate) in H; rewrite !negate_involutive in H; auto.
Qed.

Definition clause : Type := literal * literal.
Definition formula : Type := list clause.
Definition assignment : Type := Z -> bool.

Definition eval_literal (a : assignment) (l : literal) : bool :=
  let (v, sign) := l in
  if sign then a v else negb (a v).

Lemma eval_negate : forall a l,
  eval_literal a (negate l) = negb (eval_literal a l).
Proof.
  intros a [v b]; unfold eval_literal, negate; simpl.
  destruct b; simpl; auto.
  symmetry; apply Bool.negb_involutive.
Qed.

Definition satisfies (a : assignment) (f : formula) : Prop :=
  forall c, In c f ->
    eval_literal a (fst c) = true \/ eval_literal a (snd c) = true.

Definition satisfiable (f : formula) : Prop := exists a, satisfies a f.

(* ================================================================ *)
(* Section 2: Validity Constraints                                   *)
(* ================================================================ *)

Definition valid_literal (numVars : Z) (l : literal) : Prop :=
  let (v, _) := l in 1 <= v <= numVars.

Lemma valid_literal_negate : forall numVars l,
  valid_literal numVars l -> valid_literal numVars (negate l).
Proof.
  intros numVars [v b] H; unfold valid_literal in *; simpl in *.
  unfold negate; simpl; auto.
Qed.

Definition valid_clause (numVars : Z) (c : clause) : Prop :=
  valid_literal numVars (fst c) /\ valid_literal numVars (snd c).

Definition valid_formula (numVars : Z) (f : formula) : Prop :=
  forall c, In c f -> valid_clause numVars c.

(* ================================================================ *)
(* Section 3: Implication Graph Construction                         *)
(* ================================================================ *)

Fixpoint literal_list_aux (n : nat) (base : Z) : list literal :=
  match n with
  | O => nil
  | S n' => (base, true) :: (base, false) :: literal_list_aux n' (base + 1)
  end.

Definition literal_list (numVars : Z) : list literal :=
  literal_list_aux (Z.to_nat numVars) 1.

Lemma literal_list_aux_in : forall n (base : Z) (v : Z) (b : bool),
  (exists (k : nat), (k < n)%nat /\ v = base + Z.of_nat k) -> In (v, b) (literal_list_aux n base).
Proof.
  induction n.
  - simpl; intros base v b H; destruct H as [k [Hlt _]]; exfalso; lia.
  - simpl; intros base v b H; destruct H as [k [Hlt Heq]].
    destruct k as [| k'].
    + destruct b; [left | right; left]; simpl; f_equal; lia.
    + destruct b; [right; right | right; right]; apply IHn; exists k'; split; [lia | rewrite Heq; lia | lia | rewrite Heq; lia].
Qed.

Lemma literal_list_complete : forall numVars l,
  valid_literal numVars l -> In l (literal_list numVars).
Proof.
  intros numVars [v b] [Hlow Hhigh].
  unfold literal_list.
  apply literal_list_aux_in with (base := 1).
  exists (Z.to_nat (v - 1)).
  split.
  - apply Z2Nat.inj_lt; lia.
  - rewrite Z2Nat.id by lia; lia.
Qed.

Definition nth_clause (f : formula) (i : Z) : clause :=
  nth (Z.to_nat i) f ((0, false), (0, false)).

Lemma nth_clause_in : forall f i, 0 <= i < Zlength f ->
  In (nth_clause f i) f.
Proof.
  intros f i Hrange.
  unfold nth_clause.
  apply nth_In.
  rewrite (Zlength_correct f) in Hrange.
  lia.
Qed.

Definition implication_graph (f : formula) (numVars : Z)
  (Hvalid : valid_formula numVars f) : DiGraph literal Z.
Proof.
  refine {|
    dig_vvalid := fun (l : literal) => valid_literal numVars l;
    dig_evalid := fun (e : Z) => 0 <= e < 2 * Zlength f;
    dig_fst := fun (e : Z) =>
      let i := e / 2 in
      let c := nth_clause f i in
      if Z.even e then negate (fst c) else negate (snd c);
    dig_snd := fun (e : Z) =>
      let i := e / 2 in
      let c := nth_clause f i in
      if Z.even e then snd c else fst c;
    dig_listV := literal_list numVars;
  |}.
  - intros e He.
    simpl in *.
    destruct He as [He1 He2].
    set (i := e / 2).
    assert (Hi_range : 0 <= i < Zlength f)
      by (split; [apply Z.div_pos; [exact He1 | lia] |
                  apply Z.div_lt_upper_bound; [lia | exact He2]]).
    destruct (Z.even e) eqn: Heven; simpl.
    + apply valid_literal_negate.
      destruct (Hvalid (nth_clause f i) (nth_clause_in f i Hi_range)) as [Hl1 _].
      exact Hl1.
    + apply valid_literal_negate.
      destruct (Hvalid (nth_clause f i) (nth_clause_in f i Hi_range)) as [_ Hl2].
      exact Hl2.
  - intros e He.
    simpl in *.
    destruct He as [He1 He2].
    set (i := e / 2).
    assert (Hi_range : 0 <= i < Zlength f)
      by (split; [apply Z.div_pos; [exact He1 | lia] |
                  apply Z.div_lt_upper_bound; [lia | exact He2]]).
    destruct (Z.even e) eqn: Heven; simpl.
    + destruct (Hvalid (nth_clause f i) (nth_clause_in f i Hi_range)) as [_ Hl2].
      exact Hl2.
    + destruct (Hvalid (nth_clause f i) (nth_clause_in f i Hi_range)) as [Hl1 _].
      exact Hl1.
  - intros v Hv.
    simpl in *.
    apply literal_list_complete; auto.
Defined.

Lemma implication_graph_gvalid : forall f numVars
  (Hvalid : valid_formula numVars f),
  gvalid (implication_graph f numVars Hvalid).
Proof.
  intros; exact I.
Qed.

Lemma step_implication : forall f numVars
  (Hvalid : valid_formula numVars f),
  forall c, In c f ->
  step (implication_graph f numVars Hvalid) (negate (fst c)) (snd c) /\
  step (implication_graph f numVars Hvalid) (negate (snd c)) (fst c).
Proof.
  intros f numVars Hvalid [l1 l2] Hc.
  set (g := implication_graph f numVars Hvalid).
  assert (Hpos: exists i : Z, 0 <= i < Zlength f /\
    nth (Z.to_nat i) f ((0,false),(0,false)) = (l1, l2)).
  { apply In_nth with (d := ((0,false),(0,false))) in Hc.
    destruct Hc as [i [Hrange Hnth]].
    exists (Z.of_nat i); split.
    - split; [apply (Nat2Z.is_nonneg i) |].
      apply Nat2Z.inj_lt in Hrange.
      rewrite Zlength_correct; assumption.
    - rewrite Nat2Z.id; auto. }
  destruct Hpos as [i [Hrange Hnth]].
  pose (e1 := 2 * i).
  pose (e2 := 2 * i + 1).
  assert (He1_valid : dig_evalid g e1).
  { unfold g, implication_graph.
    unfold e1; destruct Hrange as [Hlow Hhigh].
    split; [lia | apply Zmult_lt_compat_l; [lia | exact Hhigh]]. }
  assert (He2_valid : dig_evalid g e2).
  { unfold g, implication_graph.
    unfold e2; destruct Hrange as [Hlow Hhigh].
    split; [lia |].
    apply Z.lt_le_trans with (2 * (i + 1)).
    - nia.
    - apply Zmult_le_compat_l; [lia |].
      nia. }
  assert (Hvalid_c : valid_clause numVars (l1, l2)) by (apply Hvalid; exact Hc).
  destruct Hvalid_c as [Hvalid_l1 Hvalid_l2].
  assert (Hstep1 : step g (negate l1) l2).
  { unfold step; exists e1.
    apply (DigStepAux literal Z g e1 (negate l1) l2 He1_valid
      (valid_literal_negate numVars l1 Hvalid_l1) Hvalid_l2).
    - unfold g, implication_graph, dig_fst; simpl.
      unfold e1, nth_clause.
      rewrite (Z.mul_comm 2 i), Z.div_mul by lia.
      rewrite Z.even_mul, Z.even_2; simpl.
      rewrite Bool.orb_true_r; simpl.
      rewrite Hnth; reflexivity.
    - unfold g, implication_graph, dig_snd; simpl.
      unfold e1, nth_clause.
      rewrite (Z.mul_comm 2 i), Z.div_mul by lia.
      rewrite Z.even_mul, Z.even_2; simpl.
      rewrite Bool.orb_true_r; simpl.
      rewrite Hnth; reflexivity. }
  assert (Hstep2 : step g (negate l2) l1).
  { unfold step; exists e2.
    assert (e2_div_2_eq_i : e2 / 2 = i).
    { unfold e2. rewrite (Z.mul_comm 2 i), Z.div_add_l by lia.
      rewrite Z.div_small; [|lia]. ring. }
    assert (e2_even_false : Z.even e2 = false).
    { unfold e2. apply Z.even_odd. }
    apply (DigStepAux literal Z g e2 (negate l2) l1 He2_valid
      (valid_literal_negate numVars l2 Hvalid_l2) Hvalid_l1).
    - unfold g, implication_graph, dig_fst; simpl.
      unfold nth_clause.
      rewrite e2_div_2_eq_i.
      rewrite e2_even_false; simpl.
      rewrite Hnth; reflexivity.
    - unfold g, implication_graph, dig_snd; simpl.
      unfold nth_clause.
      rewrite e2_div_2_eq_i.
      rewrite e2_even_false; simpl.
      rewrite Hnth; reflexivity.
  }
  split; [exact Hstep1 | exact Hstep2].
Qed.

(* ================================================================ *)
(* Section 4: Forward Direction                                      *)
(* ================================================================ *)

Definition mutually_reachable (g : DiGraph literal Z) (u v : literal) : Prop :=
  reachable g u v /\ reachable g v u.

Definition no_conflict (g : DiGraph literal Z) (numVars : Z) : Prop :=
  forall v, 1 <= v <= numVars ->
    ~ mutually_reachable g (v, true) (v, false).

Lemma eval_preserved_along_step : forall f numVars a,
  satisfies a f ->
  forall Hvalid : valid_formula numVars f,
  forall l1 l2,
  step (implication_graph f numVars Hvalid) l1 l2 ->
  eval_literal a l1 = true -> eval_literal a l2 = true.
Proof.
  intros f numVars a Hsat Hvalid l1 l2 Hstep Heval.
  set (g := implication_graph f numVars Hvalid) in *.
  destruct Hstep as [e Hstep].
  destruct Hstep as [He Hx Hy Hfx Hsy].
  unfold g, implication_graph in Hfx, Hsy; simpl in Hfx, Hsy.
  rename He into Hrange.
  destruct Hrange as [He1 He2].
  set (i := e / 2).
  set (c := nth_clause f i).
  assert (Hi_range : 0 <= i < Zlength f).
  { unfold i; split.
    - apply Z.div_pos; [exact He1 | apply Z.lt_0_2].
    - apply Z.div_lt_upper_bound; [apply Z.lt_0_2 | exact He2]. }
  revert Hfx Hsy.
  destruct (Z.even e) eqn: Heven; intros Hfx Hsy; simpl in Hfx, Hsy;
    unfold c, i in Hfx, Hsy.
  - rewrite <- Hfx in Heval; rewrite <- Hsy.
    rewrite eval_negate in Heval.
    destruct (Hsat (nth_clause f (e/2)) (nth_clause_in f i Hi_range))
      as [Hc1 | Hc2].
    + rewrite Hc1 in Heval; simpl in Heval; discriminate.
    + exact Hc2.
  - rewrite <- Hfx in Heval; rewrite <- Hsy.
    rewrite eval_negate in Heval.
    destruct (Hsat (nth_clause f (e/2)) (nth_clause_in f i Hi_range))
      as [Hc1 | Hc2].
    + exact Hc1.
    + rewrite Hc2 in Heval; simpl in Heval; discriminate.
Qed.

Lemma eval_preserved_along_path : forall f numVars a,
  satisfies a f ->
  forall Hvalid : valid_formula numVars f,
  forall l1 l2,
  reachable (implication_graph f numVars Hvalid) l1 l2 ->
  eval_literal a l1 = true -> eval_literal a l2 = true.
Proof.
  intros f numVars a Hsat Hvalid l1 l2 Hreach Heval.
  unfold reachable in Hreach.
  unfold reachable in Hreach.
  let X := eval unfold clos_refl_trans in Hreach in
  change Hreach with X.
  destruct Hreach as [n Hn].
  induction n as [| n IH] in l1, l2, Hn, Heval |- *.
  - simpl nsteps in Hn.
    unfold Rels.id in Hn.
    simpl in Hn.
    subst; exact Heval.
  - simpl nsteps in Hn.
    unfold Rels.concat in Hn.
    destruct Hn as [z [Hz1 Hz2]].
    apply (IH z l2 Hz2).
    apply (eval_preserved_along_step f numVars a Hsat Hvalid l1 z Hz1 Heval).
Qed.

Lemma forward : forall f numVars
  (Hvalid : valid_formula numVars f),
  satisfiable f -> no_conflict (implication_graph f numVars Hvalid) numVars.
Proof.
  intros f numVars Hvalid [a Hsat] v Hv Hmr.
  set (g := implication_graph f numVars Hvalid) in *.
  destruct Hmr as [Hftb Hbtf].
  destruct (classic (a v = true)) as [Hav | Hav].
  - assert (Heval: eval_literal a (v, true) = true)
      by (unfold eval_literal; simpl; rewrite Hav; auto).
    pose proof (eval_preserved_along_path f numVars a Hsat Hvalid
      (v, true) (v, false) Hftb Heval) as Heval_false.
    unfold eval_literal in Heval_false; simpl in Heval_false.
    rewrite Hav in Heval_false; simpl in Heval_false.
    discriminate.
  - apply Bool.not_true_is_false in Hav.
    assert (Heval: eval_literal a (v, false) = true)
      by (unfold eval_literal; simpl; rewrite Hav; auto).
    pose proof (eval_preserved_along_path f numVars a Hsat Hvalid
      (v, false) (v, true) Hbtf Heval) as Heval_true.
    unfold eval_literal in Heval_true; simpl in Heval_true.
    rewrite Hav in Heval_true; simpl in Heval_true.
    discriminate.
Qed.

(* ================================================================ *)
(* Section 5: Backward Direction                                     *)
(* ================================================================ *)

Section BACKWARD.

Variables (f : formula) (numVars : Z).
Hypothesis (Hvalid : valid_formula numVars f).

Let g : DiGraph literal Z := implication_graph f numVars Hvalid.

Let Hgvalid_g : gvalid g := implication_graph_gvalid f numVars Hvalid.

Lemma backward (Hnc : no_conflict g numVars) : satisfiable f.
Proof.
  destruct (scc_partition_exists g (Hgvalid := Hgvalid_g))
    as [sccs [[Hcover [Hisscc Hdisjoint]] Hnodup]].
  destruct (exists_topological_order g sccs
              (conj Hcover (conj Hisscc Hdisjoint)) Hnodup)
    as [prec [Hcond_edge [Htotal [Hirrefl Htrans]]]].
  set (scc_of := fun (l : literal) =>
    epsilon (inhabits (fun (_ : literal) => True)) (fun s : literal -> Prop => In s sccs /\ s l)).
  assert (scc_of_spec : forall (l : literal), valid_literal numVars l ->
    In (scc_of l) sccs /\ (scc_of l) l).
  { intros l Hv; unfold scc_of.
    assert (Hex : exists s, In s sccs /\ s l) by (apply Hcover; auto).
    exact (epsilon_spec (inhabits (fun (_ : literal) => True))
      (fun s : literal -> Prop => In s sccs /\ s l) Hex). }
  assert (scc_of_neq : forall (v : Z), 1 <= v <= numVars ->
    scc_of (v, true) <> scc_of (v, false)).
  { intros v Hv_range Heq.
    apply (Hnc v Hv_range).
    assert (Hscc : is_SCC g (scc_of (v, true))) by
      (apply Hisscc; eapply scc_of_spec; eauto; exact (conj Hv_range eq_refl)).
    destruct Hscc as [_ [Hmr _]].
    apply (Hmr (v, true) (v, false));
      [eapply scc_of_spec; eauto; exact (conj Hv_range eq_refl)
      | rewrite Heq; eapply scc_of_spec; eauto; exact (conj Hv_range eq_refl)]. }
  set (a := fun (v : Z) =>
    if excluded_middle_informative (1 <= v <= numVars) then
      if excluded_middle_informative (prec (scc_of (v, false)) (scc_of (v, true)))
      then true else false
    else false).
  assert (eval_false_prec : forall (l : literal) (Hv : valid_literal numVars l),
    eval_literal a l = false -> prec (scc_of l) (scc_of (negate l))).
  { intros l Hv Hfalse.
    destruct l as [v b]; destruct b.
    - unfold eval_literal, a in Hfalse; simpl in Hfalse.
      destruct excluded_middle_informative as [Hv_range|Hnot]; [|exfalso; exact (Hnot Hv)].
      destruct excluded_middle_informative as [Hprec_v|Hnotprec_v].
      + exfalso.
        assert (Hneq : scc_of (v, true) <> scc_of (v, false))
          by (apply scc_of_neq; auto; exact Hv_range).
        assert (Hin1 : In (scc_of (v, true)) sccs)
          by (eapply scc_of_spec; eauto; exact (conj Hv_range eq_refl)).
        assert (Hin2 : In (scc_of (v, false)) sccs)
          by (eapply scc_of_spec; eauto; exact (conj Hv_range eq_refl)).
        discriminate.
      + assert (Hneq : scc_of (v, true) <> scc_of (v, false))
          by (apply scc_of_neq; auto; exact Hv_range).
        assert (Hin1 : In (scc_of (v, true)) sccs)
          by (eapply scc_of_spec; eauto; exact (conj Hv_range eq_refl)).
        assert (Hin2 : In (scc_of (v, false)) sccs)
          by (eapply scc_of_spec; eauto; exact (conj Hv_range eq_refl)).
        destruct (Htotal (scc_of (v, true)) (scc_of (v, false)) Hin1 Hin2 Hneq)
          as [Hord|Hord'];
        [exact Hord
        |exfalso; exact (Hnotprec_v Hord')].
    - unfold eval_literal, a in Hfalse; simpl in Hfalse.
      destruct excluded_middle_informative as [Hv_range|Hnot]; [|exfalso; exact (Hnot Hv)].
      destruct excluded_middle_informative as [Hprec_v|Hnotprec_v]; [exact Hprec_v|discriminate]. }
  assert (step_cond_or_eq : forall (l1 l2 : literal),
    step g l1 l2 ->
    (scc_of l1 = scc_of l2) \/
    condensation_edge g sccs (scc_of l1) (scc_of l2)).
  { intros l1 l2 Hstep.
    destruct Hstep as [e Hstep].
    destruct Hstep as [He Hx Hy Hfx Hsy].
    subst l1 l2.
    assert (Hvx : valid_literal numVars (dig_fst g e))
      by (unfold g, implication_graph; simpl; exact Hx).
    assert (Hvy : valid_literal numVars (dig_snd g e))
      by (unfold g, implication_graph; simpl; exact Hy).
    destruct (classic (scc_of (dig_fst g e) = scc_of (dig_snd g e))) as [Heq|Hneq];
      [left; auto| right].
    destruct (scc_of_spec (dig_fst g e) Hvx) as [Hin1 Hl1].
    destruct (scc_of_spec (dig_snd g e) Hvy) as [Hin2 Hl2].
    unfold condensation_edge.
    repeat split; auto.
    exists (dig_fst g e), (dig_snd g e); repeat split; auto.
    unfold step; exists e.
    exact (DigStepAux literal Z g e (dig_fst g e) (dig_snd g e) He Hx Hy eq_refl eq_refl). }
  exists a.
  unfold satisfies; intros [l1 l2] Hc.
  destruct (classic (eval_literal a l1 = true \/ eval_literal a l2 = true)) as [Hdis|Hndis].
  - destruct Hdis as [H|H]; auto.
  - destruct (not_or_and _ _ Hndis) as [Hf1 Hf2].
    apply Bool.not_true_is_false in Hf1.
    apply Bool.not_true_is_false in Hf2.
  assert (Hvalid_c : valid_clause numVars (l1, l2)) by (apply Hvalid; exact Hc).
  destruct Hvalid_c as [Hv1 Hv2].
  assert (Hv_neg1 : valid_literal numVars (negate l1)) by (apply valid_literal_negate; auto).
  assert (Hv_neg2 : valid_literal numVars (negate l2)) by (apply valid_literal_negate; auto).
  assert (Hprec_l1 : prec (scc_of l1) (scc_of (negate l1))) by (apply eval_false_prec; auto).
  assert (Hprec_l2 : prec (scc_of l2) (scc_of (negate l2))) by (apply eval_false_prec; auto).
  assert (Hstep_edges : step g (negate l1) l2 /\ step g (negate l2) l1)
    by (apply (step_implication f numVars Hvalid (l1, l2) Hc)).
  destruct Hstep_edges as [Hstep1 Hstep2].
  assert (Hprec_dag1 : prec (scc_of (negate l1)) (scc_of l2) \/
                       scc_of (negate l1) = scc_of l2).
  { pose proof (step_cond_or_eq (negate l1) l2 Hstep1) as Hsc.
    destruct Hsc as [Heq | Hce].
    - right; exact Heq.
    - left; apply Hcond_edge; exact Hce. }
  assert (Hprec_dag2 : prec (scc_of (negate l2)) (scc_of l1) \/
                       scc_of (negate l2) = scc_of l1).
  { pose proof (step_cond_or_eq (negate l2) l1 Hstep2) as Hsc.
    destruct Hsc as [Heq | Hce].
    - right; exact Heq.
    - left; apply Hcond_edge; exact Hce. }
  assert (Hchain1 : prec (scc_of l1) (scc_of l2)).
  { destruct Hprec_dag1 as [Hedge|Heq].
    - apply (Htrans _ _ _ Hprec_l1 Hedge).
    - rewrite <- Heq; exact Hprec_l1. }
  assert (Hchain2 : prec (scc_of l2) (scc_of l1)).
  { destruct Hprec_dag2 as [Hedge|Heq].
    - apply (Htrans _ _ _ Hprec_l2 Hedge).
    - rewrite <- Heq; exact Hprec_l2. }
  assert (Hcycle : prec (scc_of l1) (scc_of l1))
    by (apply (Htrans _ _ _ Hchain1 Hchain2)).
  exfalso; exact (Hirrefl _ _ Hcycle Hcycle).
Qed.

End BACKWARD.

(* ================================================================ *)
(* Section 6: Main Theorem                                          *)
(* ================================================================ *)

Theorem two_sat_characterization :
  forall f numVars (Hvalid : valid_formula numVars f),
  (satisfiable f <-> no_conflict (implication_graph f numVars Hvalid) numVars).
Proof.
  intros f numVars Hvalid.
  split.
  - apply forward; auto.
  - intro Hnc.
    exact (backward f numVars Hvalid Hnc).
Qed.
