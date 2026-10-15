Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition RolesConsistent (n : Z) (comments : list (Z * Z * Z)) (roles : list Z) : Prop :=
  Zlength roles = n /\ Forall (fun r => r = 0 \/ r = 1) roles /\
  forall q, In q comments ->
    let ' (i, j, c) := q in
    (Znth (i - 1) roles 0 = 0 /\ Znth (j - 1) roles 0 = c) \/
    (Znth (i - 1) roles 0 = 1 /\ Znth (j - 1) roles 0 <> c).
Definition Pre (n : Z) (comments : list (Z * Z * Z)) : Prop :=
  (* Stated explicitly in the P053 solver Require, so dropped here:
       Zlength comments <= 500000 /\
       Forall (fun q => let ' (i, j, c) := q in 1 <= i <= n /\ 1 <= j <= n /\ i <> j /\ (c = 0 \/ c = 1)) comments /\
       1 <= n <= 200000   *)
  True.

(* How many of the crewmates are imposters: the roles marked with one. *)
Definition ImposterCount (roles : list Z) : Z := fold_right Z.add 0 roles.

Definition Spec (n : Z) (comments : list (Z * Z * Z)) (out : Z) : Prop :=
  (out = (- 1) /\ ~exists r, RolesConsistent n comments r) \/
  (out >= 0 /\ max_value_of_subset Z.le
    (fun v => exists r, RolesConsistent n comments r /\ v = ImposterCount r)
    (fun x => x) out).

(* ================================================================= *)
(*  Annotation interface for [solver].  The public specification above *)
(*  is intentionally untouched; everything below describes only the   *)
(*  solver's private array representation and loop states.             *)
(* ================================================================= *)

From AUXLib Require Import ListLib.

Definition comment_at (comments : list (Z * Z * Z)) (i : Z) : Z * Z * Z :=
  Znth i comments (0, 0, 0).

Definition edge_src (comments : list (Z * Z * Z)) (e : Z) : Z :=
  let '(u, v, _) := comment_at comments (e / 2) in
  if Z.even e then u else v.

Definition edge_dst (comments : list (Z * Z * Z)) (e : Z) : Z :=
  let '(u, v, _) := comment_at comments (e / 2) in
  if Z.even e then v else u.

Definition edge_wt (comments : list (Z * Z * Z)) (e : Z) : Z :=
  let '(_, _, w) := comment_at comments (e / 2) in w.

(* Following [nxt] from an edge index until [-1] yields this list. *)
Inductive AdjChain (ns : list Z) : Z -> list Z -> Prop :=
  | adj_end  : AdjChain ns (-1) nil
  | adj_cons : forall e rest,
      0 <= e -> AdjChain ns (Znth e ns 0) rest -> AdjChain ns e (e :: rest).

(* The arrays encode the first [k] comments as a forward star. *)
Definition ForwardStar (n cap k : Z) (hs ns ts ws : list Z)
    (comments : list (Z * Z * Z)) : Prop :=
  Zlength hs = n + 1 /\
  Zlength ns = 2 * cap /\ Zlength ts = 2 * cap /\ Zlength ws = 2 * cap /\
  0 <= k <= cap /\ k <= Zlength comments /\
  (forall e, 0 <= e < 2 * k ->
     Znth e ts 0 = edge_dst comments e /\ Znth e ws 0 = edge_wt comments e) /\
  (forall u, 1 <= u <= n ->
     exists es, AdjChain ns (Znth u hs 0) es /\ NoDup es /\
       forall e, In e es <-> (0 <= e < 2 * k /\ edge_src comments e = u)).

Definition ColourValues (n : Z) (cs : list Z) : Prop :=
  Zlength cs = n + 1 /\
  forall v, 1 <= v <= n ->
    Znth v cs 0 = -1 \/ Znth v cs 0 = 0 \/ Znth v cs 0 = 1.

Definition ParityRespected (comments : list (Z * Z * Z)) (cs : list Z) : Prop :=
  forall i, 0 <= i < Zlength comments ->
    let '(u, v, w) := comment_at comments i in
    Znth u cs 0 <> -1 -> Znth v cs 0 <> -1 ->
    Znth v cs 0 = Z.lxor (Znth u cs 0) w.

Definition ColouredClosed (comments : list (Z * Z * Z)) (cs : list Z) : Prop :=
  forall i, 0 <= i < Zlength comments ->
    let '(u, v, _) := comment_at comments i in
    (Znth u cs 0 <> -1 <-> Znth v cs 0 <> -1).

Definition OnSet (n : Z) (cs r : list Z) : Prop :=
  Zlength r = n /\
  (forall v, 1 <= v <= n -> Znth v cs 0 <> -1 ->
     Znth (v - 1) r 0 = 0 \/ Znth (v - 1) r 0 = 1) /\
  (forall v, 1 <= v <= n -> Znth v cs 0 = -1 -> Znth (v - 1) r 0 = 0).

Definition ConsistentOn (n : Z) (comments : list (Z * Z * Z))
    (cs r : list Z) : Prop :=
  OnSet n cs r /\
  forall i, 0 <= i < Zlength comments ->
    let '(u, v, w) := comment_at comments i in
    Znth u cs 0 <> -1 -> Znth v cs 0 <> -1 ->
    Znth (v - 1) r 0 = Z.lxor (Znth (u - 1) r 0) w.

Definition MaxImpostersOn (n : Z) (comments : list (Z * Z * Z))
    (cs : list Z) (t : Z) : Prop :=
  max_value_of_subset Z.le
    (fun x => exists r, ConsistentOn n comments cs r /\
                         x = fold_right Z.add 0 r)
    (fun x => x) t.

(* Initialization prefixes.  These are pure facts about whole-array ghost
   lists, so untouched cells (especially index 0) remain owned by [full]. *)
Definition HeadsInitialised (hs : list Z) (next : Z) : Prop :=
  forall v, 1 <= v < next -> Znth v hs 0 = -1.

Definition ColoursInitialised (cs : list Z) (next : Z) : Prop :=
  forall v, 1 <= v < next -> Znth v cs 0 = -1.

(* Machine-level range facts kept separate from the mathematical encoding. *)
Definition ForwardStarRanges (n k : Z) (hs ns ts ws : list Z) : Prop :=
  (forall u, 1 <= u <= n -> -1 <= Znth u hs 0 < 2 * k) /\
  (forall e, 0 <= e < 2 * k ->
     -1 <= Znth e ns 0 < 2 * k /\
     1 <= Znth e ts 0 <= n /\
     (Znth e ws 0 = 0 \/ Znth e ws 0 = 1)).

(* [vs] is exactly the set newly coloured since [before]. *)
Definition NewColourSet (n : Z) (before after vs : list Z) : Prop :=
  NoDup vs /\ Forall (fun v => 1 <= v <= n) vs /\
  (forall v, 1 <= v <= n ->
     (In v vs <-> Znth v before 0 = -1 /\ Znth v after 0 <> -1)) /\
  (forall v, 1 <= v <= n -> ~ In v vs ->
     Znth v after 0 = Znth v before 0).

Definition ColourCount (cs vertices : list Z) (bit count : Z) : Prop :=
  count = Z.of_nat
    (count_occ Z.eq_dec (map (fun v => Znth v cs 0) vertices) bit).

(* This is the propagation conclusion needed from connectivity, stated
   directly in the frontier instead of introducing a graph/reachability
   object.  Every consistent assignment differs from the current component
   colouring by one common bit. *)
Definition ComponentTwoChoices (n : Z) (comments : list (Z * Z * Z))
    (cs vertices : list Z) : Prop :=
  forall roles, RolesConsistent n comments roles ->
    exists flip, (flip = 0 \/ flip = 1) /\
      forall v, In v vertices ->
        Znth (v - 1) roles 0 = Z.lxor (Znth v cs 0) flip.

(* Every outgoing edge of a finished vertex has been traversed without a
   conflict; traversal also guarantees that the neighbour is coloured. *)
Definition FullyScanned (comments : list (Z * Z * Z))
    (cs finished : list Z) : Prop :=
  forall e, 0 <= e < 2 * Zlength comments -> In (edge_src comments e) finished ->
    Znth (edge_dst comments e) cs 0 <> -1 /\
    Znth (edge_dst comments e) cs 0 =
      Z.lxor (Znth (edge_src comments e) cs 0) (edge_wt comments e).

(* While scanning one vertex, [cur] names the remaining suffix of its
   forward-star chain; all edges outside that suffix are already respected. *)
Definition ScanAt (comments : list (Z * Z * Z)) (ns cs : list Z)
    (u cur : Z) : Prop :=
  exists remaining,
    AdjChain ns cur remaining /\
    (forall e, 0 <= e < 2 * Zlength comments ->
       edge_src comments e = u -> ~ In e remaining ->
       Znth (edge_dst comments e) cs 0 <> -1 /\
       Znth (edge_dst comments e) cs 0 =
         Z.lxor (Znth u cs 0) (edge_wt comments e)).

(* Stack-loop head: [finished] has been popped and fully scanned; [pending]
   is exactly the live stack prefix.  Counts cover [finished] only. *)
Definition ComponentFrontier (n : Z) (comments : list (Z * Z * Z))
    (before after finished pending : list Z) (c0 c1 : Z) : Prop :=
  ColourValues n after /\
  NewColourSet n before after (finished ++ pending) /\
  ComponentTwoChoices n comments after (finished ++ pending) /\
  FullyScanned comments after finished /\
  ColourCount after finished 0 c0 /\ ColourCount after finished 1 c1.

(* Inner adjacency-loop head.  The current [u] has already been counted but
   is not fully scanned until [cur] reaches [-1]. *)
Definition ComponentScan (n : Z) (comments : list (Z * Z * Z))
    (ns before after finished pending : list Z) (u cur c0 c1 : Z) : Prop :=
  ColourValues n after /\
  NewColourSet n before after (finished ++ u :: pending) /\
  ComponentTwoChoices n comments after (finished ++ u :: pending) /\
  FullyScanned comments after finished /\
  ScanAt comments ns after u cur /\
  ColourCount after (finished ++ u :: nil) 0 c0 /\
  ColourCount after (finished ++ u :: nil) 1 c1.

(* Normal stack-loop exit.  Besides the concrete frontier facts, this is the
   constructive B4 bridge used by the outer loop. *)
Definition ComponentComplete (n : Z) (comments : list (Z * Z * Z))
    (before after vertices : list Z) (c0 c1 : Z) : Prop :=
  ComponentFrontier n comments before after vertices nil c0 c1 /\
  ParityRespected comments after /\ ColouredClosed comments after /\
  (forall t, MaxImpostersOn n comments before t ->
     MaxImpostersOn n comments after (t + Z.max c0 c1)).

(* ================================================================= *)
(*  Strengthened retry interface.  The declarations above are retained *)
(*  unchanged; these additional Props close two structural gaps found  *)
(*  by the first VC-checking pass.                                     *)
(* ================================================================= *)

(* A role list that is consistent on one explicitly named vertex set.
   It is independent of contradictions in every other uncoloured
   component, unlike a global [RolesConsistent] premise. *)
Definition RolesConsistentOnVertices (n : Z)
    (comments : list (Z * Z * Z)) (vertices roles : list Z) : Prop :=
  Zlength roles = n /\
  (forall v, In v vertices ->
     Znth (v - 1) roles 0 = 0 \/ Znth (v - 1) roles 0 = 1) /\
  (forall i, 0 <= i < Zlength comments ->
     let '(u, v, w) := comment_at comments i in
     In u vertices -> In v vertices ->
     Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w).

(* B2 in component-local form: every locally consistent role assignment
   differs from the solver's colouring by one common bit. *)
Definition ComponentTwoChoicesLocal (n : Z)
    (comments : list (Z * Z * Z)) (cs vertices : list Z) : Prop :=
  forall roles, RolesConsistentOnVertices n comments vertices roles ->
    exists flip, (flip = 0 \/ flip = 1) /\
      forall v, In v vertices ->
        Znth (v - 1) roles 0 = Z.lxor (Znth v cs 0) flip.

(* The live chain really is the unscanned suffix for [u]: every edge still
   reachable from [cur] belongs to [u]'s forward-star adjacency list. *)
Definition ScanAtOwned (comments : list (Z * Z * Z)) (ns cs : list Z)
    (u cur : Z) : Prop :=
  ScanAt comments ns cs u cur /\
  exists remaining,
    AdjChain ns cur remaining /\
    forall e, In e remaining -> edge_src comments e = u.

Definition ComponentFrontierStrong (n : Z)
    (comments : list (Z * Z * Z))
    (before after finished pending : list Z) (c0 c1 : Z) : Prop :=
  ComponentFrontier n comments before after finished pending c0 c1 /\
  ComponentTwoChoicesLocal n comments after (finished ++ pending).

Definition ComponentScanStrong (n : Z)
    (comments : list (Z * Z * Z))
    (ns before after finished pending : list Z) (u cur c0 c1 : Z) : Prop :=
  ComponentScan n comments ns before after finished pending u cur c0 c1 /\
  ScanAtOwned comments ns after u cur /\
  ComponentTwoChoicesLocal n comments after (finished ++ u :: pending).

Definition ComponentCompleteStrong (n : Z)
    (comments : list (Z * Z * Z))
    (before after vertices : list Z) (c0 c1 : Z) : Prop :=
  ComponentComplete n comments before after vertices c0 c1 /\
  ComponentTwoChoicesLocal n comments after vertices.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma OnSet_fold_upper_bound__outer_loop_component_commit :
  forall n cs r,
    OnSet n cs r -> fold_right Z.add 0 r <= n.
Proof.
  intros n cs r [Hlen [Hcol Huncol]].
  assert (Hvalues : Forall (fun x => 0 <= x <= 1) r).
  {
    apply Forall_forall.
    intros x Hin.
    destruct (In_nth r x 0 Hin) as [k [Hk Hnth]].
    assert (Hindex : 0 <= Z.of_nat k < n).
    { rewrite Zlength_correct in Hlen. lia. }
    destruct (Z.eq_dec (Znth (Z.of_nat k + 1) cs 0) (-1))
      as [Hunvisited | Hvisited].
    - specialize (Huncol (Z.of_nat k + 1) ltac:(lia) Hunvisited).
      replace (Z.of_nat k + 1 - 1) with (Z.of_nat k) in Huncol by lia.
      unfold Znth in Huncol.
      rewrite Nat2Z.id in Huncol.
      rewrite Hnth in Huncol.
      lia.
    - specialize (Hcol (Z.of_nat k + 1) ltac:(lia) Hvisited).
      replace (Z.of_nat k + 1 - 1) with (Z.of_nat k) in Hcol by lia.
      unfold Znth in Hcol.
      rewrite Nat2Z.id in Hcol.
      rewrite Hnth in Hcol.
      destruct Hcol; lia.
  }
  clear Hcol Huncol.
  rewrite Zlength_correct in Hlen.
  assert (Hbinary : forall l,
      Forall (fun x => 0 <= x <= 1) l ->
      fold_right Z.add 0 l <= Z.of_nat (length l)).
  {
    intros l Hl.
    induction l as [|a l IH].
    - simpl. lia.
    - inversion Hl as [|a' l' Ha Htail]; subst.
      simpl.
      specialize (IH Htail).
      lia.
  }
  assert (Hsum : fold_right Z.add 0 r <= Z.of_nat (length r)).
  { apply Hbinary. exact Hvalues. }
  lia.
Qed.
Lemma MaxImpostersOn_upper_bound__outer_loop_component_commit :
  forall n comments cs t,
    MaxImpostersOn n comments cs t -> t <= n.
Proof.
  intros n comments cs t Hmax.
  unfold MaxImpostersOn, max_value_of_subset in Hmax.
  destruct Hmax as [x [Hobj Hvalue]].
  unfold max_object_of_subset in Hobj.
  sets_unfold in Hobj.
  destruct Hobj as [[r [Hconsistent Hsum]] _].
  simpl in Hvalue.
  subst x.
  subst t.
  apply OnSet_fold_upper_bound__outer_loop_component_commit with (cs := cs).
  exact (proj1 Hconsistent).
Qed.
Lemma Zlength_replace_Znth__forward_star_build_step :
  forall {A : Type} (l : list A) i (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A l i v.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  f_equal.
  generalize (Z.to_nat i); intro n.
  revert n; induction l; intro n; destruct n; simpl; auto.
Qed.
Lemma AdjChain_ext__forward_star_build_step :
  forall ns ns' cur es,
    AdjChain ns cur es ->
    (forall e, In e es -> Znth e ns' 0 = Znth e ns 0) ->
    AdjChain ns' cur es.
Proof.
  intros ns ns' cur es Hchain.
  induction Hchain as [| e rest He Htail IH]; intros Heq.
  - constructor.
  - constructor; [exact He|].
    rewrite Heq by (left; reflexivity).
    apply IH. intros x Hx. apply Heq. right; exact Hx.
Qed.
Lemma triple_src__forward_star_build_step : forall q : Z * Z * Z,
  (let '(u, _, _) := q in u) = fst (fst q).
Proof. intros [[u v] w]; reflexivity. Qed.
Lemma triple_dst__forward_star_build_step : forall q : Z * Z * Z,
  (let '(_, v, _) := q in v) = snd (fst q).
Proof. intros [[u v] w]; reflexivity. Qed.
Lemma triple_wt__forward_star_build_step : forall q : Z * Z * Z,
  (let '(_, _, w) := q in w) = snd q.
Proof. intros [[u v] w]; reflexivity. Qed.
Lemma fold_right_add_zero_of_Znth_zero__outer_loop_entry :
  forall r : list Z,
    (forall i, 0 <= i < Zlength r -> Znth i r 0 = 0) ->
    fold_right Z.add 0 r = 0.
Proof.
  induction r as [|a r IH]; intros Hzero; simpl; auto.
  pose proof (Zlength_nonneg r) as Hrlen.
  assert (Ha : a = 0).
  {
    specialize (Hzero 0).
    rewrite Zlength_cons in Hzero.
    specialize (Hzero ltac:(lia)).
    rewrite Znth0_cons in Hzero.
    exact Hzero.
  }
  rewrite Ha.
  apply IH.
  intros i Hi.
  specialize (Hzero (i + 1)).
  rewrite Zlength_cons in Hzero.
  specialize (Hzero ltac:(lia)).
  rewrite Znth_cons in Hzero by lia.
  replace (i + 1 - 1) with i in Hzero by lia.
  exact Hzero.
Qed.
Lemma Zlength_zeros__outer_loop_entry :
  forall n, 0 <= n -> Zlength (zeros n) = n.
Proof.
  intros n Hn.
  unfold zeros.
  rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma Znth_zeros__outer_loop_entry :
  forall n i, Znth i (zeros n) 0 = 0.
Proof.
  intros n i.
  unfold zeros.
  apply Znth_repeat.
Qed.
Lemma fold_right_add_zeros__outer_loop_entry :
  forall n, fold_right Z.add 0 (zeros n) = 0.
Proof.
  intros n.
  unfold zeros.
  induction (Z.to_nat n); simpl; auto.
Qed.
Lemma max_imposters_on_empty__outer_loop_entry :
  forall n comments cs,
    0 <= n ->
    Zlength cs = n + 1 ->
    (forall v, 1 <= v <= n -> Znth v cs 0 = -1) ->
    (forall i, 0 <= i < Zlength comments ->
       let '(u, v, _) := comment_at comments i in
       1 <= u <= n /\ 1 <= v <= n) ->
    MaxImpostersOn n comments cs 0.
Proof.
  intros n comments cs Hn Hcs Hall Hbounds.
  unfold MaxImpostersOn, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset.
  exists 0.
  split.
  - split.
    + exists (zeros n).
      split.
      * unfold ConsistentOn, OnSet.
        split.
        -- repeat split.
           ++ apply Zlength_zeros__outer_loop_entry; lia.
           ++ intros v Hv _.
              rewrite Znth_zeros__outer_loop_entry.
              left; reflexivity.
           ++ intros v Hv _.
              apply Znth_zeros__outer_loop_entry.
        -- intros i Hi.
           specialize (Hbounds i Hi).
           destruct (comment_at comments i) as [[u v] w] eqn:Hcomment.
           simpl in Hbounds.
           intros Hu _.
           rewrite (Hall u (proj1 Hbounds)) in Hu.
           contradiction.
      * symmetry; apply fold_right_add_zeros__outer_loop_entry.
    + intros b Hb.
      destruct Hb as [r [Hr Hb]].
      subst b.
      unfold ConsistentOn, OnSet in Hr.
      destruct Hr as [[Hrlen [_ Hrzero]] _].
      rewrite (fold_right_add_zero_of_Znth_zero__outer_loop_entry r).
      * lia.
      * intros i Hi.
        specialize (Hrzero (i + 1) ltac:(lia)).
        replace (i + 1 - 1) with i in Hrzero by lia.
        apply Hrzero.
        apply Hall; lia.
  - reflexivity.
Qed.
Lemma singleton_component_frontier_strong__outer_loop_entry :
  forall n comments before ks s,
    1 <= n -> 1 <= s <= n ->
    Zlength before = n + 1 ->
    Zlength ks = n + 1 ->
    ColourValues n before ->
    Znth s before 0 < 0 ->
    ComponentFrontierStrong n comments before
      (replace_Znth s 0 before) nil
      (sublist 0 1 (replace_Znth 0 s ks)) 0 0.
Proof.
  intros n comments before ks s Hn Hs Hbefore_len Hks_len Hvalues Hneg.
  assert (Hbefore_s : Znth s before 0 = -1).
  {
    destruct Hvalues as [_ Hvalues_at].
    specialize (Hvalues_at s Hs).
    destruct Hvalues_at as [Hminus | [Hzero | Hone]]; lia.
  }
  assert (Hafter_s : Znth s (replace_Znth s 0 before) 0 = 0).
  {
    apply Znth_replace_Znth_Same.
    lia.
  }
  assert (Hpending : sublist 0 1 (replace_Znth 0 s ks) = [s]).
  {
    destruct ks as [|k ks].
    - rewrite Zlength_nil in Hks_len; lia.
    - reflexivity.
  }
  rewrite Hpending.
  unfold ComponentFrontierStrong, ComponentFrontier.
  split.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + unfold ColourValues.
      split.
      * rewrite Zlength_replace_Znth; exact Hbefore_len.
      * intros v Hv.
        destruct (Z.eq_dec v s) as [-> | Hneq].
        -- rewrite Hafter_s. right; left; reflexivity.
        -- rewrite Znth_replace_Znth_Diff by lia.
           destruct Hvalues as [_ Hvalues_at].
           apply Hvalues_at; exact Hv.
    + unfold NewColourSet.
      refine (conj _ (conj _ (conj _ _))).
      * constructor; [intro H; simpl in H; contradiction | constructor].
      * constructor; [exact Hs | constructor].
      * intros v Hv.
        split.
        -- intros Hin.
           simpl in Hin.
           destruct Hin as [-> | []].
           split; [exact Hbefore_s | rewrite Hafter_s; lia].
        -- intros [Hbefore_v Hafter_v].
           simpl.
           destruct (Z.eq_dec v s) as [Heq | Hneq]; auto.
           exfalso.
           rewrite Znth_replace_Znth_Diff in Hafter_v by lia.
           contradiction.
      * intros v Hv Hnotin.
        rewrite Znth_replace_Znth_Diff by (simpl in Hnotin; lia).
        reflexivity.
    + unfold ComponentTwoChoices.
      intros roles Hroles.
      destruct Hroles as [Hroles_len [Hbits _]].
      assert (Hrole_s :
        Znth (s - 1) roles 0 = 0 \/ Znth (s - 1) roles 0 = 1).
      {
        apply Forall_forall with (x := Znth (s - 1) roles 0) in Hbits.
        - exact Hbits.
        - unfold Znth.
          apply nth_In.
          replace (length roles) with (Z.to_nat (Zlength roles)).
          + apply (proj1 (Z2Nat.inj_lt (s - 1) (Zlength roles)
                    ltac:(lia) (Zlength_nonneg roles))).
            lia.
          + rewrite Zlength_correct, Nat2Z.id; reflexivity.
      }
      exists (Znth (s - 1) roles 0).
      split; [exact Hrole_s |].
      intros v Hin.
      simpl in Hin.
      destruct Hin as [-> | []].
      rewrite Hafter_s.
      destruct Hrole_s as [-> | ->]; reflexivity.
    + unfold FullyScanned.
      intros e _ Hin.
      simpl in Hin; contradiction.
    + unfold ColourCount.
      reflexivity.
    + unfold ColourCount.
      reflexivity.
  - unfold ComponentTwoChoicesLocal.
    intros roles Hroles.
    destruct Hroles as [_ [Hbits _]].
    specialize (Hbits s ltac:(simpl; auto)).
    exists (Znth (s - 1) roles 0).
    split; [exact Hbits |].
    intros v Hin.
    simpl in Hin.
    destruct Hin as [-> | []].
    rewrite Hafter_s.
    destruct Hbits as [-> | ->]; reflexivity.
Qed.
Lemma sublist_pop_permutation__frontier_pop_to_scan :
  forall (ks : list Z) top,
    0 < top <= Zlength ks ->
    Permutation (sublist 0 top ks)
      (Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks).
Proof.
  intros ks top Htop.
  rewrite (sublist_split 0 top (top - 1) ks) by lia.
  assert (Hsingle : sublist (top - 1) top ks =
    Znth (top - 1) ks 0 :: nil).
  { pose proof (sublist_single 0 (top - 1) ks) as Hone.
    replace (top - 1 + 1) with top in Hone by lia.
    apply Hone. lia. }
  rewrite Hsingle.
  apply Permutation_app_comm.
Qed.
Lemma nodup_app_keep_head__frontier_pop_to_scan :
  forall (prefix tail : list Z) x,
    NoDup (prefix ++ x :: tail) -> NoDup (prefix ++ x :: nil).
Proof.
  induction prefix as [|a prefix IH]; intros tail x Hnd.
  - simpl in *. inversion Hnd; subst. constructor; [intro Hin; inversion Hin|constructor].
  - simpl in *. inversion Hnd; subst.
    constructor.
    + intro Hin. apply H1.
      apply in_app_iff in Hin. apply in_app_iff.
      destruct Hin as [Hin | [Hin | []]].
      * left. exact Hin.
      * right. left. exact Hin.
    + apply IH with (tail := tail). exact H2.
Qed.
Lemma nodup_bounded_Zlength__frontier_pop_to_scan :
  forall (xs : list Z) n,
    0 <= n -> NoDup xs -> Forall (fun x => 1 <= x <= n) xs ->
    Zlength xs <= n.
Proof.
  intros xs n Hn Hnd Hall.
  assert (Hincl : incl xs (map Z.of_nat (seq 1 (Z.to_nat n)))).
  {
    intros x Hx.
    apply Forall_forall with (x := x) in Hall; [| exact Hx].
    apply in_map_iff.
    exists (Z.to_nat x).
    split; [lia|].
    apply in_seq.
    lia.
  }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  rewrite Zlength_correct.
  lia.
Qed.
Lemma colour_counts_cover__frontier_pop_to_scan :
  forall n cs vertices,
    ColourValues n cs ->
    Forall (fun v => 1 <= v <= n) vertices ->
    (forall v, In v vertices -> Znth v cs 0 <> -1) ->
    (count_occ Z.eq_dec (map (fun v => Znth v cs (0 : Z)) vertices) (0 : Z) +
     count_occ Z.eq_dec (map (fun v => Znth v cs (0 : Z)) vertices) (1 : Z) =
     length vertices)%nat.
Proof.
  intros n cs vertices Hcv Hall Hcoloured.
  destruct Hcv as [_ Hvalues].
  induction Hall as [|v vs Hv Hvs IH].
  - reflexivity.
  - simpl.
    assert (Hvnot : Znth v cs 0 <> -1).
    { apply Hcoloured. left. reflexivity. }
    specialize (Hvalues v Hv).
    assert (Htail : forall x, In x vs -> Znth x cs 0 <> -1).
    { intros x Hx. apply Hcoloured. right. exact Hx. }
    specialize (IH Htail).
    destruct Hvalues as [Hm1 | [Hz | Ho]].
    + contradiction.
    + rewrite Hz. simpl. lia.
    + rewrite Ho. simpl. lia.
Qed.
Lemma component_frontier_pop_to_scan__frontier_pop_to_scan :
  forall n comments before after finished ks c0 c1 bit top hs ns ts ws cap,
    0 <= n -> Zlength ks = n + 1 -> 0 <= top <= n -> top <> 0 ->
    (bit = 0 \/ bit = 1) ->
    Znth (Znth (top - 1) ks 0) after 0 = bit ->
    ComponentFrontierStrong n comments before after finished
      (sublist 0 top ks) c0 c1 ->
    cap = Zlength comments ->
    ForwardStar n cap cap hs ns ts ws comments ->
    ComponentScanStrong n comments ns before after finished
      (sublist 0 (top - 1) ks) (Znth (top - 1) ks 0)
      (Znth (Znth (top - 1) ks 0) hs 0)
      (if Z.eq_dec bit 0 then c0 + 1 else c0)
      (if Z.eq_dec bit 1 then c1 + 1 else c1) /\
    c0 + 1 + c1 <= n.
Proof.
  intros n comments before after finished ks c0 c1 bit top hs ns ts ws cap
    Hn Hks Htop Htopne Hbit Hcolor Hstrong Hcap Hfs.
  assert (Htop' : 0 < top <= Zlength ks) by lia.
  pose proof (sublist_pop_permutation__frontier_pop_to_scan ks top Htop') as Hpop.
  assert (Hperm :
    Permutation (finished ++ sublist 0 top ks)
      (finished ++ Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks)).
  { apply Permutation_app_head. exact Hpop. }
  unfold ComponentFrontierStrong in Hstrong.
  destruct Hstrong as [Hfront Hlocal].
  unfold ComponentFrontier in Hfront.
  destruct Hfront as [Hvalues [Hnew [Hchoices [Hscanned [Hcount0 Hcount1]]]]].
  unfold NewColourSet in Hnew.
  destruct Hnew as [Hnd [Hall [Hiff Hsame]]].
  assert (Hnd' : NoDup
    (finished ++ Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks)).
  { eapply Permutation_NoDup; eauto. }
  assert (Hall' : Forall (fun v => 1 <= v <= n)
    (finished ++ Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks)).
  { eapply Permutation_Forall; eauto. }
  assert (Hnew' : NewColourSet n before after
    (finished ++ Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks)).
  {
    unfold NewColourSet.
    split; [exact Hnd'|]. split; [exact Hall'|]. split.
    - intros x Hx.
      specialize (Hiff x Hx).
      split; intro Hin.
      + apply Hiff.
        eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
      + eapply Permutation_in; [exact Hperm |].
        apply Hiff. exact Hin.
    - intros x Hx Hnot.
      apply Hsame; [exact Hx|]. intro Hin.
      apply Hnot.
      eapply Permutation_in; eauto.
  }
  assert (Hchoices' : ComponentTwoChoices n comments after
    (finished ++ Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks)).
  {
    intros roles Hroles.
    destruct (Hchoices roles Hroles) as [flip [Hflip Hagree]].
    exists flip. split; [exact Hflip|].
    intros v Hin. apply Hagree.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
  }
  assert (Hlocal' : ComponentTwoChoicesLocal n comments after
    (finished ++ Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks)).
  {
    intros roles Hroles.
    destruct (Hlocal roles) as [flip [Hflip Hagree]].
    - unfold RolesConsistentOnVertices in *.
      destruct Hroles as [Hlen [Hbits Hedge]].
      repeat split; try assumption.
      + intros v Hin. apply Hbits.
        eapply Permutation_in; [exact Hperm | exact Hin].
      + intros i Hi.
        specialize (Hedge i Hi).
        destruct (comment_at comments i) as [[u v] w].
        intros Hu Hv. apply Hedge.
        * eapply Permutation_in; [exact Hperm | exact Hu].
        * eapply Permutation_in; [exact Hperm | exact Hv].
    - exists flip. split; [exact Hflip|].
      intros v Hin. apply Hagree.
      eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
  }
  assert (Hchain : exists es,
    AdjChain ns (Znth (Znth (top - 1) ks 0) hs 0) es /\
    NoDup es /\
    forall e, In e es <->
      (0 <= e < 2 * cap /\ edge_src comments e = Znth (top - 1) ks 0)).
  {
    unfold ForwardStar in Hfs.
    destruct Hfs as [_ [_ [_ [_ [_ [_ [_ Hheads]]]]]]].
    apply Hheads.
    apply Forall_forall with (x := Znth (top - 1) ks 0) in Hall'.
    - exact Hall'.
    - apply in_or_app. right. left. reflexivity.
  }
  destruct Hchain as [es [Hadj [Hesnd Hes]]].
  assert (Hscanat : ScanAt comments ns after (Znth (top - 1) ks 0)
    (Znth (Znth (top - 1) ks 0) hs 0)).
  {
    exists es. split; [exact Hadj|].
    intros e He Hsrc Hnot.
    exfalso. apply Hnot. apply Hes. split; [lia|exact Hsrc].
  }
  assert (Howned : ScanAtOwned comments ns after (Znth (top - 1) ks 0)
    (Znth (Znth (top - 1) ks 0) hs 0)).
  {
    split; [exact Hscanat|].
    exists es. split; [exact Hadj|].
    intros e He. apply Hes in He. tauto.
  }
  assert (Hcount0' : ColourCount after
    (finished ++ Znth (top - 1) ks 0 :: nil) 0
    (if Z.eq_dec bit 0 then c0 + 1 else c0)).
  {
    unfold ColourCount in *.
    rewrite map_app, count_occ_app. simpl.
    rewrite Hcolor. destruct Hbit as [-> | ->]; simpl; lia.
  }
  assert (Hcount1' : ColourCount after
    (finished ++ Znth (top - 1) ks 0 :: nil) 1
    (if Z.eq_dec bit 1 then c1 + 1 else c1)).
  {
    unfold ColourCount in *.
    rewrite map_app, count_occ_app. simpl.
    rewrite Hcolor. destruct Hbit as [-> | ->]; simpl; lia.
  }
  split.
  - unfold ComponentScanStrong, ComponentScan.
    split.
    + split; [exact Hvalues|].
      split; [exact Hnew'|].
      split; [exact Hchoices'|].
      split; [exact Hscanned|].
      split; [exact Hscanat|].
      split; [exact Hcount0'|exact Hcount1'].
    + split; [exact Howned|exact Hlocal'].
  - assert (Hfinished_bounds : Forall (fun v => 1 <= v <= n)
      (finished ++ Znth (top - 1) ks 0 :: nil)).
    {
      apply Forall_app in Hall'. destruct Hall' as [Hf Hu].
      apply Forall_app. split; [exact Hf|].
      constructor.
      - apply Forall_forall with (x := Znth (top - 1) ks 0) in Hu.
        + exact Hu.
        + left. reflexivity.
      - constructor.
    }
    assert (Hfinished_nd : NoDup
      (finished ++ Znth (top - 1) ks 0 :: nil)).
    {
      eapply nodup_app_keep_head__frontier_pop_to_scan.
      exact Hnd'.
    }
    pose proof (nodup_bounded_Zlength__frontier_pop_to_scan
      _ _ Hn Hfinished_nd Hfinished_bounds) as Hlen.
    apply Forall_app in Hall'. destruct Hall' as [Hfinish _].
    assert (Hfinished_coloured : forall v, In v finished -> Znth v after 0 <> -1).
    {
      intros v Hvin.
      assert (Hvbound : 1 <= v <= n).
      { apply Forall_forall with (x := v) in Hfinish; assumption. }
      specialize (Hiff v Hvbound).
      apply Hiff. apply in_or_app. left. exact Hvin.
    }
    pose proof (colour_counts_cover__frontier_pop_to_scan
      n after finished Hvalues Hfinish Hfinished_coloured) as Hcover.
    unfold ColourCount in Hcount0, Hcount1.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
    rewrite Zlength_correct in Hlen.
    apply f_equal with (f := Z.of_nat) in Hcover.
    rewrite Nat2Z.inj_add in Hcover.
    lia.
Qed.
Lemma Znth_In__scan_conflict :
  forall (A : Type) (l : list A) (d : A) i,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l; induction l as [|a l IH]; intros d i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons; left; reflexivity.
    + rewrite Znth_cons by lia; right; apply IH; lia.
Qed.
Lemma scan_conflict_spec__scan_conflict :
  forall n m comments hs ns ts ws before cs finished pending u e c0 c1,
    m = Zlength comments ->
    0 <= e < 2 * m ->
    1 <= Znth e ts 0 <= n ->
    (Znth e ws 0 = 0 \/ Znth e ws 0 = 1) ->
    Znth (Znth e ts 0) cs 0 >= 0 ->
    Znth (Znth e ts 0) cs 0 <>
      Z.lxor (Znth u cs 0) (Znth e ws 0) ->
    ColouredClosed comments before ->
    ComponentScanStrong n comments ns before cs finished pending u e c0 c1 ->
    ForwardStar n m m hs ns ts ws comments ->
    Spec n comments (-1).
Proof.
  intros n m comments hs ns ts ws before cs finished pending u e c0 c1
    Hm He Hdstbounds Hwt Hdstcol Hconflict Hclosed Hstrong Hstar.
  unfold ComponentScanStrong in Hstrong.
  destruct Hstrong as (Hscan & Howned & Hlocal).
  unfold ComponentScan in Hscan.
  destruct Hscan as (Hcv & Hnew & Htwo & Hfully & Hscanat & Hc0 & Hc1).
  unfold NewColourSet in Hnew.
  destruct Hnew as (Hnodup & Hvertexbounds & Hmembership & Hsame).
  unfold ScanAtOwned in Howned.
  destruct Howned as (_ & remaining & Hchain & Hsource).
  assert (HeIn : In e remaining).
  { inversion Hchain; subst; simpl; auto; lia. }
  specialize (Hsource e HeIn).
  unfold ForwardStar in Hstar.
  destruct Hstar as (_ & _ & _ & _ & _ & _ & Hedge & _).
  specialize (Hedge e He).
  destruct Hedge as (Hdst & Hweight).
  assert (HuIn : In u (finished ++ u :: pending)).
  { apply in_or_app. right. simpl. auto. }
  assert (Hubounds : 1 <= u <= n).
  { apply (proj1 (Forall_forall _ _) Hvertexbounds). exact HuIn. }
  pose proof (Hmembership u Hubounds) as Hmembership_u.
  destruct (proj1 Hmembership_u HuIn) as (Hbeforeu & Hcsu).
  assert (Hi : 0 <= e / 2 < Zlength comments).
  { pose proof (Z.div_mod e 2 ltac:(lia)) as Hdiv.
    pose proof (Z.mod_pos_bound e 2 ltac:(lia)) as Hmod.
    rewrite <- Hm. nia. }
  remember (comment_at comments (e / 2)) as q eqn:Hq.
  destruct q as [[a b] w].
  unfold edge_src in Hsource.
  unfold edge_dst in Hdst.
  unfold edge_wt in Hweight.
  rewrite <- Hq in Hsource, Hdst, Hweight.
  cbn in Hsource, Hdst, Hweight.
  unfold ColouredClosed in Hclosed.
  specialize (Hclosed (e / 2) Hi).
  rewrite <- Hq in Hclosed.
  cbn in Hclosed.
  left. split; [reflexivity|].
  intros (roles & Hroles).
  pose proof Hroles as Hroles_full.
  unfold RolesConsistent in Hroles.
  destruct Hroles as (Hroleslen & Hrolesbits & Hrolescomment).
  assert (HcommentIn : In (a, b, w) comments).
  { rewrite Hq. unfold comment_at. apply Znth_In__scan_conflict. exact Hi. }
  specialize (Hrolescomment (a, b, w) HcommentIn).
  cbn in Hrolescomment.
  destruct (Z.even e) eqn:Heven.
  - subst a.
    rewrite Hdst in Hdstbounds, Hdstcol, Hconflict.
    rewrite Hweight in Hwt, Hconflict.
    assert (Hbeforeb : Znth b before 0 = -1).
    { destruct (Z.eq_dec (Znth b before 0) (-1)); auto.
      exfalso. apply (proj2 Hclosed n0). exact Hbeforeu. }
    assert (Hcsb : Znth b cs 0 <> -1) by lia.
    assert (HbIn : In b (finished ++ u :: pending)).
    { apply (proj2 (Hmembership b Hdstbounds)). split; assumption. }
    specialize (Htwo roles).
    destruct (Htwo Hroles_full) as (flip & Hflip & Hchoice).
    pose proof (Hchoice u HuIn) as Hchoiceu.
    pose proof (Hchoice b HbIn) as Hchoiceb.
    unfold ColourValues in Hcv.
    destruct Hcv as (_ & Hcv).
    pose proof (Hcv u Hubounds) as Hcsuval.
    pose proof (Hcv b Hdstbounds) as Hcsbval.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      subst;
      repeat match goal with H : Znth _ cs 0 = _ |- _ => rewrite H in * end;
      cbn in *; first [congruence | lia].
  - subst b.
    rewrite Hdst in Hdstbounds, Hdstcol, Hconflict.
    rewrite Hweight in Hwt, Hconflict.
    assert (Hbeforea : Znth a before 0 = -1).
    { destruct (Z.eq_dec (Znth a before 0) (-1)); auto.
      exfalso. apply (proj1 Hclosed n0). exact Hbeforeu. }
    assert (Hcsa : Znth a cs 0 <> -1) by lia.
    assert (HaIn : In a (finished ++ u :: pending)).
    { apply (proj2 (Hmembership a Hdstbounds)). split; assumption. }
    specialize (Htwo roles).
    destruct (Htwo Hroles_full) as (flip & Hflip & Hchoice).
    pose proof (Hchoice u HuIn) as Hchoiceu.
    pose proof (Hchoice a HaIn) as Hchoicea.
    unfold ColourValues in Hcv.
    destruct Hcv as (_ & Hcv).
    pose proof (Hcv u Hubounds) as Hcsuval.
    pose proof (Hcv a Hdstbounds) as Hcsaval.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      subst;
      repeat match goal with H : Znth _ cs 0 = _ |- _ => rewrite H in * end;
      cbn in *; first [congruence | lia].
Qed.
Lemma In_Zseq_iff__scan_edge_transitions :
  forall s len a,
    In a (Zseq s len) <-> exists k, (k < len)%nat /\ a = s + Z.of_nat k.
Proof.
  intros s len; revert s.
  induction len; intros s a; simpl.
  - split; intros H.
    + contradiction.
    + destruct H as [k [Hlt _]]. lia.
  - split; intros H.
    + destruct H as [Heq | Hin].
      * exists 0%nat. split; [lia | subst; simpl; lia].
      * apply IHlen in Hin.
        destruct Hin as [k [Hlt Heq]].
        exists (S k). split; [lia | subst; simpl; lia].
    + destruct H as [k [Hlt Heq]].
      destruct k.
      * simpl in Heq. left. subst. lia.
      * right. apply IHlen.
        exists k. split; [lia | subst; simpl; lia].
Qed.
Lemma sublist_replace_append__scan_edge_transitions :
  forall (l : list Z) top v,
    0 <= top < Zlength l ->
    sublist 0 (top + 1) (replace_Znth top v l) =
      sublist 0 top l ++ [v].
Proof.
  intros l top v Htop.
  rewrite (sublist_split 0 (top + 1) top (replace_Znth top v l)) by
    (rewrite ?Zlength_replace_Znth; lia).
  assert (Hprefix :
    sublist 0 top (replace_Znth top v l) = sublist 0 top l).
  { apply (proj2 (list_eq_ext _ _ 0)).
    split.
    - rewrite (Zlength_sublist 0 top (replace_Znth top v l)) by
        (rewrite Zlength_replace_Znth; lia).
      rewrite (Zlength_sublist 0 top l) by lia. reflexivity.
    - intros k Hk.
      assert (Hkb : 0 <= k < top).
      { rewrite (Zlength_sublist 0 top (replace_Znth top v l)) in Hk by
          (rewrite Zlength_replace_Znth; lia). lia. }
      rewrite !Znth_sublist by lia.
      rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  rewrite Hprefix.
  rewrite (sublist_single 0 top (replace_Znth top v l)) by
    (rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Same by lia. reflexivity.
Qed.
Lemma nodup_vertex_range_Zlength__scan_edge_transitions :
  forall n vertices,
    0 <= n -> NoDup vertices ->
    Forall (fun v => 1 <= v <= n) vertices ->
    Zlength vertices <= n.
Proof.
  intros n vertices Hn Hnd Hrange.
  assert (Hincl : incl vertices (Zseq 1 (Z.to_nat n))).
  { intros v Hin.
    apply In_Zseq_iff__scan_edge_transitions.
    exists (Z.to_nat (v - 1)).
    apply Forall_forall with (x := v) in Hrange; [|assumption].
    split.
    - apply Z2Nat.inj_lt; lia.
    - rewrite Z2Nat.id by lia. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite Zseq_length in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  rewrite Zlength_correct.
  exact Hlen.
Qed.
Lemma component_scan_pending_top_lt__scan_edge_transitions :
  forall n comments ns before cs finished ks u e c0 c1 top,
    0 <= n -> 0 <= top -> top <= n -> Zlength ks = n + 1 ->
    ComponentScanStrong n comments ns before cs finished
      (sublist 0 top ks) u e c0 c1 ->
    top < n.
Proof.
  intros n comments ns before cs finished ks u e c0 c1 top
    Hn Htop Htopn Hks Hstrong.
  unfold ComponentScanStrong, ComponentScan, NewColourSet in Hstrong.
  destruct Hstrong as [[_ [Hnew _]] _].
  destruct Hnew as [Hnd [Hrange _]].
  pose proof (nodup_vertex_range_Zlength__scan_edge_transitions
    n (finished ++ u :: sublist 0 top ks) Hn Hnd Hrange) as Hlen.
  rewrite Zlength_app, Zlength_cons, Zlength_sublist in Hlen by lia.
  pose proof (Zlength_nonneg finished).
  lia.
Qed.
Lemma component_scan_advance_existing__scan_edge_transitions :
  forall n comments ns before cs finished pending u e c0 c1 ts ws,
    e <> -1 ->
    0 <= e < 2 * Zlength comments ->
    Znth e ts 0 = edge_dst comments e ->
    Znth e ws 0 = edge_wt comments e ->
    0 <= Znth (Znth e ts 0) cs 0 ->
    Znth (Znth e ts 0) cs 0 = Z.lxor (Znth u cs 0) (Znth e ws 0) ->
    ComponentScanStrong n comments ns before cs finished pending u e c0 c1 ->
    ComponentScanStrong n comments ns before cs finished pending u
      (Znth e ns 0) c0 c1.
Proof.
  intros n comments ns before cs finished pending u e c0 c1 ts ws
    Hene Herange Hdst Hwt Hnonneg Hedge Hstrong.
  unfold ComponentScanStrong in *.
  destruct Hstrong as [Hscan [Howned Hlocal]].
  split; [|split].
  - unfold ComponentScan in *.
    destruct Hscan as [Hcv [Hnew [Htwo [Hfull [Hscanat [Hc0 Hc1]]]]]].
    refine (conj Hcv (conj Hnew (conj Htwo (conj Hfull (conj _ (conj Hc0 Hc1)))))).
    unfold ScanAt in *.
    destruct Hscanat as [remaining [Hchain Hdone]].
    inversion Hchain as [|e' rest' He' Hrest']; subst.
    + contradiction.
    + refine (ex_intro _ rest' _). split; [assumption|].
      intros e0 He0 Hsrc Hnotin.
      destruct (Z.eq_dec e0 e) as [->|Hneq].
      * rewrite <- Hdst, <- Hwt. split.
        -- lia.
        -- exact Hedge.
      * apply Hdone; try assumption.
        simpl. intros [Heq|Hin]; [congruence|apply Hnotin; exact Hin].
  - unfold ScanAtOwned in *.
    destruct Howned as [_ [remaining [Hchain Hsrcs]]].
    split.
    + unfold ScanAt.
      destruct Hscan as [_ [_ [_ [_ [Hscanat _]]]]].
      destruct Hscanat as [remaining0 [Hchain0 Hdone]].
      inversion Hchain0 as [|e' rest' He' Hrest']; subst; [contradiction|].
      refine (ex_intro _ rest' _). split; [assumption|].
      intros e0 He0 Hsrc Hnotin.
      destruct (Z.eq_dec e0 e) as [->|Hneq].
      * rewrite <- Hdst, <- Hwt. split.
        -- lia.
        -- exact Hedge.
      * apply Hdone; try assumption.
        simpl. intros [Heq|Hin]; [congruence|apply Hnotin; exact Hin].
    + inversion Hchain as [|e' rest' He' Hrest']; subst; [contradiction|].
      refine (ex_intro _ rest' _). split; [assumption|].
      intros e0 Hin. apply Hsrcs. simpl. auto.
  - exact Hlocal.
Qed.
Lemma colour_values_replace__scan_edge_transitions :
  forall n cs v x,
    1 <= v <= n -> (x = 0 \/ x = 1) ->
    ColourValues n cs ->
    ColourValues n (replace_Znth v x cs).
Proof.
  intros n cs v x Hv Hx Hcv.
  unfold ColourValues in *.
  destruct Hcv as [Hlen Hvals].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros z Hz.
    destruct (Z.eq_dec z v) as [->|Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      destruct Hx; subst; auto.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hvals; lia.
Qed.
Lemma fully_scanned_replace_fresh__scan_edge_transitions :
  forall comments cs finished v x,
    0 <= v < Zlength cs -> Znth v cs 0 = -1 -> ~ In v finished ->
    (forall z, In z finished -> 0 <= z < Zlength cs) ->
    (forall e, 0 <= e < 2 * Zlength comments ->
      0 <= edge_dst comments e < Zlength cs) ->
    FullyScanned comments cs finished ->
    FullyScanned comments (replace_Znth v x cs) finished.
Proof.
  intros comments cs finished v x Hvrange Hvm1 Hfresh HfinishedRanges
    HdstRanges Hfull.
  unfold FullyScanned in *.
  intros e He Hin.
  destruct (Hfull e He Hin) as [Hcol Hrel].
  pose proof (HfinishedRanges (edge_src comments e) Hin) as Hsrcrange.
  pose proof (HdstRanges e He) as Hdstrange.
  assert (Hsrcne : edge_src comments e <> v).
  { intro Heq. apply Hfresh. rewrite <- Heq. exact Hin. }
  assert (Hdstne : edge_dst comments e <> v).
  { intro Heq. rewrite Heq, Hvm1 in Hcol. contradiction. }
  split.
  - rewrite Znth_replace_Znth_Diff;
      [exact Hcol|exact Hvrange|exact Hdstrange|congruence].
  - rewrite Znth_replace_Znth_Diff;
      [|exact Hvrange|exact Hdstrange|congruence].
    rewrite Znth_replace_Znth_Diff;
      [exact Hrel|exact Hvrange|exact Hsrcrange|congruence].
Qed.
Lemma colour_count_replace_fresh__scan_edge_transitions :
  forall cs vertices bit count v x,
    0 <= v < Zlength cs -> ~ In v vertices ->
    (forall z, In z vertices -> 0 <= z < Zlength cs) ->
    ColourCount cs vertices bit count ->
    ColourCount (replace_Znth v x cs) vertices bit count.
Proof.
  intros cs vertices bit count v x Hvrange Hfresh Hranges Hcount.
  unfold ColourCount in *.
  rewrite Hcount.
  assert (Hmap :
    map (fun z => Znth z cs 0) vertices =
    map (fun z => Znth z (replace_Znth v x cs) 0) vertices).
  { apply map_ext_in. intros z Hz.
    symmetry. rewrite Znth_replace_Znth_Diff;
      [reflexivity|exact Hvrange|apply Hranges; exact Hz|].
    intro Heq. subst z. contradiction. }
  rewrite Hmap. reflexivity.
Qed.
Lemma scan_at_owned_advance_new__scan_edge_transitions :
  forall comments ns cs u e v w x,
    0 <= e < 2 * Zlength comments ->
    edge_dst comments e = v -> edge_wt comments e = w ->
    0 <= v < Zlength cs -> 0 <= u < Zlength cs ->
    Znth v cs 0 = -1 -> u <> v ->
    (forall e0, 0 <= e0 < 2 * Zlength comments ->
      0 <= edge_dst comments e0 < Zlength cs) ->
    (x = 0 \/ x = 1) ->
    x = Z.lxor (Znth u cs 0) w ->
    ScanAtOwned comments ns cs u e ->
    ScanAtOwned comments ns (replace_Znth v x cs) u (Znth e ns 0).
Proof.
  intros comments ns cs u e v w x Herange Hdst Hwt Hvrange Hurange Hvm1 Hune
    HdstRanges Hxbit Hx Howned.
  unfold ScanAtOwned in *.
  destruct Howned as [Hscan [remaining [Hchain Hsources]]].
  unfold ScanAt in Hscan.
  destruct Hscan as [remaining0 [Hchain0 Hdone]].
  inversion Hchain as [|e' rest' He' Hrest'].
  - lia.
  - subst e'.
    inversion Hchain0 as [|e0' rest0' He0' Hrest0'].
    + lia.
    + subst e0'. subst remaining0. subst remaining. split.
      * unfold ScanAt. exists rest0'. split; [exact Hrest0'|].
        intros e0 He0 Hsrc Hnotin.
        destruct (Z.eq_dec e0 e) as [Heq|Hneq].
        -- subst e0. rewrite Hdst, Hwt.
           split.
           ++ rewrite Znth_replace_Znth_Same by exact Hvrange.
              destruct Hxbit; lia.
           ++ rewrite Znth_replace_Znth_Same by exact Hvrange.
              rewrite Znth_replace_Znth_Diff;
                [exact Hx|exact Hvrange|exact Hurange|congruence].
        -- assert (Hnotold : ~ In e0 (e :: rest0')).
           { simpl. intros [Heq|Hin]; [congruence|apply Hnotin; exact Hin]. }
           destruct (Hdone e0 He0 Hsrc Hnotold) as [Hcol Hrel].
           pose proof (HdstRanges e0 He0) as Hdstrange.
           assert (Hdstne : edge_dst comments e0 <> v).
           { intro Heq. rewrite Heq, Hvm1 in Hcol. contradiction. }
           split.
           ++ rewrite Znth_replace_Znth_Diff;
                [exact Hcol|exact Hvrange|exact Hdstrange|congruence].
           ++ rewrite Znth_replace_Znth_Diff;
                [|exact Hvrange|exact Hdstrange|congruence].
              rewrite Znth_replace_Znth_Diff;
                [exact Hrel|exact Hvrange|exact Hurange|congruence].
      * exists rest'. split; [exact Hrest'|].
        intros e0 Hin. apply Hsources. simpl. auto.
Qed.
Lemma Znth_In_bounds__scan_edge_transitions :
  forall (A : Type) (l : list A) (d : A) i,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l; induction l as [|a l IH]; intros d i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons; left; reflexivity.
    + rewrite Znth_cons by lia; right; apply IH; lia.
Qed.
Lemma xor_relation_sym__scan_edge_transitions :
  forall a b w,
    (a = 0 \/ a = 1) -> (b = 0 \/ b = 1) -> (w = 0 \/ w = 1) ->
    b = Z.lxor a w -> a = Z.lxor b w.
Proof.
  intros a b w Ha Hb Hw H.
  destruct Ha, Hb, Hw; subst; vm_compute in *; congruence.
Qed.
Lemma xor_extend_flip__scan_edge_transitions :
  forall a w f,
    (a = 0 \/ a = 1) -> (w = 0 \/ w = 1) -> (f = 0 \/ f = 1) ->
    Z.lxor (Z.lxor a f) w = Z.lxor (Z.lxor a w) f.
Proof.
  intros a w f Ha Hw Hf.
  destruct Ha, Hw, Hf; subst; vm_compute; reflexivity.
Qed.
Lemma contract_disj_xor__scan_edge_transitions :
  forall ru rv c,
    (rv = 0 \/ rv = 1) -> (c = 0 \/ c = 1) ->
    ((ru = 0 /\ rv = c) \/ (ru = 1 /\ rv <> c)) ->
    rv = Z.lxor ru c.
Proof.
  intros ru rv c Hrv Hc H.
  destruct H as [[Hru Heq]|[Hru Hneq]]; subst ru.
  - rewrite Heq. destruct Hc as [Hc|Hc]; subst c; reflexivity.
  - destruct Hrv as [Hrv|Hrv]; destruct Hc as [Hc|Hc];
      rewrite Hrv, Hc in Hneq |- *; vm_compute in Hneq |- *; congruence.
Qed.
Lemma roles_consistent_edge__scan_edge_transitions :
  forall n comments roles e,
    0 <= e < 2 * Zlength comments ->
    1 <= edge_src comments e <= n ->
    1 <= edge_dst comments e <= n ->
    (edge_wt comments e = 0 \/ edge_wt comments e = 1) ->
    RolesConsistent n comments roles ->
    Znth (edge_dst comments e - 1) roles 0 =
      Z.lxor (Znth (edge_src comments e - 1) roles 0) (edge_wt comments e).
Proof.
  intros n comments roles e Herange Hsrc Hdst Hwt Hroles.
  destruct Hroles as [Hlen [Hbits Hcomments]].
  assert (Hi : 0 <= e / 2 < Zlength comments).
  { split.
    - destruct (Z.eq_dec e 0) as [Heq|Hne].
      + subst e. change (0 <= 0). lia.
      + pose proof (Z.div_pos e 2) as Hdiv. lia.
    - apply Z.div_lt_upper_bound; lia. }
  pose proof (Znth_In_bounds__scan_edge_transitions _ comments (0, 0, 0) (e / 2) Hi) as Hin.
  specialize (Hcomments (comment_at comments (e / 2)) Hin).
  assert (Hsrcbit : Znth (edge_src comments e - 1) roles 0 = 0 \/
                    Znth (edge_src comments e - 1) roles 0 = 1).
  { apply Forall_forall with
      (x := Znth (edge_src comments e - 1) roles 0) in Hbits.
    - exact Hbits.
    - apply Znth_In_bounds__scan_edge_transitions. lia. }
  assert (Hdstbit : Znth (edge_dst comments e - 1) roles 0 = 0 \/
                    Znth (edge_dst comments e - 1) roles 0 = 1).
  { apply Forall_forall with
      (x := Znth (edge_dst comments e - 1) roles 0) in Hbits.
    - exact Hbits.
    - apply Znth_In_bounds__scan_edge_transitions. lia. }
  unfold edge_src, edge_dst, edge_wt in *.
  destruct (comment_at comments (e / 2)) as [[a b] w] eqn:Hcomment.
  destruct (Z.even e) eqn:Heven; simpl in *.
  - eapply contract_disj_xor__scan_edge_transitions; [exact Hdstbit|exact Hwt|exact Hcomments].
  - apply xor_relation_sym__scan_edge_transitions; [exact Hdstbit|exact Hsrcbit|exact Hwt|].
    eapply contract_disj_xor__scan_edge_transitions; [exact Hsrcbit|exact Hwt|exact Hcomments].
Qed.
Lemma roles_consistent_local_edge__scan_edge_transitions :
  forall n comments vertices roles e,
    0 <= e < 2 * Zlength comments ->
    In (edge_src comments e) vertices ->
    In (edge_dst comments e) vertices ->
    (edge_wt comments e = 0 \/ edge_wt comments e = 1) ->
    RolesConsistentOnVertices n comments vertices roles ->
    Znth (edge_dst comments e - 1) roles 0 =
      Z.lxor (Znth (edge_src comments e - 1) roles 0) (edge_wt comments e).
Proof.
  intros n comments vertices roles e Herange Hsrcin Hdstin Hwt Hroles.
  destruct Hroles as [Hlen [Hbits Hcomments]].
  assert (Hi : 0 <= e / 2 < Zlength comments).
  { split.
    - destruct (Z.eq_dec e 0) as [Heq|Hne].
      + subst e. change (0 <= 0). lia.
      + pose proof (Z.div_pos e 2) as Hdiv. lia.
    - apply Z.div_lt_upper_bound; lia. }
  specialize (Hcomments (e / 2) Hi).
  assert (Hsrcbit : Znth (edge_src comments e - 1) roles 0 = 0 \/
                    Znth (edge_src comments e - 1) roles 0 = 1).
  { apply Hbits. exact Hsrcin. }
  assert (Hdstbit : Znth (edge_dst comments e - 1) roles 0 = 0 \/
                    Znth (edge_dst comments e - 1) roles 0 = 1).
  { apply Hbits. exact Hdstin. }
  unfold edge_src, edge_dst, edge_wt in *.
  destruct (comment_at comments (e / 2)) as [[a b] w] eqn:Hcomment.
  destruct (Z.even e) eqn:Heven; simpl in *.
  - apply Hcomments; assumption.
  - apply xor_relation_sym__scan_edge_transitions; [exact Hdstbit|exact Hsrcbit|exact Hwt|].
    apply Hcomments; assumption.
Qed.
Lemma component_two_choices_extend__scan_edge_transitions :
  forall n comments before cs oldvs u v w x,
    ColourValues n cs -> NewColourSet n before cs oldvs ->
    ComponentTwoChoices n comments cs oldvs ->
    In u oldvs -> 1 <= v <= n -> Znth v cs 0 < 0 ->
    (w = 0 \/ w = 1) -> x = Z.lxor (Znth u cs 0) w ->
    (forall roles, RolesConsistent n comments roles ->
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w) ->
    ComponentTwoChoices n comments (replace_Znth v x cs) (oldvs ++ [v]).
Proof.
  intros n comments before cs oldvs u v w x Hcv Hnew Htwo Huin Hv Hvneg Hw Hx Hedge.
  assert (Hvm1 : Znth v cs 0 = -1).
  { unfold ColourValues in Hcv. destruct Hcv as [_ Hvals0].
    specialize (Hvals0 v Hv). destruct Hvals0 as [H|[H|H]]; lia. }
  unfold NewColourSet in Hnew.
  destruct Hnew as [Hnd [Hrange [Hiff Hsame]]].
  assert (Hvrange_old : ~ In v oldvs).
  { intro Hin. apply (proj1 (Hiff v Hv)) in Hin. lia. }
  assert (Hurange : 1 <= u <= n).
  { apply Forall_forall with (x := u) in Hrange; assumption. }
  assert (Hune : u <> v) by (intro; subst; contradiction).
  unfold ColourValues in Hcv.
  destruct Hcv as [Hlen Hvals].
  assert (Hubit : Znth u cs 0 = 0 \/ Znth u cs 0 = 1).
  { specialize (Hvals u Hurange). destruct Hvals as [H|H]; [|exact H].
    apply (proj1 (Hiff u Hurange)) in Huin. lia. }
  unfold ComponentTwoChoices in *.
  intros roles Hroles.
  destruct (Htwo roles Hroles) as [flip [Hflip Hagree]].
  exists flip. split; [exact Hflip|].
  intros z Hz.
  apply in_app_or in Hz. destruct Hz as [Hz|Hz].
  - assert (Hzne : z <> v) by (intro; subst; contradiction).
    assert (Hzrange : 1 <= z <= n).
    { apply Forall_forall with (x := z) in Hrange; assumption. }
    rewrite Znth_replace_Znth_Diff by lia. apply Hagree. exact Hz.
  - simpl in Hz. destruct Hz as [Heq|[]]. subst z.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Hx, (Hedge roles Hroles), (Hagree u Huin).
    apply xor_extend_flip__scan_edge_transitions; assumption.
Qed.
Lemma component_two_choices_local_extend__scan_edge_transitions :
  forall n comments before cs oldvs u v w x,
    ColourValues n cs -> NewColourSet n before cs oldvs ->
    ComponentTwoChoicesLocal n comments cs oldvs ->
    In u oldvs -> 1 <= v <= n -> Znth v cs 0 < 0 ->
    (w = 0 \/ w = 1) -> x = Z.lxor (Znth u cs 0) w ->
    (forall roles, RolesConsistentOnVertices n comments (oldvs ++ [v]) roles ->
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w) ->
    ComponentTwoChoicesLocal n comments (replace_Znth v x cs) (oldvs ++ [v]).
Proof.
  intros n comments before cs oldvs u v w x Hcv Hnew Htwo Huin Hv Hvneg Hw Hx Hedge.
  assert (Hvm1 : Znth v cs 0 = -1).
  { unfold ColourValues in Hcv. destruct Hcv as [_ Hvals0].
    specialize (Hvals0 v Hv). destruct Hvals0 as [H|[H|H]]; lia. }
  unfold NewColourSet in Hnew.
  destruct Hnew as [Hnd [Hrange [Hiff Hsame]]].
  assert (Hvrange_old : ~ In v oldvs).
  { intro Hin. apply (proj1 (Hiff v Hv)) in Hin. lia. }
  assert (Hurange : 1 <= u <= n).
  { apply Forall_forall with (x := u) in Hrange; assumption. }
  unfold ColourValues in Hcv.
  destruct Hcv as [Hlen Hvals].
  assert (Hubit : Znth u cs 0 = 0 \/ Znth u cs 0 = 1).
  { specialize (Hvals u Hurange). destruct Hvals as [H|H]; [|exact H].
    apply (proj1 (Hiff u Hurange)) in Huin. lia. }
  unfold ComponentTwoChoicesLocal in *.
  intros roles Hroles_new.
  assert (Hroles_old : RolesConsistentOnVertices n comments oldvs roles).
  { unfold RolesConsistentOnVertices in *.
    destruct Hroles_new as [Hrlen [Hrbits Hrcomments]].
    refine (conj Hrlen (conj _ _)).
    - intros z Hz. apply Hrbits. apply in_or_app. left. exact Hz.
    - intros i Hi. specialize (Hrcomments i Hi).
      destruct (comment_at comments i) as [[a b] c] eqn:Hcomment.
      intros Ha Hb. apply Hrcomments;
        apply in_or_app; left; assumption. }
  destruct (Htwo roles Hroles_old) as [flip [Hflip Hagree]].
  exists flip. split; [exact Hflip|].
  intros z Hz.
  apply in_app_or in Hz. destruct Hz as [Hz|Hz].
  - assert (Hzne : z <> v) by (intro; subst; contradiction).
    assert (Hzrange : 1 <= z <= n).
    { apply Forall_forall with (x := z) in Hrange; assumption. }
    rewrite Znth_replace_Znth_Diff by lia. apply Hagree. exact Hz.
  - simpl in Hz. destruct Hz as [Heq|[]]. subst z.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Hx, (Hedge roles Hroles_new), (Hagree u Huin).
    apply xor_extend_flip__scan_edge_transitions; assumption.
Qed.
Lemma new_colour_set_extend__scan_edge_transitions :
  forall n before cs oldvs v x,
    1 <= v <= n -> (x = 0 \/ x = 1) ->
    Znth v cs 0 < 0 -> ColourValues n cs ->
    NewColourSet n before cs oldvs ->
    NewColourSet n before (replace_Znth v x cs) (oldvs ++ [v]).
Proof.
  intros n before cs oldvs v x Hv Hx Hvneg Hcv Hnew.
  unfold ColourValues in Hcv.
  destruct Hcv as [Hlen Hvals].
  assert (Hvm1 : Znth v cs 0 = -1).
  { specialize (Hvals v Hv). destruct Hvals as [H|[H|H]]; lia. }
  unfold NewColourSet in *.
  destruct Hnew as [Hnd [Hrange [Hiff Hsame]]].
  assert (Hfresh : ~ In v oldvs).
  { intro Hin. apply Hiff in Hin; lia. }
  assert (Hbefore : Znth v before 0 = -1).
  { rewrite <- Hvm1. symmetry. apply Hsame; auto. }
  assert (Hxnm1 : x <> -1) by (destruct Hx; lia).
  refine (conj _ (conj _ (conj _ _))).
  - apply NoDup_app.
    + exact Hnd.
    + constructor; [simpl; auto|constructor].
    + intros a Ha Hb. simpl in Hb. destruct Hb as [->|[]]. contradiction.
  - apply Forall_app. split; [assumption|]. constructor; auto.
  - intros z Hz. split.
    + intros Hin.
      apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * assert (Hzne : z <> v) by (intro; subst; contradiction).
        apply (Hiff z Hz) in Hin. destruct Hin as [Hb Hc]. split; [exact Hb|].
        rewrite Znth_replace_Znth_Diff by lia. exact Hc.
      * simpl in Hin. destruct Hin as [->|[]]. split; [assumption|].
        rewrite Znth_replace_Znth_Same by lia. assumption.
    + intros [Hb Hc].
      destruct (Z.eq_dec z v) as [->|Hzne].
      * apply in_or_app. right. simpl; auto.
      * apply in_or_app. left. apply (proj2 (Hiff z Hz)). split; [exact Hb|].
        rewrite Znth_replace_Znth_Diff in Hc by lia. exact Hc.
  - intros z Hz Hnotin.
    assert (Hzne : z <> v).
    { intro; subst. apply Hnotin. apply in_or_app. right. simpl; auto. }
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hsame; [exact Hz|].
    intro Hin. apply Hnotin. apply in_or_app; auto.
Qed.
Lemma component_scan_advance_new__scan_edge_transitions :
  forall n cap comments hs ns ts ws before cs finished pending u e c0 c1,
    cap = Zlength comments -> 0 <= e < 2 * cap -> 1 <= u <= n ->
    Znth (Znth e ts 0) cs 0 < 0 ->
    ForwardStar n cap cap hs ns ts ws comments ->
    ForwardStarRanges n cap hs ns ts ws ->
    ComponentScanStrong n comments ns before cs finished pending u e c0 c1 ->
    ComponentScanStrong n comments ns before
      (replace_Znth (Znth e ts 0)
        (Z.lxor (Znth u cs 0) (Znth e ws 0)) cs)
      finished (pending ++ [Znth e ts 0]) u (Znth e ns 0) c0 c1.
Proof.
  intros n cap comments hs ns ts ws before cs finished pending u e c0 c1
    Hcap Herange Hurange Hvneg Hfs Hfr Hstrong.
  set (v := Znth e ts 0).
  set (w := Znth e ws 0).
  set (x := Z.lxor (Znth u cs 0) w).
  assert (HerangeC : 0 <= e < 2 * Zlength comments) by lia.
  unfold ForwardStar in Hfs.
  destruct Hfs as [Hhs [Hns [Hts [Hws [Hk [Hkcomments [Hedges Hadj]]]]]]].
  assert (HedgeNow := Hedges e Herange).
  destruct HedgeNow as [Hdst Hwt].
  unfold ForwardStarRanges in Hfr.
  destruct Hfr as [Hheads Hranges].
  assert (HrangeNow := Hranges e Herange).
  destruct HrangeNow as [[Hnlo Hnhi] [[Hvlow Hvhigh] Hwbit]].
  assert (Hvrange : 1 <= v <= n) by (unfold v; lia).
  assert (Hwrange : w = 0 \/ w = 1) by (unfold w; assumption).
  unfold ComponentScanStrong in Hstrong.
  destruct Hstrong as [Hscan [Howned Hlocal]].
  unfold ComponentScan in Hscan.
  destruct Hscan as [Hcv [Hnew [Htwo [Hfull [Hscanat [Hc0 Hc1]]]]]].
  assert (Hcslen : Zlength cs = n + 1).
  { unfold ColourValues in Hcv. tauto. }
  assert (Hvm1 : Znth v cs 0 = -1).
  { unfold ColourValues in Hcv. destruct Hcv as [_ Hvals].
    specialize (Hvals v Hvrange). change (Znth v cs 0 < 0) in Hvneg.
    destruct Hvals as [H|[H|H]].
    - exact H.
    - rewrite H in Hvneg. lia.
    - rewrite H in Hvneg. lia. }
  set (oldvs := finished ++ u :: pending).
  assert (Huold : In u oldvs).
  { unfold oldvs. apply in_or_app. right. simpl. auto. }
  assert (Hsrc : edge_src comments e = u).
  { unfold ScanAtOwned in Howned.
    destruct Howned as [_ [remaining [Hchain Hsources]]].
    inversion Hchain as [|e' rest' He' Hrest'].
    - lia.
    - subst e'. subst remaining. apply Hsources. simpl. auto. }
  assert (HdstRanges : forall e0, 0 <= e0 < 2 * Zlength comments ->
      0 <= edge_dst comments e0 < Zlength cs).
  { intros e0 He0.
    assert (He0cap : 0 <= e0 < 2 * cap) by lia.
    assert (Hre0 := Hranges e0 He0cap).
    destruct Hre0 as [_ [[Htlo Hthi] _]].
    assert (Hee0 := Hedges e0 He0cap).
    destruct Hee0 as [Hedst _]. rewrite <- Hedst. lia. }
  assert (HoldRanges : forall z, In z oldvs -> 0 <= z < Zlength cs).
  { intros z Hz. unfold NewColourSet in Hnew.
    destruct Hnew as [_ [Hrange _]].
    apply Forall_forall with (x := z) in Hrange; [|exact Hz]. lia. }
  assert (Hufresh : u <> v).
  { intro Heq.
    unfold NewColourSet in Hnew.
    destruct Hnew as [_ [_ [Hiff _]]].
    pose proof (proj1 (Hiff u Hurange) Huold) as [_ Hcol].
    apply Hcol. rewrite Heq. exact Hvm1. }
  assert (Hubit : Znth u cs 0 = 0 \/ Znth u cs 0 = 1).
  { unfold ColourValues in Hcv. destruct Hcv as [_ Hvals].
    specialize (Hvals u Hurange). destruct Hvals as [H|H]; [|exact H].
    unfold NewColourSet in Hnew.
    destruct Hnew as [_ [_ [Hiff _]]].
    apply (proj1 (Hiff u Hurange)) in Huold. tauto. }
  assert (Hxbit : x = 0 \/ x = 1).
  { unfold x. destruct Hubit as [Hu|Hu], Hwrange as [Hw|Hw];
      rewrite Hu, Hw; vm_compute; auto. }
  assert (Hfreshold : ~ In v oldvs).
  { intro Hin. unfold NewColourSet in Hnew.
    destruct Hnew as [_ [_ [Hiff _]]].
    apply (proj1 (Hiff v Hvrange)) in Hin. tauto. }
  assert (HglobalEdge : forall roles, RolesConsistent n comments roles ->
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w).
  { intros roles Hroles.
    pose proof (roles_consistent_edge__scan_edge_transitions n comments roles e HerangeC) as Hedge.
    rewrite Hsrc, <- Hdst, <- Hwt in Hedge. apply Hedge; assumption. }
  assert (HlocalEdge : forall roles,
      RolesConsistentOnVertices n comments (oldvs ++ [v]) roles ->
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w).
  { intros roles Hroles.
    pose proof (roles_consistent_local_edge__scan_edge_transitions
      n comments (oldvs ++ [v]) roles e HerangeC) as Hedge.
    assert (Hsrcin : In (edge_src comments e) (oldvs ++ [v])).
    { rewrite Hsrc. apply in_or_app. left. exact Huold. }
    assert (Hdstin : In (edge_dst comments e) (oldvs ++ [v])).
    { rewrite <- Hdst. apply in_or_app. right. simpl. auto. }
    specialize (Hedge Hsrcin Hdstin).
    rewrite <- Hwt in Hedge.
    specialize (Hedge Hwrange Hroles).
    rewrite Hsrc, <- Hdst in Hedge. exact Hedge. }
  assert (Hcv' : ColourValues n (replace_Znth v x cs)).
  { apply colour_values_replace__scan_edge_transitions; assumption. }
  assert (Hnew' : NewColourSet n before (replace_Znth v x cs) (oldvs ++ [v])).
  { eapply new_colour_set_extend__scan_edge_transitions; try eassumption. }
  assert (Htwo' : ComponentTwoChoices n comments (replace_Znth v x cs) (oldvs ++ [v])).
  { eapply component_two_choices_extend__scan_edge_transitions with
      (before := before) (u := u) (w := w);
      [exact Hcv|exact Hnew|exact Htwo|exact Huold|exact Hvrange|exact Hvneg|
       exact Hwrange|reflexivity|exact HglobalEdge]. }
  assert (Hlocal' : ComponentTwoChoicesLocal n comments
      (replace_Znth v x cs) (oldvs ++ [v])).
  { eapply component_two_choices_local_extend__scan_edge_transitions with
      (before := before) (u := u) (w := w);
      [exact Hcv|exact Hnew|exact Hlocal|exact Huold|exact Hvrange|exact Hvneg|
       exact Hwrange|reflexivity|exact HlocalEdge]. }
  assert (Hfreshfinished : ~ In v finished).
  { intro Hin. apply Hfreshold. unfold oldvs. apply in_or_app. left. exact Hin. }
  assert (HfinishedRanges : forall z, In z finished -> 0 <= z < Zlength cs).
  { intros z Hz. apply HoldRanges. unfold oldvs. apply in_or_app. left. exact Hz. }
  assert (Hfull' : FullyScanned comments (replace_Znth v x cs) finished).
  { eapply fully_scanned_replace_fresh__scan_edge_transitions; try eassumption. lia. }
  assert (Howned' : ScanAtOwned comments ns (replace_Znth v x cs) u (Znth e ns 0)).
  { eapply scan_at_owned_advance_new__scan_edge_transitions with (v := v) (w := w) (x := x);
      [exact HerangeC|unfold v; symmetry; exact Hdst|
       unfold w; symmetry; exact Hwt|lia|lia|exact Hvm1|exact Hufresh|
       exact HdstRanges|exact Hxbit|reflexivity|exact Howned]. }
  assert (Hfreshcount : ~ In v (finished ++ u :: nil)).
  { intro Hin. apply Hfreshold. unfold oldvs in *. apply in_app_or in Hin.
    destruct Hin as [Hin|Hin].
    - apply in_or_app. left. exact Hin.
    - simpl in Hin. destruct Hin as [Heq|[]]. subst u. contradiction. }
  assert (HcountRanges : forall z, In z (finished ++ u :: nil) ->
      0 <= z < Zlength cs).
  { intros z Hz. apply HoldRanges. unfold oldvs. apply in_app_or in Hz.
    destruct Hz as [Hz|Hz].
    - apply in_or_app. left. exact Hz.
    - simpl in Hz. destruct Hz as [Heq|[]]. subst z.
      apply in_or_app. right. simpl. auto. }
  assert (Hc0' : ColourCount (replace_Znth v x cs) (finished ++ u :: nil) 0 c0).
  { eapply colour_count_replace_fresh__scan_edge_transitions; try eassumption. lia. }
  assert (Hc1' : ColourCount (replace_Znth v x cs) (finished ++ u :: nil) 1 c1).
  { eapply colour_count_replace_fresh__scan_edge_transitions; try eassumption. lia. }
  assert (Hshape : oldvs ++ [v] = finished ++ u :: (pending ++ [v])).
  { unfold oldvs.
    change ((finished ++ (u :: pending)) ++ [v] =
      finished ++ ((u :: pending) ++ [v])).
    symmetry. apply app_assoc. }
  rewrite Hshape in Hnew', Htwo', Hlocal'.
  assert (Hscanat' : ScanAt comments ns (replace_Znth v x cs) u (Znth e ns 0)).
  { unfold ScanAtOwned in Howned'. tauto. }
  unfold ComponentScanStrong, ComponentScan.
  split.
  - exact (conj Hcv' (conj Hnew' (conj Htwo'
      (conj Hfull' (conj Hscanat' (conj Hc0' Hc1')))))).
  - exact (conj Howned' Hlocal').
Qed.
Lemma component_scan_advance_new_stack__scan_edge_transitions :
  forall n cap comments hs ns ts ws before cs finished ks u e c0 c1 top,
    cap = Zlength comments -> 0 <= e < 2 * cap -> 1 <= u <= n ->
    Znth (Znth e ts 0) cs 0 < 0 ->
    0 <= top < Zlength ks ->
    ForwardStar n cap cap hs ns ts ws comments ->
    ForwardStarRanges n cap hs ns ts ws ->
    ComponentScanStrong n comments ns before cs finished
      (sublist 0 top ks) u e c0 c1 ->
    ComponentScanStrong n comments ns before
      (replace_Znth (Znth e ts 0)
        (Z.lxor (Znth u cs 0) (Znth e ws 0)) cs)
      finished (sublist 0 (top + 1)
        (replace_Znth top (Znth e ts 0) ks))
      u (Znth e ns 0) c0 c1.
Proof.
  intros n cap comments hs ns ts ws before cs finished ks u e c0 c1 top
    Hcap He Hu Hv Htop Hfs Hfr Hscan.
  rewrite sublist_replace_append__scan_edge_transitions by exact Htop.
  eapply component_scan_advance_new__scan_edge_transitions;
    try eassumption.
Qed.
Lemma component_scan_done__scan_and_component_closure :
  forall n comments ns before after finished pending u c0 c1,
    ComponentScanStrong n comments ns before after finished pending
      u (-1) c0 c1 ->
    ComponentFrontierStrong n comments before after
      (finished ++ u :: nil) pending c0 c1.
Proof.
  intros n comments ns before after finished pending u c0 c1 Hstrong.
  unfold ComponentScanStrong in Hstrong.
  destruct Hstrong as [Hscan [Howned Hlocal]].
  unfold ComponentScan in Hscan.
  destruct Hscan as
      [Hvalues [Hnew [Hchoices [Hfinished [Hscan [Hcount0 Hcount1]]]]]].
  unfold ScanAtOwned in Howned.
  destruct Howned as [_ [remaining [Hchain Howned]]].
  assert (remaining = nil) by (inversion Hchain; subst; [reflexivity | lia]).
  subst remaining.
  unfold ComponentFrontierStrong.
  split.
  - unfold ComponentFrontier.
    split; [exact Hvalues |].
    split; [rewrite <- app_assoc; simpl; exact Hnew |].
    split; [rewrite <- app_assoc; simpl; exact Hchoices |].
    split.
    + intros e He Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * exact (Hfinished e He Hin).
      * simpl in Hin. destruct Hin as [Hu | []]. subst u.
        destruct Hscan as [remaining [Hchain' Hdone]].
        assert (remaining = nil) by
          (inversion Hchain'; subst; [reflexivity | lia]).
        subst remaining.
        apply Hdone; [exact He | reflexivity |].
        simpl. tauto.
    + split; assumption.
  - rewrite <- app_assoc. simpl. exact Hlocal.
Qed.
Lemma new_component_edge_closed__scan_and_component_closure :
  forall n comments before after vertices i u v w,
    NewColourSet n before after vertices ->
    ColouredClosed comments before -> ColouredClosed comments after ->
    0 <= i < Zlength comments -> comment_at comments i = (u, v, w) ->
    1 <= u <= n -> 1 <= v <= n ->
    (In u vertices <-> In v vertices).
Proof.
  intros n comments before after vertices i u v w Hnew Hbefore Hafter
    Hi Hcomment Hu Hv.
  destruct Hnew as [_ [_ [Hnewiff _]]].
  specialize (Hbefore i Hi). rewrite Hcomment in Hbefore.
  specialize (Hafter i Hi). rewrite Hcomment in Hafter.
  split; intro Hin.
  - apply (proj1 (Hnewiff u Hu)) in Hin.
    destruct Hin as [Huold Huafter].
    apply (proj2 (Hnewiff v Hv)). split.
    + destruct (Z.eq_dec (Znth v before 0) (-1)) as [Heq | Hne]; [exact Heq |].
      exfalso. assert (Hune := proj2 Hbefore Hne). congruence.
    + apply (proj1 Hafter). exact Huafter.
  - apply (proj1 (Hnewiff v Hv)) in Hin.
    destruct Hin as [Hvold Hvafter].
    apply (proj2 (Hnewiff u Hu)). split.
    + destruct (Z.eq_dec (Znth u before 0) (-1)) as [Heq | Hne]; [exact Heq |].
      exfalso. assert (Hvne := proj1 Hbefore Hne). congruence.
    + apply (proj2 Hafter). exact Hvafter.
Qed.
Lemma lxor_bit__scan_and_component_closure :
  forall a b, (a = 0 \/ a = 1) -> (b = 0 \/ b = 1) ->
    Z.lxor a b = 0 \/ Z.lxor a b = 1.
Proof. intros a b [-> | ->] [-> | ->]; simpl; auto. Qed.
Lemma lxor_shuffle__scan_and_component_closure :
  forall a b c, Z.lxor (Z.lxor a b) c = Z.lxor (Z.lxor a c) b.
Proof.
  intros a b c. rewrite !Z.lxor_assoc. f_equal. apply Z.lxor_comm.
Qed.
Lemma edge_forward__scan_and_component_closure :
  forall comments i u v w,
    comment_at comments i = (u, v, w) ->
    edge_src comments (2 * i) = u /\
    edge_dst comments (2 * i) = v /\
    edge_wt comments (2 * i) = w.
Proof.
  intros comments i u v w Hcomment.
  unfold edge_src, edge_dst, edge_wt.
  replace (2 * i / 2) with i by
    (symmetry; rewrite Z.mul_comm; apply Z.div_mul; lia).
  rewrite Hcomment, Z.even_mul. simpl. auto.
Qed.
Lemma edge_reverse__scan_and_component_closure :
  forall comments i u v w,
    comment_at comments i = (u, v, w) ->
    edge_src comments (2 * i + 1) = v /\
    edge_dst comments (2 * i + 1) = u /\
    edge_wt comments (2 * i + 1) = w.
Proof.
  intros comments i u v w Hcomment.
  unfold edge_src, edge_dst, edge_wt.
  replace ((2 * i + 1) / 2) with i by
    (apply Zdiv_unique with (r := 1); lia).
  rewrite Hcomment.
  replace (Z.even (2 * i + 1)) with false.
  - simpl. auto.
  - rewrite Z.even_add, Z.even_mul. simpl. reflexivity.
Qed.
Lemma comment_bounds_from_forward_star__scan_and_component_closure :
  forall n cap comments hs ns ts ws,
    cap = Zlength comments ->
    ForwardStar n cap cap hs ns ts ws comments ->
    ForwardStarRanges n cap hs ns ts ws ->
    forall i, 0 <= i < Zlength comments ->
      let '(u, v, _) := comment_at comments i in
      1 <= u <= n /\ 1 <= v <= n.
Proof.
  intros n cap comments hs ns ts ws Hcap Hstar Hranges i Hi.
  destruct (comment_at comments i) as [[u v] w] eqn:Hcomment.
  unfold ForwardStar in Hstar.
  destruct Hstar as [_ [_ [_ [_ [_ [_ [Hedges _]]]]]]].
  unfold ForwardStarRanges in Hranges.
  destruct Hranges as [_ Hranges].
  pose proof (edge_forward__scan_and_component_closure
    comments i u v w Hcomment) as [Hsrc [Hdst Hwt]].
  pose proof (edge_reverse__scan_and_component_closure
    comments i u v w Hcomment) as [Hsrc' [Hdst' Hwt']].
  assert (Hf : 0 <= 2 * i < 2 * cap) by lia.
  assert (Hr : 0 <= 2 * i + 1 < 2 * cap) by lia.
  pose proof (Hedges (2 * i) Hf) as HedgesF.
  pose proof (Hranges (2 * i) Hf) as HrangesF.
  pose proof (Hedges (2 * i + 1) Hr) as HedgesR.
  pose proof (Hranges (2 * i + 1) Hr) as HrangesR.
  destruct HedgesF as [Hto _].
  destruct HedgesR as [Hto' _].
  destruct HrangesF as [_ [Hto_range _]].
  destruct HrangesR as [_ [Hto_range' _]].
  rewrite Hto, Hdst in Hto_range.
  rewrite Hto', Hdst' in Hto_range'.
  auto.
Qed.
Lemma frontier_respected_closed__scan_and_component_closure :
  forall n cap comments hs ns ts ws before after vertices,
    cap = Zlength comments ->
    ForwardStar n cap cap hs ns ts ws comments ->
    ForwardStarRanges n cap hs ns ts ws ->
    ParityRespected comments before ->
    ColouredClosed comments before ->
    NewColourSet n before after vertices ->
    FullyScanned comments after vertices ->
    ParityRespected comments after /\ ColouredClosed comments after.
Proof.
  intros n cap comments hs ns ts ws before after vertices
    Hcap Hstar Hranges Hparity Hclosed Hnew Hscanned.
  destruct Hnew as [Hnodup [Hvbounds [Hnewiff Hsame]]].
  assert (Hbounds := comment_bounds_from_forward_star__scan_and_component_closure
    n cap comments hs ns ts ws Hcap Hstar Hranges).
  split.
  - intros i Hi.
    destruct (comment_at comments i) as [[u v] w] eqn:Hcomment.
    intros Hu_after Hv_after.
    specialize (Hbounds i Hi). rewrite Hcomment in Hbounds.
    destruct Hbounds as [Hu_bounds Hv_bounds].
    destruct (Z.eq_dec (Znth u before 0) (-1)) as [Hu_old | Hu_old].
    + assert (Hu_in : In u vertices).
      { apply (proj2 (Hnewiff u Hu_bounds)). auto. }
      pose proof (edge_forward__scan_and_component_closure
        comments i u v w Hcomment) as [Hsrc [Hdst Hwt]].
      pose proof (Hscanned (2 * i)) as Hedge.
      specialize (Hedge ltac:(lia) ltac:(rewrite Hsrc; exact Hu_in)).
      rewrite Hsrc, Hdst, Hwt in Hedge. tauto.
    + assert (Hv_old : Znth v before 0 <> -1).
      { specialize (Hclosed i Hi). rewrite Hcomment in Hclosed. tauto. }
      assert (Hu_notin : ~ In u vertices).
      { intro Hin. apply (proj1 (Hnewiff u Hu_bounds)) in Hin. tauto. }
      assert (Hv_notin : ~ In v vertices).
      { intro Hin. apply (proj1 (Hnewiff v Hv_bounds)) in Hin. tauto. }
      rewrite (Hsame u Hu_bounds Hu_notin), (Hsame v Hv_bounds Hv_notin).
      specialize (Hparity i Hi). rewrite Hcomment in Hparity.
      exact (Hparity Hu_old Hv_old).
  - intros i Hi.
    destruct (comment_at comments i) as [[u v] w] eqn:Hcomment.
    specialize (Hbounds i Hi). rewrite Hcomment in Hbounds.
    destruct Hbounds as [Hu_bounds Hv_bounds].
    split; intro Hcol.
    + destruct (Z.eq_dec (Znth u before 0) (-1)) as [Hu_old | Hu_old].
      * assert (Hu_in : In u vertices).
        { apply (proj2 (Hnewiff u Hu_bounds)). auto. }
        pose proof (edge_forward__scan_and_component_closure
          comments i u v w Hcomment) as [Hsrc [Hdst Hwt]].
        pose proof (Hscanned (2 * i)) as Hedge.
        specialize (Hedge ltac:(lia) ltac:(rewrite Hsrc; exact Hu_in)).
        rewrite Hsrc, Hdst in Hedge. tauto.
      * assert (Hv_old : Znth v before 0 <> -1).
        { specialize (Hclosed i Hi). rewrite Hcomment in Hclosed. tauto. }
        assert (Hv_notin : ~ In v vertices).
        { intro Hin. apply (proj1 (Hnewiff v Hv_bounds)) in Hin. tauto. }
        rewrite (Hsame v Hv_bounds Hv_notin). exact Hv_old.
    + destruct (Z.eq_dec (Znth v before 0) (-1)) as [Hv_old | Hv_old].
      * assert (Hv_in : In v vertices).
        { apply (proj2 (Hnewiff v Hv_bounds)). auto. }
        pose proof (edge_reverse__scan_and_component_closure
          comments i u v w Hcomment) as [Hsrc [Hdst Hwt]].
        pose proof (Hscanned (2 * i + 1)) as Hedge.
        specialize (Hedge ltac:(lia) ltac:(rewrite Hsrc; exact Hv_in)).
        rewrite Hsrc, Hdst in Hedge. tauto.
      * assert (Hu_old : Znth u before 0 <> -1).
        { specialize (Hclosed i Hi). rewrite Hcomment in Hclosed. tauto. }
        assert (Hu_notin : ~ In u vertices).
        { intro Hin. apply (proj1 (Hnewiff u Hu_bounds)) in Hin. tauto. }
        rewrite (Hsame u Hu_bounds Hu_notin). exact Hu_old.
Qed.
Lemma znth_replace_same__scan_and_component_closure :
  forall {A : Type} (xs : list A) (i : Z) (v d : A),
    0 <= i < Zlength xs ->
    Znth i (replace_Znth i v xs) d = v.
Proof.
  induction xs as [|x xs IH]; intros i v d Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + unfold replace_Znth, Znth. simpl. reflexivity.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply IH. lia.
Qed.
Lemma znth_replace_diff__scan_and_component_closure :
  forall {A : Type} (xs : list A) (i j : Z) (v d : A),
    0 <= i < Zlength xs -> 0 <= j < Zlength xs ->
    i <> j -> Znth j (replace_Znth i v xs) d = Znth j xs d.
Proof.
  induction xs as [|x xs IH]; intros i j v d Hi Hj Hij.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi, Hj.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + assert (j <> 0) by congruence.
      assert (0 < j) by lia.
      unfold replace_Znth. simpl.
      rewrite !Znth_cons by lia. reflexivity.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      destruct (Z.eq_dec j 0) as [-> | Hj0].
      * unfold Znth. simpl. reflexivity.
      * assert (0 < j) by lia.
        rewrite !Znth_cons by lia.
        apply IH; lia.
Qed.
Lemma sum_replace__scan_and_component_closure :
  forall (xs : list Z) (i v : Z), 0 <= i < Zlength xs ->
    fold_right Z.add 0 (replace_Znth i v xs) =
    fold_right Z.add 0 xs - Znth i xs 0 + v.
Proof.
  induction xs as [|x xs IH]; intros i v Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + unfold replace_Znth, Znth. simpl. ring.
    + assert (0 < i) by lia.
      rewrite replace_Znth_cons by lia.
      rewrite Znth_cons by lia. simpl.
      rewrite IH by lia. ring.
Qed.
Lemma fold_replace_length__scan_and_component_closure :
  forall (vertices : list Z) (n : Z) (base : list Z) (f : Z -> Z),
    Zlength base = n ->
    Zlength (fold_right
      (fun v r => replace_Znth (v - 1) (f v) r) base vertices) = n.
Proof.
  induction vertices as [|x vertices IH]; intros n base f Hlen; simpl.
  - exact Hlen.
  - rewrite Zlength_replace_Znth. apply IH. exact Hlen.
Qed.
Lemma fold_replace_member__scan_and_component_closure :
  forall (vertices : list Z) (n : Z) (base : list Z) (f : Z -> Z) (v : Z),
    Zlength base = n -> Forall (fun x => 1 <= x <= n) vertices ->
    1 <= v <= n -> In v vertices ->
    Znth (v - 1)
      (fold_right (fun x r => replace_Znth (x - 1) (f x) r)
        base vertices) 0 = f v.
Proof.
  induction vertices as [|x vertices IH]; intros n base f v Hlen Hbounds Hv Hin.
  - contradiction.
  - inversion Hbounds as [|? ? Hx Htail]; subst. simpl in Hin. simpl.
    pose proof (fold_replace_length__scan_and_component_closure
      vertices (Zlength base) base f eq_refl) as Htail_len.
    destruct Hin as [-> | Hin].
    + apply znth_replace_same__scan_and_component_closure.
      rewrite Htail_len; lia.
    + destruct (Z.eq_dec (x - 1) (v - 1)) as [Heq | Hneq].
      * assert (x = v) by lia. subst.
        apply znth_replace_same__scan_and_component_closure.
        rewrite Htail_len; lia.
      * rewrite znth_replace_diff__scan_and_component_closure.
        -- apply (IH (Zlength base) base f v eq_refl Htail Hv Hin).
        -- rewrite Htail_len; lia.
        -- rewrite Htail_len; lia.
        -- exact Hneq.
Qed.
Lemma fold_replace_outside__scan_and_component_closure :
  forall (vertices : list Z) (n : Z) (base : list Z) (f : Z -> Z) (v : Z),
    Zlength base = n -> Forall (fun x => 1 <= x <= n) vertices ->
    1 <= v <= n -> ~ In v vertices ->
    Znth (v - 1)
      (fold_right (fun x r => replace_Znth (x - 1) (f x) r)
        base vertices) 0 = Znth (v - 1) base 0.
Proof.
  induction vertices as [|x vertices IH]; intros n base f v Hlen Hbounds Hv Hout.
  - reflexivity.
  - inversion Hbounds as [|? ? Hx Htail]; subst. simpl.
    pose proof (fold_replace_length__scan_and_component_closure
      vertices (Zlength base) base f eq_refl) as Htail_len.
    assert (Hxv : x <> v) by (intro; subst; apply Hout; simpl; auto).
    rewrite znth_replace_diff__scan_and_component_closure.
    + apply (IH (Zlength base) base f v eq_refl Htail Hv).
      intro Hin. apply Hout. simpl. auto.
    + rewrite Htail_len; lia.
    + rewrite Htail_len; lia.
    + lia.
Qed.
Lemma fold_replace_sum__scan_and_component_closure :
  forall (vertices : list Z) (n : Z) (base : list Z) (f : Z -> Z),
    Zlength base = n -> NoDup vertices ->
    Forall (fun x => 1 <= x <= n) vertices ->
    (forall v, In v vertices -> Znth (v - 1) base 0 = 0) ->
    fold_right Z.add 0
      (fold_right (fun x r => replace_Znth (x - 1) (f x) r)
        base vertices) =
    fold_right Z.add 0 base + fold_right Z.add 0 (map f vertices).
Proof.
  induction vertices as [|x vertices IH]; intros n base f Hlen Hnd Hbounds Hzero.
  - simpl. lia.
  - inversion Hnd as [|? ? Hnotin Hndtail]; subst.
    inversion Hbounds as [|? ? Hx Htail]; subst. simpl.
    pose proof (fold_replace_length__scan_and_component_closure
      vertices (Zlength base) base f eq_refl) as Htail_len.
    rewrite sum_replace__scan_and_component_closure.
    + rewrite (fold_replace_outside__scan_and_component_closure
        vertices (Zlength base) base f x eq_refl Htail Hx Hnotin).
      rewrite Hzero by (simpl; auto).
      assert (Hzero_tail : forall v, In v vertices ->
          Znth (v - 1) base 0 = 0).
      { intros v Hin. apply Hzero. simpl. auto. }
      rewrite (IH (Zlength base) base f eq_refl Hndtail Htail Hzero_tail).
      ring.
    + rewrite Htail_len; lia.
Qed.
Lemma binary_sum_count__scan_and_component_closure :
  forall (xs : list Z), Forall (fun x => x = 0 \/ x = 1) xs ->
    fold_right Z.add 0 xs = Z.of_nat (count_occ Z.eq_dec xs 1) /\
    fold_right Z.add 0 (map (fun x => Z.lxor x 1) xs) =
      Z.of_nat (count_occ Z.eq_dec xs 0).
Proof.
  induction xs as [|x xs IH]; intro Hbits.
  - simpl. auto.
  - inversion Hbits as [|? ? Hx Htail]; subst.
    specialize (IH Htail). destruct IH as [IH1 IH0].
    destruct Hx as [-> | ->].
    + simpl. split; [exact IH1 |]. rewrite IH0.
      change (1 + Z.of_nat (count_occ Z.eq_dec xs 0) =
        Z.of_nat (S (count_occ Z.eq_dec xs 0))).
      rewrite Nat2Z.inj_succ. lia.
    + simpl. split; [| exact IH0]. rewrite IH1.
      change (1 + Z.of_nat (count_occ Z.eq_dec xs 1) =
        Z.of_nat (S (count_occ Z.eq_dec xs 1))).
      rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma component_bit_sum__scan_and_component_closure :
  forall n cs vertices c0 c1 flip,
    ColourValues n cs -> Forall (fun v => 1 <= v <= n) vertices ->
    (forall v, In v vertices -> Znth v cs 0 <> -1) ->
    ColourCount cs vertices 0 c0 -> ColourCount cs vertices 1 c1 ->
    (flip = 0 \/ flip = 1) ->
    fold_right Z.add 0
      (map (fun v => Z.lxor (Znth v cs 0) flip) vertices) =
    if Z.eq_dec flip 0 then c1 else c0.
Proof.
  intros n cs vertices c0 c1 flip Hvalues Hbounds Hcoloured
    Hcount0 Hcount1 Hflip.
  unfold ColourValues in Hvalues.
  destruct Hvalues as [_ Hvalues].
  assert (Hbits : Forall (fun x => x = 0 \/ x = 1)
      (map (fun v => Znth v cs 0) vertices)).
  { rewrite Forall_forall in *. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [v [Hx Hin]].
    subst x.
    specialize (Hvalues v (Hbounds v Hin)).
    destruct Hvalues as [Hminus | Hbits]; [exfalso; apply (Hcoloured v Hin); exact Hminus | exact Hbits]. }
  pose proof (binary_sum_count__scan_and_component_closure _ Hbits)
    as [Hsum1 Hsum0].
  unfold ColourCount in Hcount0, Hcount1.
  destruct Hflip as [-> | ->].
  - destruct (Z.eq_dec 0 0); [|contradiction].
    rewrite Hcount1, <- Hsum1.
    f_equal. apply map_ext. intro v. apply Z.lxor_0_r.
  - destruct (Z.eq_dec 1 0); [lia|].
    rewrite Hcount0, <- Hsum0, map_map. reflexivity.
Qed.
Lemma extend_consistent__scan_and_component_closure :
  forall n comments before after vertices base flip,
    (forall i, 0 <= i < Zlength comments ->
       let '(u, v, _) := comment_at comments i in
       1 <= u <= n /\ 1 <= v <= n) ->
    NewColourSet n before after vertices ->
    ColouredClosed comments before -> ColouredClosed comments after ->
    ParityRespected comments after -> ColourValues n after ->
    ConsistentOn n comments before base ->
    (flip = 0 \/ flip = 1) ->
    ConsistentOn n comments after
      (fold_right
        (fun v r => replace_Znth (v - 1)
          (Z.lxor (Znth v after 0) flip) r) base vertices).
Proof.
  intros n comments before after vertices base flip Hbounds Hnew Hclosed_before
    Hclosed_after Hparity Hvalues Hbase Hflip.
  destruct Hnew as [Hnodup [Hvbounds [Hnewiff Hsame]]].
  destruct Hbase as [[Hlen [Hbase_bits Hbase_zero]] Hbase_cons].
  split.
  - split.
    + apply fold_replace_length__scan_and_component_closure. exact Hlen.
    + split.
      * intros v Hv Hcol.
        destruct (in_dec Z.eq_dec v vertices) as [Hin | Hout].
        -- rewrite (fold_replace_member__scan_and_component_closure
              vertices n base _ v Hlen Hvbounds Hv Hin).
           apply lxor_bit__scan_and_component_closure; [|exact Hflip].
           unfold ColourValues in Hvalues. destruct Hvalues as [_ Hvalues].
           specialize (Hvalues v Hv). destruct Hvalues as [Hm | Hb].
           ++ exfalso. apply Hcol. exact Hm.
           ++ exact Hb.
        -- rewrite (fold_replace_outside__scan_and_component_closure
              vertices n base _ v Hlen Hvbounds Hv Hout).
           apply Hbase_bits; [exact Hv |].
           rewrite (Hsame v Hv Hout) in Hcol. exact Hcol.
      * intros v Hv Huncol.
        assert (Hout : ~ In v vertices).
        { intro Hin. apply (proj1 (Hnewiff v Hv)) in Hin. tauto. }
        rewrite (fold_replace_outside__scan_and_component_closure
          vertices n base _ v Hlen Hvbounds Hv Hout).
        apply Hbase_zero; [exact Hv |].
        rewrite <- (Hsame v Hv Hout). exact Huncol.
  - intros i Hi.
    destruct (comment_at comments i) as [[u v] w] eqn:Hcomment.
    intros Hu_after Hv_after.
    specialize (Hbounds i Hi). rewrite Hcomment in Hbounds.
    destruct Hbounds as [Hu Hv].
    assert (Hnewfull : NewColourSet n before after vertices).
    { unfold NewColourSet. exact (conj Hnodup (conj Hvbounds (conj Hnewiff Hsame))). }
    pose proof (new_component_edge_closed__scan_and_component_closure
      n comments before after vertices i u v w) as Hedge.
    specialize (Hedge Hnewfull Hclosed_before
      Hclosed_after Hi Hcomment Hu Hv).
    destruct (in_dec Z.eq_dec u vertices) as [Hu_in | Hu_out].
    + assert (Hv_in : In v vertices) by (apply (proj1 Hedge); exact Hu_in).
      rewrite (fold_replace_member__scan_and_component_closure
        vertices n base _ v Hlen Hvbounds Hv Hv_in).
      rewrite (fold_replace_member__scan_and_component_closure
        vertices n base _ u Hlen Hvbounds Hu Hu_in).
      specialize (Hparity i Hi). rewrite Hcomment in Hparity.
      rewrite (Hparity Hu_after Hv_after).
      apply lxor_shuffle__scan_and_component_closure.
    + assert (Hv_out : ~ In v vertices).
      { intro Hv_in. apply Hu_out. apply (proj2 Hedge). exact Hv_in. }
      rewrite (fold_replace_outside__scan_and_component_closure
        vertices n base _ v Hlen Hvbounds Hv Hv_out).
      rewrite (fold_replace_outside__scan_and_component_closure
        vertices n base _ u Hlen Hvbounds Hu Hu_out).
      specialize (Hbase_cons i Hi). rewrite Hcomment in Hbase_cons.
      apply Hbase_cons.
      * rewrite <- (Hsame u Hu Hu_out). exact Hu_after.
      * rewrite <- (Hsame v Hv Hv_out). exact Hv_after.
Qed.
Lemma fold_replace_sum_general__scan_and_component_closure :
  forall (vertices : list Z) (n : Z) (base : list Z) (f : Z -> Z),
    Zlength base = n -> NoDup vertices ->
    Forall (fun x => 1 <= x <= n) vertices ->
    fold_right Z.add 0
      (fold_right (fun x r => replace_Znth (x - 1) (f x) r)
        base vertices) =
    fold_right Z.add 0 base -
      fold_right Z.add 0 (map (fun x => Znth (x - 1) base 0) vertices) +
      fold_right Z.add 0 (map f vertices).
Proof.
  induction vertices as [|x vertices IH]; intros n base f Hlen Hnd Hbounds.
  - simpl. ring.
  - inversion Hnd as [|? ? Hnotin Hndtail]; subst.
    inversion Hbounds as [|? ? Hx Htail]; subst. simpl.
    pose proof (fold_replace_length__scan_and_component_closure
      vertices (Zlength base) base f eq_refl) as Htail_len.
    rewrite sum_replace__scan_and_component_closure.
    + rewrite (fold_replace_outside__scan_and_component_closure
        vertices (Zlength base) base f x eq_refl Htail Hx Hnotin).
      rewrite (IH (Zlength base) base f eq_refl Hndtail Htail).
      ring.
    + rewrite Htail_len; lia.
Qed.
Lemma restrict_consistent__scan_and_component_closure :
  forall n comments before after vertices roles,
    (forall i, 0 <= i < Zlength comments ->
       let '(u, v, _) := comment_at comments i in
       1 <= u <= n /\ 1 <= v <= n) ->
    NewColourSet n before after vertices ->
    ConsistentOn n comments after roles ->
    ConsistentOn n comments before
      (fold_right (fun v r => replace_Znth (v - 1) 0 r) roles vertices).
Proof.
  intros n comments before after vertices roles Hbounds Hnew Hroles.
  destruct Hnew as [Hnodup [Hvbounds [Hnewiff Hsame]]].
  destruct Hroles as [[Hlen [Hrole_bits Hrole_zero]] Hrole_cons].
  split.
  - split.
    + apply fold_replace_length__scan_and_component_closure. exact Hlen.
    + split.
      * intros v Hv Hbefore_col.
        assert (Hout : ~ In v vertices).
        { intro Hin. apply (proj1 (Hnewiff v Hv)) in Hin. tauto. }
        rewrite (fold_replace_outside__scan_and_component_closure
          vertices n roles (fun _ => 0) v Hlen Hvbounds Hv Hout).
        apply Hrole_bits; [exact Hv |].
        rewrite (Hsame v Hv Hout). exact Hbefore_col.
      * intros v Hv Hbefore_uncol.
        destruct (in_dec Z.eq_dec v vertices) as [Hin | Hout].
        -- rewrite (fold_replace_member__scan_and_component_closure
             vertices n roles (fun _ => 0) v Hlen Hvbounds Hv Hin).
           reflexivity.
        -- rewrite (fold_replace_outside__scan_and_component_closure
             vertices n roles (fun _ => 0) v Hlen Hvbounds Hv Hout).
           apply Hrole_zero; [exact Hv |].
           rewrite (Hsame v Hv Hout). exact Hbefore_uncol.
  - intros i Hi.
    destruct (comment_at comments i) as [[u v] w] eqn:Hcomment.
    intros Hu_before Hv_before.
    specialize (Hbounds i Hi). rewrite Hcomment in Hbounds.
    destruct Hbounds as [Hu Hv].
    assert (Hu_out : ~ In u vertices).
    { intro Hin. apply (proj1 (Hnewiff u Hu)) in Hin. tauto. }
    assert (Hv_out : ~ In v vertices).
    { intro Hin. apply (proj1 (Hnewiff v Hv)) in Hin. tauto. }
    rewrite (fold_replace_outside__scan_and_component_closure
      vertices n roles (fun _ => 0) v Hlen Hvbounds Hv Hv_out).
    rewrite (fold_replace_outside__scan_and_component_closure
      vertices n roles (fun _ => 0) u Hlen Hvbounds Hu Hu_out).
    specialize (Hrole_cons i Hi). rewrite Hcomment in Hrole_cons.
    apply Hrole_cons.
    + rewrite (Hsame u Hu Hu_out). exact Hu_before.
    + rewrite (Hsame v Hv Hv_out). exact Hv_before.
Qed.
Lemma consistent_on_vertices__scan_and_component_closure :
  forall n comments before after vertices roles,
    NewColourSet n before after vertices ->
    ConsistentOn n comments after roles ->
    RolesConsistentOnVertices n comments vertices roles.
Proof.
  intros n comments before after vertices roles Hnew Hroles.
  destruct Hnew as [_ [Hbounds [Hnewiff _]]].
  destruct Hroles as [[Hlen [Hbits Hzero]] Hconsistent].
  unfold RolesConsistentOnVertices. split; [exact Hlen |]. split.
  - intros v Hin. apply Hbits.
    + rewrite Forall_forall in Hbounds. exact (Hbounds v Hin).
    + apply (proj1 (Hnewiff v ltac:(rewrite Forall_forall in Hbounds; exact (Hbounds v Hin)))) in Hin.
      tauto.
  - intros i Hi.
    destruct (comment_at comments i) as [[u v] w] eqn:Hcomment.
    intros Hu_in Hv_in.
    specialize (Hconsistent i Hi). rewrite Hcomment in Hconsistent.
    apply Hconsistent.
    + apply (proj1 (Hnewiff u ltac:(rewrite Forall_forall in Hbounds; exact (Hbounds u Hu_in)))) in Hu_in.
      tauto.
    + apply (proj1 (Hnewiff v ltac:(rewrite Forall_forall in Hbounds; exact (Hbounds v Hv_in)))) in Hv_in.
      tauto.
Qed.
Lemma component_roles_sum__scan_and_component_closure :
  forall n comments before after vertices roles c0 c1,
    NewColourSet n before after vertices -> ColourValues n after ->
    ColourCount after vertices 0 c0 -> ColourCount after vertices 1 c1 ->
    ComponentTwoChoicesLocal n comments after vertices ->
    ConsistentOn n comments after roles ->
    exists flip, (flip = 0 \/ flip = 1) /\
      fold_right Z.add 0
        (map (fun v => Znth (v - 1) roles 0) vertices) =
      if Z.eq_dec flip 0 then c1 else c0.
Proof.
  intros n comments before after vertices roles c0 c1 Hnew Hvalues
    Hcount0 Hcount1 Hlocal Hroles.
  pose proof (consistent_on_vertices__scan_and_component_closure
    n comments before after vertices roles Hnew Hroles) as Hlocal_roles.
  specialize (Hlocal roles Hlocal_roles).
  destruct Hlocal as [flip [Hflip Hpoint]]. exists flip. split; [exact Hflip |].
  destruct Hnew as [_ [Hbounds [Hnewiff _]]].
  assert (Hcoloured : forall v, In v vertices -> Znth v after 0 <> -1).
  { intros v Hin. rewrite Forall_forall in Hbounds.
    apply (proj1 (Hnewiff v (Hbounds v Hin))) in Hin. tauto. }
  replace (map (fun v => Znth (v - 1) roles 0) vertices) with
    (map (fun v => Z.lxor (Znth v after 0) flip) vertices).
  - apply component_bit_sum__scan_and_component_closure with n;
      assumption.
  - symmetry. apply map_ext_in. intros v Hin. apply Hpoint. exact Hin.
Qed.
Lemma sum_map_zero__scan_and_component_closure :
  forall xs : list Z,
    fold_right Z.add 0 (map (fun _ : Z => 0) xs) = 0.
Proof. induction xs as [|x xs IH]; simpl; [reflexivity | exact IH]. Qed.
Lemma component_max_lift__scan_and_component_closure :
  forall n comments before after vertices c0 c1,
    (forall i, 0 <= i < Zlength comments ->
       let '(u, v, _) := comment_at comments i in
       1 <= u <= n /\ 1 <= v <= n) ->
    NewColourSet n before after vertices ->
    ColouredClosed comments before -> ColouredClosed comments after ->
    ParityRespected comments after -> ColourValues n after ->
    ColourCount after vertices 0 c0 -> ColourCount after vertices 1 c1 ->
    ComponentTwoChoicesLocal n comments after vertices ->
    forall t, MaxImpostersOn n comments before t ->
      MaxImpostersOn n comments after (t + Z.max c0 c1).
Proof.
  intros n comments before after vertices c0 c1 Hbounds Hnew Hclosed_before
    Hclosed_after Hparity Hvalues Hcount0 Hcount1 Hlocal t Hmax.
  assert (Hchoose : exists flip, (flip = 0 \/ flip = 1) /\
      (if Z.eq_dec flip 0 then c1 else c0) = Z.max c0 c1).
  { destruct (Z_le_dec c0 c1) as [Hle | Hgt].
    - exists 0. split; [auto |].
      destruct (Z.eq_dec 0 0); [rewrite Z.max_r by lia; reflexivity | contradiction].
    - exists 1. split; [auto |].
      destruct (Z.eq_dec 1 0); [lia | rewrite Z.max_l by lia; reflexivity]. }
  destruct Hchoose as [flip [Hflip Hchoice]].
  unfold MaxImpostersOn, max_value_of_subset, max_object_of_subset in Hmax |- *.
  destruct Hmax as [best [[[best_roles [Hbest_cons Hbest_sum]] Hupper] Hbest_value]].
  assert (Hnew_parts := Hnew).
  destruct Hnew_parts as [Hnodup [Hvbounds [Hnewiff Hsame]]].
  assert (Hvertices_old_zero : forall v, In v vertices ->
      Znth (v - 1) best_roles 0 = 0).
  { intros v Hin. destruct Hbest_cons as [[Hlen [Hbits Hzero]] Hcons].
    apply Hzero.
    - rewrite Forall_forall in Hvbounds. exact (Hvbounds v Hin).
    - apply (proj1 (Hnewiff v ltac:(rewrite Forall_forall in Hvbounds;
        exact (Hvbounds v Hin)))) in Hin. tauto. }
  exists (t + Z.max c0 c1). split; [split | reflexivity].
  - exists (fold_right
      (fun v r => replace_Znth (v - 1)
        (Z.lxor (Znth v after 0) flip) r) best_roles vertices).
    split.
    + apply extend_consistent__scan_and_component_closure with before;
        assumption.
    + rewrite (fold_replace_sum__scan_and_component_closure
        vertices n best_roles (fun v => Z.lxor (Znth v after 0) flip)).
      * pose proof (component_bit_sum__scan_and_component_closure
          n after vertices c0 c1 flip Hvalues Hvbounds) as Hcomponent.
        assert (Hcoloured : forall v, In v vertices -> Znth v after 0 <> -1).
        { intros v Hin. rewrite Forall_forall in Hvbounds.
          apply (proj1 (Hnewiff v (Hvbounds v Hin))) in Hin. tauto. }
        specialize (Hcomponent Hcoloured Hcount0 Hcount1 Hflip).
        rewrite Hcomponent, Hchoice, <- Hbest_sum, Hbest_value. reflexivity.
      * destruct Hbest_cons as [[Hlen _] _]. exact Hlen.
      * exact Hnodup.
      * exact Hvbounds.
      * exact Hvertices_old_zero.
  - intros candidate Hcandidate.
    destruct Hcandidate as [roles [Hroles Hcandidate_sum]].
    pose proof (restrict_consistent__scan_and_component_closure
      n comments before after vertices roles Hbounds Hnew Hroles) as Hrestricted.
    pose proof (component_roles_sum__scan_and_component_closure
      n comments before after vertices roles c0 c1 Hnew Hvalues
      Hcount0 Hcount1 Hlocal Hroles) as Hroles_component.
    destruct Hroles_component as [roles_flip [Hroles_flip Hroles_component]].
    destruct Hroles as [[Hroles_len _] _].
    pose proof (fold_replace_sum_general__scan_and_component_closure
      vertices n roles (fun _ => 0) Hroles_len Hnodup Hvbounds) as Hsum_restrict.
    pose proof (sum_map_zero__scan_and_component_closure vertices) as Hzero_sum.
    rewrite Hzero_sum in Hsum_restrict.
    assert (Hrestricted_upper :
      fold_right Z.add 0
        (fold_right (fun v r => replace_Znth (v - 1) 0 r)
          roles vertices) <= best).
    { apply Hupper. exists (fold_right
        (fun v r => replace_Znth (v - 1) 0 r) roles vertices).
      split; [exact Hrestricted | reflexivity]. }
    assert (Hcomponent_upper :
      (if Z.eq_dec roles_flip 0 then c1 else c0) <= Z.max c0 c1).
    { destruct (Z.eq_dec roles_flip 0); [apply Z.le_max_r | apply Z.le_max_l]. }
    rewrite Hroles_component in Hsum_restrict.
    rewrite Hcandidate_sum, Hbest_value in *.
    lia.
Qed.
Lemma component_frontier_complete__scan_and_component_closure :
  forall n cap comments hs ns ts ws before after vertices c0 c1,
    cap = Zlength comments ->
    ForwardStar n cap cap hs ns ts ws comments ->
    ForwardStarRanges n cap hs ns ts ws ->
    ParityRespected comments before -> ColouredClosed comments before ->
    ComponentFrontierStrong n comments before after vertices nil c0 c1 ->
    ComponentCompleteStrong n comments before after vertices c0 c1.
Proof.
  intros n cap comments hs ns ts ws before after vertices c0 c1 Hcap Hstar
    Hranges Hparity_before Hclosed_before Hfrontier_strong.
  unfold ComponentFrontierStrong in Hfrontier_strong.
  destruct Hfrontier_strong as [Hfrontier Hlocal].
  unfold ComponentFrontier in Hfrontier.
  destruct Hfrontier as
    [Hvalues [Hnew [Hglobal [Hscanned [Hcount0 Hcount1]]]]].
  rewrite app_nil_r in Hnew, Hglobal, Hlocal.
  pose proof (frontier_respected_closed__scan_and_component_closure
    n cap comments hs ns ts ws before after vertices Hcap Hstar Hranges
    Hparity_before Hclosed_before Hnew Hscanned) as [Hparity_after Hclosed_after].
  unfold ComponentCompleteStrong. split.
  - unfold ComponentComplete. split.
    + unfold ComponentFrontier. rewrite app_nil_r.
      exact (conj Hvalues
        (conj Hnew (conj Hglobal (conj Hscanned (conj Hcount0 Hcount1))))).
    + split; [exact Hparity_after |]. split; [exact Hclosed_after |].
      apply (component_max_lift__scan_and_component_closure
        n comments before after vertices c0 c1);
        try assumption.
      apply comment_bounds_from_forward_star__scan_and_component_closure
        with cap hs ns ts ws; assumption.
  - exact Hlocal.
Qed.
Lemma xor_roles_equiv__final_specification : forall ru rv c,
  (ru = 0 \/ ru = 1) -> (rv = 0 \/ rv = 1) -> (c = 0 \/ c = 1) ->
  ((ru = 0 /\ rv = c) \/ (ru = 1 /\ rv <> c) <-> rv = Z.lxor ru c).
Proof.
  intros ru rv c Hru Hrv Hc.
  destruct Hru, Hrv, Hc; subst; vm_compute; intuition congruence.
Qed.
Lemma roles_consistent_iff_consistent_on_total__final_specification :
  forall n comments cs roles,
  (forall v, 1 <= v <= n -> Znth v cs 0 <> -1) ->
  (forall i, 0 <= i < Zlength comments ->
    let '(u, v, w) := comment_at comments i in
    1 <= u <= n /\ 1 <= v <= n /\ (w = 0 \/ w = 1)) ->
  (ConsistentOn n comments cs roles <-> RolesConsistent n comments roles).
Proof.
  intros n comments cs roles Htotal Hvalid.
  unfold ConsistentOn, OnSet, RolesConsistent.
  split.
  - intros [[Hlen [Hvals Huncol]] Hpar].
    split; [exact Hlen|].
    split.
    + apply Forall_forall. intros x Hin.
      destruct (In_nth roles x 0 Hin) as [k [Hk Hnth]].
      specialize (Hvals (Z.of_nat k + 1)).
      assert (1 <= Z.of_nat k + 1 <= n) as Hbounds.
      { rewrite Zlength_correct in Hlen. lia. }
      specialize (Hvals Hbounds (Htotal _ Hbounds)).
      unfold Znth in Hvals.
      replace (Z.to_nat (Z.of_nat k + 1 - 1)) with k in Hvals by lia.
      rewrite Hnth in Hvals. exact Hvals.
    + intros [[u v] w] Hin.
      destruct (In_nth comments (u, v, w) (0, 0, 0) Hin) as [k [Hk Hnth]].
      set (i := Z.of_nat k).
      assert (Hi : 0 <= i < Zlength comments).
      { subst i. rewrite Zlength_correct. lia. }
      assert (Hat : comment_at comments i = (u, v, w)).
      { unfold comment_at, Znth. subst i. rewrite Nat2Z.id. exact Hnth. }
      specialize (Hvalid i Hi). rewrite Hat in Hvalid.
      destruct Hvalid as [Hu [Hv Hw]].
      specialize (Hpar i Hi). rewrite Hat in Hpar.
      specialize (Hpar (Htotal u Hu) (Htotal v Hv)).
      pose proof (xor_roles_equiv__final_specification
        (Znth (u - 1) roles 0) (Znth (v - 1) roles 0) w
        (Hvals u Hu (Htotal u Hu)) (Hvals v Hv (Htotal v Hv)) Hw) as Hxor.
      apply (proj2 Hxor). exact Hpar.
  - intros [Hlen [Hforall Hcomments]].
    split.
    + split; [exact Hlen|]. split.
      * intros v Hv _.
        apply (proj1 (Forall_forall _ _) Hforall).
        unfold Znth. apply nth_In.
        apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
        rewrite <- Zlength_correct. lia.
      * intros v Hv Hneg. exfalso. apply (Htotal v Hv). exact Hneg.
    + intros i Hi.
      destruct (comment_at comments i) as [[u v] w] eqn:Hat.
      intros _ _.
      assert (Hin : In (comment_at comments i) comments).
      { unfold comment_at, Znth. apply nth_In.
        apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
        rewrite <- Zlength_correct. lia. }
      specialize (Hcomments _ Hin). rewrite Hat in Hcomments.
      specialize (Hvalid i Hi). rewrite Hat in Hvalid.
      destruct Hvalid as [Hu [Hv Hw]].
      assert (Hru : Znth (u - 1) roles 0 = 0 \/ Znth (u - 1) roles 0 = 1).
      { apply (proj1 (Forall_forall _ _) Hforall).
        unfold Znth. apply nth_In.
        apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
        rewrite <- Zlength_correct. lia. }
      assert (Hrv : Znth (v - 1) roles 0 = 0 \/ Znth (v - 1) roles 0 = 1).
      { apply (proj1 (Forall_forall _ _) Hforall).
        unfold Znth. apply nth_In.
        apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
        rewrite <- Zlength_correct. lia. }
      pose proof (xor_roles_equiv__final_specification
        (Znth (u - 1) roles 0) (Znth (v - 1) roles 0) w Hru Hrv Hw) as Hxor.
      apply (proj1 Hxor). exact Hcomments.
Qed.
Lemma max_imposters_on_total_implies_spec__final_specification :
  forall n comments cs total,
  0 <= total ->
  (forall v, 1 <= v <= n -> Znth v cs 0 <> -1) ->
  (forall i, 0 <= i < Zlength comments ->
    let '(u, v, w) := comment_at comments i in
    1 <= u <= n /\ 1 <= v <= n /\ (w = 0 \/ w = 1)) ->
  MaxImpostersOn n comments cs total ->
  Spec n comments total.
Proof.
  intros n comments cs total Hnonneg Htotal Hvalid Hmax.
  unfold Spec. right. split; [lia|].
  unfold MaxImpostersOn in Hmax.
  destruct Hmax as [x [[Hx Hupper] Hxtotal]].
  exists x. split; [split|exact Hxtotal].
  - destruct Hx as [r [Hr Hx]].
    exists r. split.
    + apply (proj1 (roles_consistent_iff_consistent_on_total__final_specification
        n comments cs r Htotal Hvalid)). exact Hr.
    + unfold ImposterCount. exact Hx.
  - intros b Hb. destruct Hb as [r [Hr Hb]].
    apply Hupper. exists r. split.
    + apply (proj2 (roles_consistent_iff_consistent_on_total__final_specification
        n comments cs r Htotal Hvalid)). exact Hr.
    + unfold ImposterCount in Hb. exact Hb.
Qed.
