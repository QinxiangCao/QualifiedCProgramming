From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_lib_core.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** * S6 -- resolution and minimization.
    The implicit resolvent is [learnt ++ map (fun x => literal_neg (view_lit a x)) S].
    [S] contains unresolved current-level variables, [cnt = Zlength S], and
    [learnt] contains lower-level literals. *)

(** ----- generic list helpers ----- *)

Definition zmem (x : Z) (l : list Z) : bool := existsb (Z.eqb x) l.

Lemma zmem_true_iff : forall x l, zmem x l = true <-> In x l.
Proof.
  intros x l. unfold zmem. rewrite existsb_exists. split.
  - intros [y [Hy He]]. apply Z.eqb_eq in He. subst y. exact Hy.
  - intro Hin. exists x. split; [exact Hin | apply Z.eqb_refl].
Qed.

Lemma zmem_false_iff : forall x l, zmem x l = false <-> ~ In x l.
Proof.
  intros x l. split.
  - intros Hf Hin. apply zmem_true_iff in Hin. congruence.
  - intro Hn. destruct (zmem x l) eqn:E; [|reflexivity].
    exfalso. apply Hn. apply zmem_true_iff. exact E.
Qed.

Definition zremove (x : Z) (l : list Z) : list Z :=
  filter (fun y => negb (Z.eqb y x)) l.

Lemma In_zremove_iff : forall x y l,
  In y (zremove x l) <-> In y l /\ y <> x.
Proof.
  intros x y l. unfold zremove. rewrite filter_In. split.
  - intros [H1 H2]. split; [exact H1|].
    apply negb_true_iff in H2. apply Z.eqb_neq in H2. exact H2.
  - intros [H1 H2]. split; [exact H1|].
    apply negb_true_iff. apply Z.eqb_neq. exact H2.
Qed.

Lemma NoDup_app_intro : forall (A : Type) (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hdis.
  induction l1 as [|a l1 IH]; [exact H2|].
  cbn [app]. inversion H1 as [|? ? Hna H1']; subst.
  constructor.
  - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (Hna Hin).
    + exact (Hdis a (or_introl eq_refl) Hin).
  - apply IH; [exact H1'|].
    intros x Hx. apply Hdis. right. exact Hx.
Qed.

Lemma In_map_filter :
  forall (A B : Type) (f : A -> B) (g : A -> bool) (l : list A) (y : B),
  In y (map f (filter g l)) -> In y (map f l).
Proof.
  intros A B f g l y Hin.
  rewrite in_map_iff in Hin. destruct Hin as [x [Hf Hx]].
  apply filter_In in Hx. destruct Hx as [Hx _].
  rewrite in_map_iff. exists x. split; assumption.
Qed.

Lemma NoDup_map_filter :
  forall (A B : Type) (f : A -> B) (g : A -> bool) (l : list A),
  NoDup (map f l) -> NoDup (map f (filter g l)).
Proof.
  intros A B f g l Hnd.
  induction l as [|a l IH]; [constructor|].
  cbn [map filter] in *.
  inversion Hnd as [|? ? Hna Hnd']; subst.
  destruct (g a).
  - cbn [map]. constructor.
    + intro Hin. apply In_map_filter in Hin. exact (Hna Hin).
    + apply IH. exact Hnd'.
  - apply IH. exact Hnd'.
Qed.

(** ----- literal-shape helpers ----- *)

Lemma satisfying_literal_var : forall x b,
  literal_var (satisfying_literal x b) = x.
Proof. intros x [|]; reflexivity. Qed.

(** ----- the trail literal of an assigned variable, on the view ----- *)

Definition view_lit (a : cdcl_view) (x : Z) : literal :=
  match assignment a x with
  | Some b => satisfying_literal x b
  | None => Pos x
  end.

Lemma view_lit_assigned : forall a x b,
  assignment a x = Some b -> view_lit a x = satisfying_literal x b.
Proof. intros a x b H. unfold view_lit. rewrite H. reflexivity. Qed.

Lemma view_lit_var : forall a x, literal_var (view_lit a x) = x.
Proof.
  intros a x. unfold view_lit.
  destruct (assignment a x) as [[|]|]; reflexivity.
Qed.

Lemma neg_view_lit_false : forall a x b,
  assignment a x = Some b ->
  eval_partial_literal (assignment a) (literal_neg (view_lit a x))
  = Some false.
Proof.
  intros a x b H.
  rewrite (view_lit_assigned a x b H), literal_neg_satisfying.
  apply eval_falsified_literal_false. exact H.
Qed.

(** ----- decision-level classifiers (booleans, so the ghost sets are
    computed by [filter] exactly as the C loop walks the clause) ----- *)

Definition at_current_level_b (a : cdcl_view) (l : literal) : bool :=
  match level_of a (literal_var l) with
  | Some d => Z.eqb d (current_level a)
  | None => false
  end.

Definition below_current_b (a : cdcl_view) (l : literal) : bool :=
  match level_of a (literal_var l) with
  | Some d => andb (Z.ltb 0 d) (Z.ltb d (current_level a))
  | None => false
  end.

Lemma at_current_level_b_true_iff : forall a l,
  at_current_level_b a l = true <->
  level_of a (literal_var l) = Some (current_level a).
Proof.
  intros a l. unfold at_current_level_b.
  destruct (level_of a (literal_var l)) as [d|] eqn:E.
  - split; intro H.
    + apply Z.eqb_eq in H. subst d. reflexivity.
    + injection H as ->. apply Z.eqb_refl.
  - split; intro H; discriminate.
Qed.

Lemma below_current_b_true_iff : forall a l,
  below_current_b a l = true <->
  (exists d, level_of a (literal_var l) = Some d /\
             0 < d < current_level a).
Proof.
  intros a l. unfold below_current_b.
  destruct (level_of a (literal_var l)) as [d|] eqn:E.
  - split.
    + intro H. apply andb_prop in H. destruct H as [H1 H2].
      apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      exists d. split; [reflexivity|lia].
    + intros [d0 [Hd0 Hb]]. injection Hd0 as ->.
      apply andb_true_intro. split; apply Z.ltb_lt; lia.
  - split; [discriminate|].
    intros [d0 [Hd0 _]]. discriminate.
Qed.

(** ----- the analyze-loop carrier ----- *)

(** Rank (= trail position) comparison on the view. *)
Definition rank_lt (a : cdcl_view) (y z : Z) : Prop :=
  exists ry rz,
    assignment_rank a y = Some ry /\
    assignment_rank a z = Some rz /\ (ry < rz)%nat.

(** The ghost image of the C [tags] array (never cleared inside the
    analyze loop): pending current-level variables
    [S], already-resolved current-level variables [R], and the variables
    of the collected lower-level literals. *)
Definition analyze_tags (S R : list Z) (learnt : clause) : list Z :=
  S ++ R ++ map literal_var learnt.

(** [S] = tagged current-level variables not yet resolved, [R] = the
    already-resolved current-level variables (they stay
    tagged in the C, so the ghost must model them to match the [tags]
    test, and they sit strictly above every pending [S] member in trail
    order -- resolution proceeds in reverse trail order), [learnt] = the
    collected strictly-lower-level literals; the implicit resolvent is
    [learnt] plus the negated trail literals of [S].  Level-0 literals
    have been dropped (they are permanently implied).  The invariant also
    carries assignedness of [S] and falseness of [learnt] -- both are loop
    invariants of the C code and both are needed by [analyze_exit]. *)
Definition analyze_inv
    (F : cnf) (a : cdcl_view) (S R : list Z) (learnt : clause) : Prop :=
  entails_clause F
    (learnt ++ map (fun x => literal_neg (view_lit a x)) S) /\
  NoDup (analyze_tags S R learnt) /\
  Forall (fun x => level_of a x = Some (current_level a)) S /\
  Forall (fun x => exists b, assignment a x = Some b) S /\
  Forall (fun x => level_of a x = Some (current_level a)) R /\
  Forall (fun r => forall s, In s S -> rank_lt a s r) R /\
  Forall (fun l => exists d, level_of a (literal_var l) = Some d /\
                             0 < d < current_level a) learnt /\
  clause_false (assignment a) learnt.

Lemma level_disjoint_S_learnt :
  forall (a : cdcl_view) (S : list Z) (learnt : clause),
  Forall (fun x => level_of a x = Some (current_level a)) S ->
  Forall (fun l => exists d, level_of a (literal_var l) = Some d /\
                             0 < d < current_level a) learnt ->
  forall x, In x S -> ~ In x (map literal_var learnt).
Proof.
  intros a S learnt HS HL x HxS HxL.
  rewrite Forall_forall in HS, HL.
  rewrite in_map_iff in HxL. destruct HxL as [l [Hvl Hin]].
  destruct (HL l Hin) as [d [Hld Hd]].
  specialize (HS x HxS). rewrite <- Hvl in HS. rewrite HS in Hld.
  injection Hld as Heq. lia.
Qed.

(** ----- initialization from the conflict clause ----- *)

Definition analyze_start_S (a : cdcl_view) (C : clause) : list Z :=
  map literal_var (filter (at_current_level_b a) C).

Definition analyze_start_learnt (a : cdcl_view) (C : clause) : clause :=
  filter (below_current_b a) C.

Lemma analyze_init : forall (F : cnf) (a : cdcl_view) (C : clause),
  grounded_at a ->
  closed_levels a ->
  (forall x b, assignment a x = Some b -> level_of a x = Some 0 ->
     entails_clause F [satisfying_literal x b]) ->
  entails_clause F C ->
  clause_false (assignment a) C ->
  NoDup (map literal_var C) ->
  analyze_inv F a (analyze_start_S a C) [] (analyze_start_learnt a C).
Proof.
  intros F a C Hg Hcl Hpre HentC Hfalse Hnd.
  destruct Hcl as [_ [Hbound _]].
  assert (Hlit : forall l, In l C ->
    exists b d, assignment a (literal_var l) = Some b /\
                l = falsified_literal (literal_var l) b /\
                level_of a (literal_var l) = Some d /\
                0 <= d <= current_level a).
  { intros l Hin.
    destruct (eval_partial_false_shape _ _ (Hfalse l Hin))
      as [b [Hass Hshape]].
    destruct (Hg (literal_var l) b Hass) as [d [rx [Hlev _]]].
    exists b, d. repeat split; try assumption.
    - exact (proj1 (Hbound _ _ _ Hass Hlev)).
    - exact (proj2 (Hbound _ _ _ Hass Hlev)). }
  assert (E1 : entails_clause F
    (analyze_start_learnt a C
       ++ map (fun x => literal_neg (view_lit a x)) (analyze_start_S a C))).
  { intros rho Hmod.
    destruct (HentC rho Hmod) as [l [Hin Ht]].
    destruct (Hlit l Hin) as [b [d [Hass [Hshape [Hlev Hbd]]]]].
    destruct (Z.eq_dec d 0) as [-> | Hd0].
    - exfalso.
      destruct (Hpre _ _ Hass Hlev rho Hmod) as [k [Hk Hkt]].
      destruct Hk as [Heq|[]]. subst k.
      rewrite Hshape, <- literal_neg_satisfying, eval_literal_neg, Hkt
        in Ht.
      discriminate.
    - destruct (Z.eq_dec d (current_level a)) as [Heq | Hne].
      + subst d.
        assert (Hb : at_current_level_b a l = true)
          by (apply (proj2 (at_current_level_b_true_iff a l)); exact Hlev).
        assert (HinS : In (literal_var l) (analyze_start_S a C)).
        { unfold analyze_start_S. apply in_map.
          apply filter_In. split; assumption. }
        assert (Hkl : literal_neg (view_lit a (literal_var l)) = l).
        { rewrite (view_lit_assigned a (literal_var l) b Hass),
            literal_neg_satisfying. symmetry. exact Hshape. }
        exists l. split; [|exact Ht].
        apply in_or_app. right. rewrite <- Hkl.
        apply (in_map (fun x => literal_neg (view_lit a x))). exact HinS.
      + assert (Hb : below_current_b a l = true).
        { apply (proj2 (below_current_b_true_iff a l)).
          exists d. split; [exact Hlev|lia]. }
        exists l. split; [|exact Ht].
        apply in_or_app. left. unfold analyze_start_learnt.
        apply filter_In. split; assumption. }
  assert (E2 : NoDup (analyze_start_S a C))
    by (apply NoDup_map_filter; exact Hnd).
  assert (E3 : Forall (fun x => level_of a x = Some (current_level a))
                 (analyze_start_S a C)).
  { rewrite Forall_forall. intros x Hx.
    unfold analyze_start_S in Hx. rewrite in_map_iff in Hx.
    destruct Hx as [l [Hvl Hlf]]. apply filter_In in Hlf.
    destruct Hlf as [_ Hb].
    apply at_current_level_b_true_iff in Hb. rewrite <- Hvl. exact Hb. }
  assert (E4 : Forall (fun x => exists b, assignment a x = Some b)
                 (analyze_start_S a C)).
  { rewrite Forall_forall. intros x Hx.
    unfold analyze_start_S in Hx. rewrite in_map_iff in Hx.
    destruct Hx as [l [Hvl Hlf]]. apply filter_In in Hlf.
    destruct Hlf as [Hin _].
    destruct (Hlit l Hin) as [b [d [Hass _]]].
    exists b. rewrite <- Hvl. exact Hass. }
  assert (E5 : Forall (fun l => exists d,
                 level_of a (literal_var l) = Some d /\
                 0 < d < current_level a) (analyze_start_learnt a C)).
  { rewrite Forall_forall. intros l Hl.
    unfold analyze_start_learnt in Hl. apply filter_In in Hl.
    destruct Hl as [_ Hb].
    apply below_current_b_true_iff in Hb. exact Hb. }
  assert (E6 : clause_false (assignment a) (analyze_start_learnt a C)).
  { intros l Hl. unfold analyze_start_learnt in Hl.
    apply filter_In in Hl. destruct Hl as [Hin _].
    exact (Hfalse l Hin). }
  assert (E7 : NoDup (map literal_var (analyze_start_learnt a C)))
    by (apply NoDup_map_filter; exact Hnd).
  assert (Etags : NoDup (analyze_tags (analyze_start_S a C) []
                           (analyze_start_learnt a C))).
  { unfold analyze_tags. cbn [app]. apply NoDup_app_intro.
    - exact E2.
    - exact E7.
    - exact (level_disjoint_S_learnt a _ _ E3 E5). }
  exact (conj E1 (conj Etags (conj E3 (conj E4 (conj (Forall_nil _)
          (conj (Forall_nil _) (conj E5 E6))))))).
Qed.

(** ----- the resolution step ----- *)

(** New current-level variables contributed by the reason clause [c] of
    the resolved variable [x]; variables already tagged (members of
    [analyze_tags S R learnt] -- [x] itself is among them, being in [S])
    are skipped, exactly as [solver_analyze]'s [tags] test skips
    them; the test consults the WHOLE tag set, including the
    already-resolved variables [R]. *)
Definition resolve_new_S
    (a : cdcl_view) (c : clause) (tags : list Z) : list Z :=
  filter (fun y => negb (zmem y tags))
         (map literal_var (filter (at_current_level_b a) c)).

Definition resolve_S
    (a : cdcl_view) (x : Z) (c : clause) (S R : list Z)
    (learnt : clause) : list Z :=
  zremove x S ++ resolve_new_S a c (analyze_tags S R learnt).

(** New strictly-lower-level literals contributed by [c]; literals whose
    variable is already tagged are skipped (for a [learnt] variable its
    unique false literal is already there; [S]/[R] variables sit at the
    current level, so those parts of the test never fire on a lower-level
    literal -- but the ghost test is the C test, verbatim). *)
Definition resolve_new_lits
    (a : cdcl_view) (c : clause) (tags : list Z) : clause :=
  filter (fun l =>
            andb (below_current_b a l)
                 (negb (zmem (literal_var l) tags)))
         c.

Definition resolve_learnt
    (a : cdcl_view) (c : clause) (S R : list Z) (learnt : clause)
    : clause :=
  learnt ++ resolve_new_lits a c (analyze_tags S R learnt).

(* The entailment component of [analyze_resolve_step]'s conclusion.  Resolving the
   conflict clause against [x]'s reason keeps the model-refuting clause: every
   witness literal is either inherited, re-enters the pending set, or is
   recorded in the learnt clause below the current level. *)
Lemma analyze_resolve_entails :
  forall (F : cnf) (a : cdcl_view) (S R : list Z) (learnt : clause)
    (x : Z) (c : clause) (b : bool),
  entails_clause F (learnt ++ map (fun y => literal_neg (view_lit a y)) S) ->
  (forall x' b', assignment a x' = Some b' -> level_of a x' = Some 0 ->
     entails_clause F [satisfying_literal x' b']) ->
  assignment a x = Some b ->
  entails_clause F c ->
  clause_var_injective c ->
  In (satisfying_literal x b) c ->
  (forall m, In m c -> literal_var m <> x ->
    exists b'' dy, assignment a (literal_var m) = Some b'' /\
      m = falsified_literal (literal_var m) b'' /\
      level_of a (literal_var m) = Some dy /\
      0 <= dy <= current_level a) ->
  (forall z, In z (analyze_tags S R learnt) <->
    In z S \/ In z R \/ In z (map literal_var learnt)) ->
  (forall m, In m c -> literal_var m <> x -> ~ In (literal_var m) R) ->
  (forall z, level_of a z = Some (current_level a) ->
    ~ In z (map literal_var learnt)) ->
  (forall (P : list Z) z dy,
    Forall (fun y => level_of a y = Some (current_level a)) P ->
    level_of a z = Some dy -> dy < current_level a -> ~ In z P) ->
  Forall (fun y => level_of a y = Some (current_level a)) S ->
  Forall (fun y => level_of a y = Some (current_level a)) R ->
  clause_false (assignment a) learnt ->
  entails_clause F
    (resolve_learnt a c S R learnt
       ++ map (fun y => literal_neg (view_lit a y))
              (resolve_S a x c S R learnt)).
Proof.
  intros F a S R learnt x c b Hent Hpre Hass Hentc Hinj Hsat Hcfacts
    Htags_iff HnotR HcurnotL Hlevel_notin HlevS HlevR HfalseL.
  intros rho Hmod.
    destruct (Hent rho Hmod) as [k [Hk Hkt]].
    apply in_app_or in Hk. destruct Hk as [HkL | HkS].
    - exists k. split; [|exact Hkt].
      apply in_or_app. left. unfold resolve_learnt.
      apply in_or_app. left. exact HkL.
    - rewrite in_map_iff in HkS. destruct HkS as [y [Hky HyS]].
      destruct (Z.eq_dec y x) as [-> | Hyx].
      + (* the pivot: resolve against the reason clause *)
        subst k.
        rewrite eval_literal_neg in Hkt. apply negb_true_iff in Hkt.
        rewrite (view_lit_assigned a x b Hass) in Hkt.
        destruct (Hentc rho Hmod) as [m [Hm Hmt]].
        destruct (Z.eq_dec (literal_var m) x) as [Hmx | Hmx].
        * (* the reason clause is satisfied at its pivot literal:
             contradiction with the resolvent's negated pivot *)
          exfalso.
          assert (Hme : m = satisfying_literal x b)
            by (exact (clause_var_injective_var_lit c x b m Hinj Hsat
                         Hm Hmx)).
          subst m. rewrite Hmt in Hkt. discriminate.
        * destruct (Hcfacts m Hm Hmx)
            as (b'' & dy & Hassy & Hshape & Hlevy & Hdy).
          destruct (Z.eq_dec dy 0) as [-> | Hdy0].
          -- (* level-0 side literal: permanently implied, dropped *)
             exfalso.
             destruct (Hpre _ _ Hassy Hlevy rho Hmod) as [k' [Hk' Hk't]].
             destruct Hk' as [Heq|[]]. subst k'.
             rewrite Hshape, <- literal_neg_satisfying,
               eval_literal_neg, Hk't in Hmt.
             discriminate.
          -- assert (Hmk : literal_neg (view_lit a (literal_var m)) = m).
             { rewrite (view_lit_assigned a (literal_var m) b'' Hassy),
                 literal_neg_satisfying. symmetry. exact Hshape. }
             destruct (Z.eq_dec dy (current_level a)) as [Heqc | Hnec].
             ++
                subst dy.
                destruct (zmem (literal_var m)
                            (analyze_tags S R learnt)) eqn:Hz.
                ** apply zmem_true_iff in Hz. apply Htags_iff in Hz.
                   destruct Hz as [HzS | [HzR | HzL]].
                   ---
                       exists m. split; [|exact Hmt].
                       apply in_or_app. right. rewrite <- Hmk.
                       apply (in_map
                                (fun y0 => literal_neg (view_lit a y0))).
                       unfold resolve_S. apply in_or_app. left.
                       apply In_zremove_iff. split; assumption.
                   --- (* already resolved: impossible by trail order *)
                       exfalso. exact (HnotR m Hm Hmx HzR).
                   ---
                       exfalso. exact (HcurnotL _ Hlevy HzL).
                ** exists m. split; [|exact Hmt].
                   apply in_or_app. right. rewrite <- Hmk.
                   apply (in_map (fun y0 => literal_neg (view_lit a y0))).
                   unfold resolve_S. apply in_or_app. right.
                   unfold resolve_new_S. apply filter_In. split.
                   --- apply in_map. apply filter_In.
                       split; [exact Hm|].
                       apply (proj2 (at_current_level_b_true_iff a m)).
                       exact Hlevy.
                   --- rewrite Hz. reflexivity.
             ++
                assert (Hdyc : dy < current_level a) by lia.
                destruct (zmem (literal_var m)
                            (analyze_tags S R learnt)) eqn:Hz.
                ** apply zmem_true_iff in Hz. apply Htags_iff in Hz.
                   destruct Hz as [HzS | [HzR | HzL]].
                   --- exfalso.
                       exact (Hlevel_notin S _ _ HlevS Hlevy Hdyc HzS).
                   --- exfalso.
                       exact (Hlevel_notin R _ _ HlevR Hlevy Hdyc HzR).
                   ---
                       rewrite in_map_iff in HzL.
                       destruct HzL as [k' [Hvk' Hk'in]].
                       pose proof (HfalseL k' Hk'in) as Hk'f.
                       destruct (eval_partial_false_shape _ _ Hk'f)
                         as [b3 [Hass3 Hshape3]].
                       rewrite Hvk' in Hass3, Hshape3.
                       assert (Hb3 : b3 = b'') by congruence.
                       subst b3.
                       assert (Hkm : k' = m) by congruence.
                       rewrite Hkm in Hk'in.
                       exists m. split; [|exact Hmt].
                       apply in_or_app. left. unfold resolve_learnt.
                       apply in_or_app. left. exact Hk'in.
                ** exists m. split; [|exact Hmt].
                   apply in_or_app. left. unfold resolve_learnt.
                   apply in_or_app. right. unfold resolve_new_lits.
                   apply filter_In. split; [exact Hm|].
                   apply andb_true_intro. split.
                   --- apply (proj2 (below_current_b_true_iff a m)).
                       exists dy. split; [exact Hlevy|lia].
                   --- rewrite Hz. reflexivity.
      +
        exists k. split; [|exact Hkt].
        apply in_or_app. right. rewrite <- Hky.
        apply (in_map (fun y0 => literal_neg (view_lit a y0))).
        unfold resolve_S. apply in_or_app. left.
        apply In_zremove_iff. split; assumption.
Qed.

Lemma analyze_resolve_tags_nodup :
  forall (a : cdcl_view) (S R : list Z) (learnt : clause)
    (x : Z) (c : clause),
  In x S ->
  NoDup S ->
  NoDup R ->
  NoDup (map literal_var learnt) ->
  NoDup (resolve_new_S a c (analyze_tags S R learnt)) ->
  NoDup (map literal_var (resolve_new_lits a c (analyze_tags S R learnt))) ->
  (forall z, In z S -> ~ In z (R ++ map literal_var learnt)) ->
  (forall z, In z R -> ~ In z (map literal_var learnt)) ->
  (forall z, zmem z (analyze_tags S R learnt) = false ->
    ~ In z S /\ ~ In z R /\ ~ In z (map literal_var learnt)) ->
  (forall y, In y (resolve_new_S a c (analyze_tags S R learnt)) ->
    exists m, In m c /\ literal_var m = y /\
      level_of a y = Some (current_level a) /\
      zmem y (analyze_tags S R learnt) = false) ->
  (forall z, In z (map literal_var
            (resolve_new_lits a c (analyze_tags S R learnt))) ->
    (exists dy, level_of a z = Some dy /\ 0 < dy < current_level a) /\
    zmem z (analyze_tags S R learnt) = false) ->
  NoDup (analyze_tags (resolve_S a x c S R learnt) (x :: R)
           (resolve_learnt a c S R learnt)).
Proof.
  intros a S R learnt x c HinS HndS HndR HndL HndnewSv HndnewL
    HdisS HdisRL Hfresh_notin HnewS_char HnewLvar_char.
  unfold analyze_tags at 1. unfold resolve_S, resolve_learnt.
    rewrite map_app.
    apply NoDup_app_intro.
    -
      apply NoDup_app_intro.
      + unfold zremove. apply NoDup_filter. exact HndS.
      + exact HndnewSv.
      + intros z Hz1 Hz2.
        apply In_zremove_iff in Hz1. destruct Hz1 as [Hz1 _].
        destruct (HnewS_char z Hz2) as [m [_ [_ [_ Hzf]]]].
        destruct (Hfresh_notin z Hzf) as (HnS & _ & _).
        exact (HnS Hz1).
    -
      apply NoDup_app_intro.
      + constructor.
        * intro HxR.
          exact (HdisS x HinS (in_or_app _ _ _ (or_introl HxR))).
        * exact HndR.
      + apply NoDup_app_intro.
        * exact HndL.
        * exact HndnewL.
        * intros z Hz1 Hz2.
          destruct (HnewLvar_char z Hz2) as (_ & Hzf).
          destruct (Hfresh_notin z Hzf) as (_ & _ & HnL).
          exact (HnL Hz1).
      + intros z Hz1 Hz2.
        apply in_app_or in Hz2.
        destruct Hz1 as [<- | Hz1].
        * destruct Hz2 as [Hz2 | Hz2].
          -- exact (HdisS x HinS (in_or_app _ _ _ (or_intror Hz2))).
          -- destruct (HnewLvar_char x Hz2) as (_ & Hzf).
             destruct (Hfresh_notin x Hzf) as (HnS & _ & _).
             exact (HnS HinS).
        * destruct Hz2 as [Hz2 | Hz2].
          -- exact (HdisRL z Hz1 Hz2).
          -- destruct (HnewLvar_char z Hz2) as (_ & Hzf).
             destruct (Hfresh_notin z Hzf) as (_ & HnR & _).
             exact (HnR Hz1).
    -
      intros z Hz1 Hz2.
      apply in_app_or in Hz1.
      assert (Hz2' : z = x \/ In z R \/ In z (map literal_var learnt) \/
        In z (map literal_var
                (resolve_new_lits a c (analyze_tags S R learnt)))).
      { apply in_app_or in Hz2. destruct Hz2 as [Hz2|Hz2].
        - destruct Hz2 as [->|Hz2];
            [left; reflexivity|right; left; exact Hz2].
        - apply in_app_or in Hz2.
          destruct Hz2 as [Hz2|Hz2];
            [right; right; left; exact Hz2|
             right; right; right; exact Hz2]. }
      destruct Hz1 as [Hz1 | Hz1].
      +
        apply In_zremove_iff in Hz1. destruct Hz1 as [HzS Hzx].
        destruct Hz2' as [-> | [HzR | [HzL | HzNew]]].
        * exact (Hzx eq_refl).
        * exact (HdisS z HzS (in_or_app _ _ _ (or_introl HzR))).
        * exact (HdisS z HzS (in_or_app _ _ _ (or_intror HzL))).
        * destruct (HnewLvar_char z HzNew) as (_ & Hzf).
          destruct (Hfresh_notin z Hzf) as (HnS & _ & _).
          exact (HnS HzS).
      +
        destruct (HnewS_char z Hz1) as [m [Hmc [Hvm [Hlevz Hzf]]]].
        destruct (Hfresh_notin z Hzf) as (HnS & HnR & HnL).
        destruct Hz2' as [-> | [HzR | [HzL | HzNew]]].
        * exact (HnS HinS).
        * exact (HnR HzR).
        * exact (HnL HzL).
        * (* both fresh: the level split separates them *)
          destruct (HnewLvar_char z HzNew) as ([dy [Hzdy Hdy']] & _).
          assert (dy = current_level a) by congruence. lia.
Qed.

(** The step hypothesis [Hscan] is the trail-scan fact: the C resolves
    the trail-latest tagged variable first, so
    when [x] is picked every other pending variable sits strictly below
    it in trail order.  It is what makes the ghost [tags] test and the C
    test agree: a side literal of [x]'s reason has rank strictly BELOW
    [x] ([reason_valid]), while every member of [R] has rank strictly
    ABOVE some [S] member -- in particular above [x] -- so the reason
    clause can never mention an [R] variable. *)
Lemma analyze_resolve_step :
  forall (F : cnf) (a : cdcl_view) (S R : list Z) (learnt : clause)
         (x : Z) (c : clause),
  closed_levels a ->
  (forall x' b, assignment a x' = Some b -> level_of a x' = Some 0 ->
     entails_clause F [satisfying_literal x' b]) ->
  analyze_inv F a S R learnt ->
  In x S ->
  reason_of a x = Some c ->
  reason_valid a x c ->
  entails_clause F c ->
  NoDup (map literal_var c) ->
  (forall s, In s S -> s <> x -> rank_lt a s x) ->
  analyze_inv F a (resolve_S a x c S R learnt) (x :: R)
              (resolve_learnt a c S R learnt).
Proof.
  intros F a S R learnt x c Hcl Hpre Hinv HinS Hreason Hrv Hentc Hndc
    Hscan.
  destruct Hcl as [_ [Hbound _]].
  destruct Hinv as (Hent & Hnd & HlevS & HassS & HlevR & HrankR & HlevL
                    & HfalseL).
  unfold analyze_tags in Hnd.
  assert (HndS : NoDup S)
    by (eapply NoDup_app_remove_r; exact Hnd).
  assert (HndRV : NoDup (R ++ map literal_var learnt))
    by (eapply NoDup_app_remove_l; exact Hnd).
  assert (HndR : NoDup R)
    by (eapply NoDup_app_remove_r; exact HndRV).
  assert (HndL : NoDup (map literal_var learnt))
    by (eapply NoDup_app_remove_l; exact HndRV).
  assert (HdisS : forall z, In z S ->
    ~ In z (R ++ map literal_var learnt))
    by (intros z Hz; eapply NoDup_app_disjoint; [exact Hnd|exact Hz]).
  assert (HdisRL : forall z, In z R -> ~ In z (map literal_var learnt))
    by (intros z Hz; eapply NoDup_app_disjoint; [exact HndRV|exact Hz]).
  assert (Htags_iff : forall z,
    In z (analyze_tags S R learnt) <->
    In z S \/ In z R \/ In z (map literal_var learnt)).
  { intros z. unfold analyze_tags. rewrite ! in_app_iff. tauto. }
  assert (Hfresh_notin : forall z,
    zmem z (analyze_tags S R learnt) = false ->
    ~ In z S /\ ~ In z R /\ ~ In z (map literal_var learnt)).
  { intros z Hz. apply zmem_false_iff in Hz.
    split; [|split]; intro Hc0; apply Hz; apply Htags_iff; tauto. }
  destruct Hrv as [b [d [rx [Hass [Hlev [Hrank [Hsat Hothers]]]]]]].
  assert (Hinj : clause_var_injective c)
    by (apply NoDup_map_var_injective; exact Hndc).
  assert (Hlevx : level_of a x = Some (current_level a))
    by (rewrite Forall_forall in HlevS; exact (HlevS x HinS)).
  assert (HnotR : forall m, In m c -> literal_var m <> x ->
    ~ In (literal_var m) R).
  { intros m Hm Hmx HinR.
    destruct (Hothers m Hm Hmx)
      as [_ [dy [ry [_ [Hranky [_ Hry]]]]]].
    rewrite Forall_forall in HrankR.
    destruct (HrankR _ HinR x HinS) as [r1 [r2 [Hr1 [Hr2 Hlt]]]].
    assert (Hr1x : r1 = rx) by congruence.
    assert (Hr2y : r2 = ry) by congruence.
    subst r1 r2. lia. }
  assert (HcurnotL : forall z,
    level_of a z = Some (current_level a) ->
    ~ In z (map literal_var learnt)).
  { intros z Hz HinL.
    rewrite in_map_iff in HinL. destruct HinL as [l' [Hvl' Hl'in]].
    rewrite Forall_forall in HlevL.
    destruct (HlevL l' Hl'in) as [d0 [Hld0 Hd0]].
    rewrite Hvl' in Hld0.
    assert (d0 = current_level a) by congruence. lia. }
  assert (Hlevel_notin : forall (P : list Z) z dy,
    Forall (fun y => level_of a y = Some (current_level a)) P ->
    level_of a z = Some dy -> dy < current_level a -> ~ In z P).
  { intros P z dy HP Hz Hdy HinP.
    rewrite Forall_forall in HP.
    pose proof (HP z HinP) as Hz'.
    assert (dy = current_level a) by congruence. lia. }
  assert (Hcfacts : forall m, In m c -> literal_var m <> x ->
    exists b'' dy, assignment a (literal_var m) = Some b'' /\
      m = falsified_literal (literal_var m) b'' /\
      level_of a (literal_var m) = Some dy /\
      0 <= dy <= current_level a).
  { intros m Hm Hmx.
    destruct (Hothers m Hm Hmx)
      as [Hmfalse [dy [ry [Hlevy [Hranky [Hdyd Hry]]]]]].
    destruct (eval_partial_false_shape _ _ Hmfalse)
      as [b'' [Hassy Hshape]].
    exists b'', dy. repeat split; try assumption.
    - exact (proj1 (Hbound _ _ _ Hassy Hlevy)).
    - exact (proj2 (Hbound _ _ _ Hassy Hlevy)). }
  assert (HnewS_char : forall y,
    In y (resolve_new_S a c (analyze_tags S R learnt)) ->
    exists m, In m c /\ literal_var m = y /\
      level_of a y = Some (current_level a) /\
      zmem y (analyze_tags S R learnt) = false).
  { intros y Hy. unfold resolve_new_S in Hy.
    apply filter_In in Hy. destruct Hy as [Hy Hz].
    apply negb_true_iff in Hz.
    rewrite in_map_iff in Hy. destruct Hy as [m [Hvm Hmf]].
    apply filter_In in Hmf. destruct Hmf as [Hmc Hb].
    apply at_current_level_b_true_iff in Hb. rewrite Hvm in Hb.
    exists m. repeat split; assumption. }
  assert (HnewS_side : forall y,
    In y (resolve_new_S a c (analyze_tags S R learnt)) ->
    exists m, In m c /\ literal_var m = y /\ literal_var m <> x).
  { intros y Hy.
    destruct (HnewS_char y Hy) as [m [Hmc [Hvm [_ Hzf]]]].
    destruct (Hfresh_notin y Hzf) as (HnS & _ & _).
    exists m. split; [exact Hmc|]. split; [exact Hvm|].
    intro Hmx. apply HnS. rewrite <- Hvm, Hmx. exact HinS. }
  assert (HnewL_char : forall l,
    In l (resolve_new_lits a c (analyze_tags S R learnt)) ->
    In l c /\ (exists dy, level_of a (literal_var l) = Some dy /\
                          0 < dy < current_level a) /\
    zmem (literal_var l) (analyze_tags S R learnt) = false).
  { intros l Hl. unfold resolve_new_lits in Hl.
    apply filter_In in Hl. destruct Hl as [Hlc Hb].
    apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
    apply negb_true_iff in Hb2.
    apply below_current_b_true_iff in Hb1.
    split; [ | split ]; assumption. }
  assert (HnewLvar_char : forall z,
    In z (map literal_var
            (resolve_new_lits a c (analyze_tags S R learnt))) ->
    (exists dy, level_of a z = Some dy /\ 0 < dy < current_level a) /\
    zmem z (analyze_tags S R learnt) = false).
  { intros z Hz. rewrite in_map_iff in Hz.
    destruct Hz as [l [Hvl Hl]]. subst z.
    destruct (HnewL_char l Hl) as (_ & Hlev' & Hzm).
    split; assumption. }
  assert (E1 : entails_clause F
    (resolve_learnt a c S R learnt
       ++ map (fun y => literal_neg (view_lit a y))
              (resolve_S a x c S R learnt)))
    by (eapply analyze_resolve_entails; eassumption).
  assert (HndnewSv : NoDup (resolve_new_S a c (analyze_tags S R learnt)))
    by (unfold resolve_new_S; apply NoDup_filter;
        apply NoDup_map_filter; exact Hndc).
  assert (HndnewL : NoDup
      (map literal_var (resolve_new_lits a c (analyze_tags S R learnt))))
    by (unfold resolve_new_lits; apply NoDup_map_filter; exact Hndc).
  assert (E2 : NoDup (analyze_tags (resolve_S a x c S R learnt) (x :: R)
                        (resolve_learnt a c S R learnt)))
    by (apply analyze_resolve_tags_nodup; assumption).
  assert (E3 : Forall (fun y => level_of a y = Some (current_level a))
                 (resolve_S a x c S R learnt)).
  { rewrite Forall_forall. intros z Hz. unfold resolve_S in Hz.
    apply in_app_or in Hz. destruct Hz as [Hz|Hz].
    - apply In_zremove_iff in Hz. destruct Hz as [Hz _].
      rewrite Forall_forall in HlevS. exact (HlevS z Hz).
    - destruct (HnewS_char z Hz) as [m [_ [_ [Hlev' _]]]]. exact Hlev'. }
  assert (E4 : Forall (fun y => exists b0, assignment a y = Some b0)
                 (resolve_S a x c S R learnt)).
  { rewrite Forall_forall. intros z Hz. unfold resolve_S in Hz.
    apply in_app_or in Hz. destruct Hz as [Hz|Hz].
    - apply In_zremove_iff in Hz. destruct Hz as [Hz _].
      rewrite Forall_forall in HassS. exact (HassS z Hz).
    - destruct (HnewS_side z Hz) as [m [Hmc [Hvm Hmx]]].
      destruct (Hcfacts m Hmc Hmx) as (b'' & dy & Hassy & _).
      exists b''. rewrite <- Hvm. exact Hassy. }
  assert (E5 : Forall (fun y => level_of a y = Some (current_level a))
                 (x :: R))
    by (constructor; [exact Hlevx | exact HlevR]).
  assert (E6 : Forall (fun r => forall s,
                 In s (resolve_S a x c S R learnt) -> rank_lt a s r)
                 (x :: R)).
  { constructor.
    - (* the fresh member [x] *)
      intros s Hs. unfold resolve_S in Hs.
      apply in_app_or in Hs. destruct Hs as [Hs|Hs].
      + apply In_zremove_iff in Hs. destruct Hs as [HsS Hsx].
        exact (Hscan s HsS Hsx).
      + destruct (HnewS_side s Hs) as [m [Hmc [Hvm Hmx]]].
        destruct (Hothers m Hmc Hmx)
          as [_ [dy [ry [_ [Hranky [_ Hry]]]]]].
        unfold rank_lt. rewrite <- Hvm.
        exists ry, rx.
        split; [exact Hranky | split; [exact Hrank | exact Hry]].
    - (* the old members of R, by transitivity through [x] *)
      rewrite Forall_forall. intros r HrR s Hs.
      rewrite Forall_forall in HrankR.
      unfold resolve_S in Hs. apply in_app_or in Hs.
      destruct Hs as [Hs|Hs].
      + apply In_zremove_iff in Hs. destruct Hs as [HsS _].
        exact (HrankR r HrR s HsS).
      + destruct (HnewS_side s Hs) as [m [Hmc [Hvm Hmx]]].
        destruct (Hothers m Hmc Hmx)
          as [_ [dy [ry [_ [Hranky [_ Hry]]]]]].
        destruct (HrankR r HrR x HinS) as [r1 [r2 [Hr1 [Hr2 Hlt]]]].
        assert (Hr1x : r1 = rx) by congruence. subst r1.
        unfold rank_lt. rewrite <- Hvm.
        exists ry, r2.
        split; [exact Hranky | split; [exact Hr2 | lia]]. }
  assert (E7 : Forall (fun l => exists d0,
                 level_of a (literal_var l) = Some d0 /\
                 0 < d0 < current_level a)
                 (resolve_learnt a c S R learnt)).
  { rewrite Forall_forall. intros l Hl. unfold resolve_learnt in Hl.
    apply in_app_or in Hl. destruct Hl as [Hl|Hl].
    - rewrite Forall_forall in HlevL. exact (HlevL l Hl).
    - destruct (HnewL_char l Hl) as (_ & Hlev' & _). exact Hlev'. }
  assert (E8 : clause_false (assignment a)
                 (resolve_learnt a c S R learnt)).
  { intros l Hl. unfold resolve_learnt in Hl.
    apply in_app_or in Hl. destruct Hl as [Hl|Hl].
    - exact (HfalseL l Hl).
    - destruct (HnewL_char l Hl) as (Hlc & [d0 [Hld0 Hd0]] & _).
      assert (Hlx : literal_var l <> x).
      { intro Hc0. rewrite Hc0 in Hld0.
        rewrite Hlevx in Hld0. injection Hld0 as Heq0. lia. }
      destruct (Hothers l Hlc Hlx) as [Hlf _]. exact Hlf. }
  exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj E7
          E8))))))).
Qed.

(** ----- the exit certificate ----- *)

(** When the pending set has shrunk to the single first-UIP variable,
    the resolvent is the learned clause and it satisfies the exit
    certificate: sound, variable-distinct (the invariant's
    tag-set [NoDup] hands it over), all-false, head at the current level,
    tail strictly below.  The resolved set [R] merely passes through. *)
Lemma analyze_exit : forall (F : cnf) (a : cdcl_view) (uip : Z)
                            (R : list Z) (learnt : clause),
  analyze_inv F a [uip] R learnt ->
  uip_exit_cert F a (literal_neg (view_lit a uip) :: learnt).
Proof.
  intros F a uip R learnt Hinv.
  destruct Hinv as (Hent & Hnd & HlevS & HassS & _ & _ & HlevL &
                    HfalseL).
  assert (Hlevu : level_of a uip = Some (current_level a))
    by (exact (Forall_inv HlevS)).
  destruct (Forall_inv HassS) as [b Hassu].
  unfold analyze_tags in Hnd. cbn [app] in Hnd.
  split; [|split].
  - split.
    +
      apply entails_clause_perm
        with (c := learnt ++ [literal_neg (view_lit a uip)]).
      * apply Permutation_sym. apply Permutation_cons_append.
      * cbn [map] in Hent. exact Hent.
    +
      intros l Hl. destruct Hl as [Heq | Hl].
      * subst l. exact (neg_view_lit_false a uip b Hassu).
      * exact (HfalseL l Hl).
  -
    cbn [map]. rewrite literal_var_neg, view_lit_var.
    inversion Hnd as [|? ? Hnotin Hnd']; subst.
    constructor.
    + intro Hc0. apply Hnotin. apply in_or_app. right. exact Hc0.
    + eapply NoDup_app_remove_l. exact Hnd'.
  - exists (literal_neg (view_lit a uip)), learnt.
    split; [reflexivity|]. split.
    + rewrite literal_var_neg, view_lit_var. exact Hlevu.
    + eapply Forall_impl; [|exact HlevL].
      intros k [dk [Hldk Hdk]]. exists dk. split; [exact Hldk|lia].
Qed.

(** ----- variable-distinctness suppliers for reason clauses ----- *)

Lemma obj_wf_nodup_vars : forall (n : Z) (co : clause_obj),
  obj_wf n co -> NoDup (map literal_var (denote_obj co)).
Proof.
  intros n co Hwf. destruct Hwf as (_ & _ & Hnd).
  unfold denote_obj. apply lits_denote_nodup_vars. exact Hnd.
Qed.

Lemma tagged_reason_nodup_vars : forall q p : Z,
  lit_var_c q <> lit_var_c p ->
  NoDup (map literal_var [lit_denote q; literal_neg (lit_denote p)]).
Proof.
  intros q p Hne. cbn [map].
  rewrite literal_var_neg, ! lit_var_c_denote.
  constructor.
  - intros [He|[]]. apply Hne. symmetry. exact He.
  - constructor; [intros []|constructor].
Qed.

(** ----- conflict-clause minimization ----- *)

(** [T] is a valid redundancy witness set with respect to the seen set
    [S0] (analyze's tagged variables): every member has a reason clause
    all of whose side literals are level-0, seen, or again in [T]. *)
Definition removable_witness
    (a : cdcl_view) (S0 T : list Z) : Prop :=
  forall x, In x T -> exists c, reason_of a x = Some c /\
    (forall l, In l c -> literal_var l <> x ->
       level_of a (literal_var l) = Some 0 \/
       In (literal_var l) S0 \/ In (literal_var l) T).

(** Every variable contributed by a successful removability DFS is assigned
    strictly below the current decision level, with a concrete trail rank.
    Keeping the level and rank together is what lets a later minimization step
    shrink the DFS base from the whole tag set to its still-live learnt suffix. *)
Definition assigned_below_current (a : cdcl_view) (x : Z) : Prop :=
  exists d r,
    level_of a x = Some d /\
    assignment_rank a x = Some r /\
    d < current_level a.

(** The well-founded core: under any model of [F] that falsifies every
    kept literal, the trail literal of every level-0 / seen-but-kept /
    witnessed variable is true.  Strong induction on [assignment_rank];
    the rank strictly decreases through [reason_valid]'s side literals
    (TAG-IMPLIED). *)
Lemma removable_trail_lit_true :
  forall (F : cnf) (a : cdcl_view) (S0 T : list Z) (kept : clause),
  grounded_at a ->
  (forall x b, assignment a x = Some b -> level_of a x = Some 0 ->
     entails_clause F [satisfying_literal x b]) ->
  (forall x b, In x S0 -> ~ In x T -> assignment a x = Some b ->
     entails_clause (cnf_with_units F (map literal_neg kept))
       [satisfying_literal x b]) ->
  removable_witness a S0 T ->
  (forall x c, In x T -> reason_of a x = Some c ->
     entails_clause F c) ->
  (forall x c, In x T -> reason_of a x = Some c ->
     NoDup (map literal_var c)) ->
  forall (r : nat) (x : Z) (b : bool) (rho : valuation),
    (level_of a x = Some 0 \/ (In x S0 /\ ~ In x T) \/ In x T) ->
    assignment a x = Some b ->
    assignment_rank a x = Some r ->
    models rho F ->
    (forall k, In k kept -> eval_literal rho k = false) ->
    eval_literal rho (satisfying_literal x b) = true.
Proof.
  intros F a S0 T kept Hg Hpre HS0 Hw HTe HTi r.
  induction r using lt_wf_ind.
  rename H into IH.
  intros x b rho Hscope Hass Hrank Hmod Hkf.
  destruct Hscope as [Hlev0 | [[HinS0 HnotT] | HinT]].
  - (* level 0: directly F-entailed *)
    destruct (Hpre x b Hass Hlev0 rho Hmod) as [k [Hk Hkt]].
    destruct Hk as [Heq|[]]. subst k. exact Hkt.
  -
    assert (Hmu : models rho (cnf_with_units F (map literal_neg kept))).
    { apply models_clause_units_intro; [exact Hmod|].
      rewrite Forall_forall. intros k' Hk'.
      rewrite in_map_iff in Hk'. destruct Hk' as [k0 [Hk0eq Hk0]].
      subst k'. rewrite eval_literal_neg. rewrite (Hkf k0 Hk0).
      reflexivity. }
    destruct (HS0 x b HinS0 HnotT Hass rho Hmu) as [k [Hk Hkt]].
    destruct Hk as [Heq|[]]. subst k. exact Hkt.
  - (* witnessed: recurse through the reason clause *)
    destruct (Hw x HinT) as [c [Hreason Hants]].
    destruct (Hg x b Hass) as [d [rx [Hlev [Hrank' Horigin]]]].
    destruct Horigin as [Hnone | [c' [Hreason' Hrv]]].
    + rewrite Hnone in Hreason. discriminate.
    + assert (Hcc : c' = c) by congruence. subst c'.
      destruct Hrv
        as [b' [d' [rx' [Hass' [Hlev' [Hrank'' [Hsat Hothers]]]]]]].
      assert (Hbb : b' = b) by congruence. subst b'.
      assert (Hrr : rx' = r) by congruence. subst rx'.
      destruct (HTe x c HinT Hreason rho Hmod) as [m [Hm Hmt]].
      destruct (Z.eq_dec (literal_var m) x) as [Hmx|Hmx].
      * (* the model satisfies the reason at the propagated literal *)
        assert (Hinj : clause_var_injective c)
          by (apply NoDup_map_var_injective;
              exact (HTi x c HinT Hreason)).
        assert (Hme : m = satisfying_literal x b)
          by (exact (clause_var_injective_var_lit c x b m Hinj Hsat
                       Hm Hmx)).
        subst m. exact Hmt.
      * (* a side literal: its variable has strictly smaller rank *)
        destruct (Hothers m Hm Hmx)
          as [Hmfalse [dy [ry [Hlevy [Hranky [Hdyd Hry]]]]]].
        destruct (eval_partial_false_shape _ _ Hmfalse)
          as [b'' [Hassy Hshape]].
        assert (Hscope' : level_of a (literal_var m) = Some 0 \/
                (In (literal_var m) S0 /\ ~ In (literal_var m) T) \/
                In (literal_var m) T).
        { destruct (Hants m Hm Hmx) as [Hh|[Hh|Hh]].
          - left; exact Hh.
          - destruct (List.in_dec Z.eq_dec (literal_var m) T)
              as [Hyt|Hyt].
            + right; right; exact Hyt.
            + right; left; split; assumption.
          - right; right; exact Hh. }
        pose proof (IH ry Hry (literal_var m) b'' rho Hscope' Hassy
                      Hranky Hmod Hkf) as Hsy.
        exfalso.
        rewrite Hshape, <- literal_neg_satisfying, eval_literal_neg,
          Hsy in Hmt.
        discriminate.
Qed.

(** Removing the [T]-witnessed literals from an entailed, all-false
    learned clause preserves [F]-entailment, which justifies the C
    compaction in [solver_analyze].

    USAGE (the non-obvious instantiation): instantiate
    [S0 := map literal_var kept], NOT the whole
    C [tags] set -- with the full tag set the TAG-IMPLIED hypothesis is
    circular.  Two-stage discharge: (i) for [x] a variable of [kept] the
    TAG-IMPLIED hypothesis is trivial ([satisfying_literal x b] is the
    negation of a kept literal, so it is one of the added units);
    (ii) [removable_witness a (map literal_var kept) T] follows from the
    DFS witness because every [T]-variable sits strictly below the
    current level, so a tagged antecedent can only be a learnt-clause
    variable -- kept (hence in [S0]) or removed (hence in [T]) -- and
    never a resolved current-level variable.  The C's per-literal
    rollback in [solver_lit_removable] restores [tags] to [top] on
    a failed call and contributes nothing to [T]; only successful calls
    grow [T]. *)
Lemma minimization_sound :
  forall (F : cnf) (a : cdcl_view) (S0 T : list Z)
         (learnt kept removed : clause),
  grounded_at a ->
  (forall x b, assignment a x = Some b -> level_of a x = Some 0 ->
     entails_clause F [satisfying_literal x b]) ->
  (forall x b, In x S0 -> ~ In x T -> assignment a x = Some b ->
     entails_clause (cnf_with_units F (map literal_neg kept))
       [satisfying_literal x b]) ->
  removable_witness a S0 T ->
  (forall x c, In x T -> reason_of a x = Some c ->
     entails_clause F c) ->
  (forall x c, In x T -> reason_of a x = Some c ->
     NoDup (map literal_var c)) ->
  Permutation learnt (kept ++ removed) ->
  Forall (fun l => In (literal_var l) T) removed ->
  clause_false (assignment a) learnt ->
  entails_clause F learnt ->
  entails_clause F kept.
Proof.
  intros F a S0 T learnt kept removed
    Hg Hpre HS0 Hw HTe HTi Hperm Hrem Hfalse Hent rho Hmod.
  destruct (existsb (fun k => eval_literal rho k) kept) eqn:Hex.
  -
    apply existsb_exists in Hex. destruct Hex as [k [Hk Hkt]].
    exists k. split; assumption.
  - (* all kept literals false: the witnessed removed literals cannot
       carry the entailment either -- contradiction *)
    assert (Hkf : forall k, In k kept -> eval_literal rho k = false).
    { intros k Hk. destruct (eval_literal rho k) eqn:E; [|reflexivity].
      exfalso.
      assert (Hex' : existsb (fun k0 => eval_literal rho k0) kept
                     = true).
      { apply existsb_exists. exists k. split; assumption. }
      congruence. }
    destruct (Hent rho Hmod) as [l [Hl Hlt]].
    pose proof (Permutation_in _ Hperm Hl) as Hl'.
    apply in_app_or in Hl'. destruct Hl' as [Hlk | Hlr].
    + exists l. split; assumption.
    + exfalso.
      rewrite Forall_forall in Hrem.
      pose proof (Hrem l Hlr) as HxT.
      pose proof (Hfalse l Hl) as Hlf.
      destruct (eval_partial_false_shape _ _ Hlf) as [b [Hass Hshape]].
      destruct (Hg _ _ Hass) as [d [rx [Hlev [Hrank _]]]].
      pose proof (removable_trail_lit_true F a S0 T kept Hg Hpre HS0
                    Hw HTe HTi rx (literal_var l) b rho
                    (or_intror (or_intror HxT)) Hass Hrank Hmod Hkf)
        as Hst.
      rewrite Hshape, <- literal_neg_satisfying, eval_literal_neg,
        Hst in Hlt.
      discriminate.
Qed.

(** ----- the lit_removable DFS invariant ----- *)

(** Mid-run shape of [solver_lit_removable]'s iterative DFS: [dn] holds
    the expanded variables, [stk] the pending ones; every expanded
    variable's reason has all its side variables level-0, seen, expanded,
    or still pending. *)
Definition dfs_witness
    (a : cdcl_view) (S0 dn stk : list Z) : Prop :=
  forall x, In x dn -> exists c, reason_of a x = Some c /\
    (forall l, In l c -> literal_var l <> x ->
       level_of a (literal_var l) = Some 0 \/
       In (literal_var l) S0 \/
       In (literal_var l) dn \/ In (literal_var l) stk).

Lemma dfs_witness_extend :
  forall (a : cdcl_view) (S0 dn stk stk' : list Z) (v : Z) (c : clause),
  dfs_witness a S0 dn (v :: stk) ->
  reason_of a v = Some c ->
  (forall l, In l c -> literal_var l <> v ->
     level_of a (literal_var l) = Some 0 \/
     In (literal_var l) S0 \/
     In (literal_var l) (v :: dn) \/ In (literal_var l) stk') ->
  incl stk stk' ->
  dfs_witness a S0 (v :: dn) stk'.
Proof.
  intros a S0 dn stk stk' v c Hdfs Hr Hc Hincl x Hx.
  destruct Hx as [<- | Hx].
  - exists c. split; [exact Hr|]. exact Hc.
  - destruct (Hdfs x Hx) as [c' [Hr' Hc']].
    exists c'. split; [exact Hr'|].
    intros l Hl Hvl.
    destruct (Hc' l Hl Hvl) as [H|[H|[H|H]]].
    + left; exact H.
    + right; left; exact H.
    + right; right; left; right; exact H.
    + destruct H as [Heq | H].
      * right; right; left; left; exact Heq.
      * right; right; right; apply Hincl; exact H.
Qed.

Lemma dfs_witness_complete :
  forall (a : cdcl_view) (S0 dn : list Z),
  dfs_witness a S0 dn [] -> removable_witness a S0 dn.
Proof.
  intros a S0 dn H x Hx.
  destruct (H x Hx) as [c [Hr Hc]].
  exists c. split; [exact Hr|].
  intros l Hl Hvl.
  destruct (Hc l Hl Hvl) as [Hh|[Hh|[Hh|Hh]]].
  - left; exact Hh.
  - right; left; exact Hh.
  - right; right; exact Hh.
  - destruct Hh.
Qed.

