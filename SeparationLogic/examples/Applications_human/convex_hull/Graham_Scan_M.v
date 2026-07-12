(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From SimpleC.EE.Applications_human.convex_hull Require Import
  Geo_Point_Primitives Convexity Maximality Graham_Scan.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad StateRelHoare FixpointLib.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic StateRelMonad StateRelHoare FixpointLib.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
(* /COQ-HEAD *)

Fixpoint iter
           {A B: Type}
           (f: A -> B -> program (list A) B)
           (l: list A)
           (b: B): program (list A) B :=
  match l with
  | nil => ret b
  | a :: l0 =>
    b0 <- f a b ;;
    iter f l0 b0
  end.


(** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) **)
Definition pop_fun (p: point) : program (list point) (CntOrBrk unit unit) :=
  T <- get' id ;;
  match T with
  | t :: s :: T' =>
      choice
        (assume!! (ccw s t p) ;;
         ret (by_break tt))
        (assume!! (~ ccw s t p) ;;
         update' (fun _ => s :: T') ;;
         ret (by_continue tt))
  (* Less than 2 elements in stack: break out of the loop *)
  | _ =>
      ret (by_break tt)
  end.
  
(** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) { pop(&T); }; push(p);  **)
Definition step_fun (p : point) : program (list point) unit :=
  repeat_break (fun _ => pop_fun p) tt ;;
  T <- get' id ;;
  update' (fun _ => p :: T).

Definition step_p (p: point) (_: unit) : program (list point) unit :=
  step_fun p.

Definition build_hull (p: point) (l: list point) : program (list point) unit :=
  update' (fun _ => (p :: nil)) ;;
  iter step_p l tt.


Lemma pop_fun_preserves_graham_scan_inc : forall p T0,
  Hoare
    (fun T => graham_scan_inc p T0 = graham_scan_inc p T)
    (pop_fun p)
    (fun x T =>
       match x with
       | by_continue _ => graham_scan_inc p T0 = graham_scan_inc p T
       | by_break _ => graham_scan_inc p T0 = p :: T
       end).
Proof.
  intros p T0.
  unfold pop_fun.
  intro_state.
  destruct s0 as [| t [| s T]]; simpl in *.
  - hoare_auto_s; subst; simpl in *.
    apply Hoare_ret'; intros T' ->.
    exact H.
  - hoare_auto_s; subst; simpl in *.
    apply Hoare_ret'; intros T' ->.
    exact H.
  - destruct (ccw_dec s t p) as [Hccw | Hnccw].
    + hoare_auto_s; subst; simpl.
      apply Hoare_choice.
      * apply Hoare_assume_bind'. intros _.
        apply Hoare_ret'. intros T' ->.
        exact H.
      * apply Hoare_assume_bind'. intros Hbad.
        contradiction.
    + hoare_auto_s; subst; simpl.
      apply Hoare_choice.
      * apply Hoare_assume_bind'. intros Hbad.
        contradiction.
      * apply Hoare_assume_bind'. intros _.
        eapply Hoare_bind.
        -- apply Hoare_update'.
        -- intros [].
           apply Hoare_ret'. intros T' ->.
           exact H.
Qed.

Lemma repeat_pop_fun_correct : forall p T0,
  Hoare
    (fun T => T = T0)
    (repeat_break (fun _ : unit => pop_fun p) tt)
    (fun _ T => graham_scan_inc p T0 = p :: T).
Proof.
  intros p T0.
  eapply Hoare_conseq_pre.
  2: {
    eapply (@Hoare_repeat_break (list point) unit unit
      (fun _ : unit => pop_fun p)
      (fun _ T => graham_scan_inc p T0 = graham_scan_inc p T)
      (fun _ T => graham_scan_inc p T0 = p :: T)).
    intros [].
    apply pop_fun_preserves_graham_scan_inc.
  }
  simpl.
  intros T ->.
  reflexivity.
Qed.

Lemma step_fun_correct : forall p T0,
  Hoare
    (fun T => T = T0)
    (step_fun p)
    (fun _ T => T = graham_scan_inc p T0).
Proof.
  intros p T0.
  unfold step_fun.
  eapply Hoare_bind.
  - apply repeat_pop_fun_correct.
  - intros [].
    eapply Hoare_bind.
    + eapply Hoare_get.
    + intros T.
      eapply Hoare_conseq_post.
      2: eapply Hoare_update.
      simpl.
      intros [] T' [Told [HT' [HTold Hpre]]].
      subst T' T.
      symmetry.
      exact Hpre.
Qed.

Lemma iter_step_p_correct : forall l T0,
  Hoare
    (fun T => T = T0)
    (iter step_p l tt)
    (fun _ T => T = fold_left (fun T p => graham_scan_inc p T) l T0).
Proof.
  induction l as [| p l IH]; intros T0; simpl.
  - apply Hoare_ret'.
    intros T ->.
    reflexivity.
  - eapply Hoare_bind.
    + unfold step_p.
      apply step_fun_correct.
    + intros [].
      apply IH.
Qed.

Lemma build_hull_stack_correct : forall p l,
  Hoare
    (fun T => T = [])
    (build_hull p l)
    (fun _ T => T = fold_left (fun T p => graham_scan_inc p T) l [p]).
Proof.
  intros p l.
  unfold build_hull.
  eapply Hoare_bind.
  - eapply Hoare_update'.
  - intros [].
    eapply Hoare_conseq_pre.
    2: apply iter_step_p_correct.
    simpl.
    intros T ->.
    reflexivity.
Qed.

Theorem build_hull_hoare_final : forall p l,
  Hoare (fun T0 => T0 = [])
        (build_hull p l)
        (fun _ T' => T' = graham_scan (rev (p :: l))).
Proof.
  intros p l.
  eapply Hoare_conseq_post.
  2: apply build_hull_stack_correct.
  intros [] T HT.
  rewrite HT.
  apply fold_left_graham_scan_inc_cons.
Qed.








Lemma gs_sort_graham_scan : forall p l,
  sort p l ->
  sort p (graham_scan l).
Proof.
  intros p l Hsort.
  assert (Hsort_copy : sort p l) by exact Hsort.
  destruct Hsort as [Hleft Hrev].
  split.
  - unfold leftmost in *.
    rewrite Forall_forall in *.
    intros q Hq.
    apply Hleft.
    eapply graham_scan_subset.
    + exact Hsort_copy.
    + exact Hq.
  - apply sort_gs_g_rev_ccw_list.
    split; [exact Hleft | exact Hrev].
Qed.

Lemma gs_graham_scan_inc_nonempty : forall a T,
  graham_scan_inc a T <> [].
Proof.
  intros a T.
  induction T as [| b T IH]; simpl; try discriminate.
  destruct T as [| c T']; simpl; try discriminate.
  destruct (ccw_dec c b a); [discriminate |].
  exact IH.
Qed.

Lemma gs_graham_scan_nonempty : forall l,
  l <> [] ->
  graham_scan l <> [].
Proof.
  intros l Hne.
  destruct l as [| a l]; [contradiction |].
  simpl.
  apply gs_graham_scan_inc_nonempty.
Qed.




















Lemma gs_cleanup_closed_stack : forall p a C L,
  sort p (a :: C) ->
  rev_consec_ccw C ->
  first_anchor_strict p (rev C) ->
  is_max_hull' p (a :: C) (a :: L) ->
  (forall q, In q C -> In q L) ->
  exists C',
    graham_scan_inc a (C ++ [p]) = C' ++ [p] /\
    sort p C' /\
    rev_consec_ccw C' /\
    first_anchor_strict p (rev C') /\
    is_max_hull' p C' (a :: L) /\
    (forall q, In q C' -> In q (a :: L)).
Proof.
  intros p a C.
  induction C as [| b C IH]; intros L Hsort Hcon Hanchor Hmax Hsub.
  - simpl.
    exists [a].
    split; [reflexivity |].
    split; [exact Hsort |].
    split; [simpl; tauto |].
    split; [simpl; exact I |].
    split; [exact Hmax |].
    intros q [Hq | []].
    subst q; simpl; tauto.
  - destruct C as [| c C'].
    + simpl.
      destruct (ccw_dec p b a) as [Hccw | Hnccw].
      * exists [a; b].
        split; [reflexivity |].
        split; [exact Hsort |].
        split; [simpl; tauto |].
        split.
        -- simpl.
           exact Hccw.
        -- split; [exact Hmax |].
           intros q Hq.
           simpl in Hq |- *.
           destruct Hq as [Hq | [Hq | []]]; subst.
           ++ tauto.
           ++ right. apply Hsub. simpl. tauto.
      * exists [a].
        destruct Hsort as [Hleft Hweak].
        assert (Hsort_a : sort p [a]).
        {
          split.
          - unfold leftmost in *.
            rewrite Forall_cons_iff in *.
            destruct Hleft as [Ha _].
            split; [exact Ha | apply Forall_nil].
          - simpl.
            split; [apply Forall_nil | exact I].
        }
        split; [reflexivity |].
        split; [exact Hsort_a |].
        split; [simpl; tauto |].
        split; [simpl; exact I |].
        split.
        -- unfold is_max_hull' in *.
           rewrite Forall_forall in *.
           intros q Hq.
           destruct Hweak as [Hab _].
           rewrite Forall_g_rev_ccw_cons_iff in Hab.
           destruct Hab as [Hab _].
           eapply gs_point_in_hull_pop_single.
           ++ exact Hab.
           ++ exact Hnccw.
           ++ apply Hmax.
              exact Hq.
        -- intros q Hq.
           simpl in Hq |- *.
           destruct Hq as [Hq | []].
           subst q; tauto.
    + simpl.
      destruct (ccw_dec c b a) as [Hccw | Hnccw].
      * exists (a :: b :: c :: C').
        split; [reflexivity |].
        split; [exact Hsort |].
        split.
        -- simpl.
           split.
           ++ apply ccw_cyclicity.
              exact Hccw.
           ++ exact Hcon.
        -- split.
           ++ simpl in Hanchor |- *.
              remember (rev C') as R.
              destruct R as [| x [| y R]]; simpl in *; exact Hanchor.
           ++ split; [exact Hmax |].
              intros q Hq.
              simpl in Hq |- *.
              destruct Hq as [Hq | Hq]; subst.
              ** tauto.
              ** right. apply Hsub. simpl. exact Hq.
      * assert (Hsort_tail : sort p (a :: c :: C')).
        {
          apply gs_sort_tail_from_cons with (b := b).
          exact Hsort.
        }
        assert (Hcon_tail : rev_consec_ccw (c :: C')).
        {
          apply gs_rev_consec_ccw_tail with (b := b).
          exact Hcon.
        }
        assert (Hanchor_tail : first_anchor_strict p (rev (c :: C'))).
        {
          apply gs_first_anchor_tail with (b := b).
          exact Hanchor.
        }
        assert (Hmax_tail : is_max_hull' p (a :: c :: C') (a :: L)).
        {
          eapply is_max_hull'_pop'_g.
          - destruct Hsort as [_ Hweak].
            exact Hweak.
          - exact Hnccw.
          - exact Hmax.
        }
        assert (Hsub_tail : forall q, In q (c :: C') -> In q L).
        {
          intros q Hq.
          apply Hsub.
          simpl.
          right.
          exact Hq.
        }
        specialize (IH L Hsort_tail Hcon_tail Hanchor_tail Hmax_tail Hsub_tail)
          as [Cfinal [Hscan [Hsort_final [Hcon_final [Hanchor_final [Hmax_final Hsub_final]]]]]].
        exists Cfinal.
        split.
        -- simpl.
           destruct (ccw_dec c b a) as [Hbad | _].
           ++ contradiction.
           ++ exact Hscan.
        -- split; [exact Hsort_final |].
           split; [exact Hcon_final |].
           split; [exact Hanchor_final |].
           split; [exact Hmax_final |].
           exact Hsub_final.
Qed.

Lemma gs_closed_scan_fold_spec : forall p W,
  sort p W ->
  exists C,
    fold_left (fun T q => graham_scan_inc q T) (rev W) [p] = C ++ [p] /\
    sort p C /\
    rev_consec_ccw C /\
    first_anchor_strict p (rev C) /\
    is_max_hull' p C W /\
    (forall q, In q C -> In q W) /\
    (W <> [] -> C <> []).
Proof.
  intros p W.
  induction W as [| a W IH]; intros Hsort.
  - exists [].
    simpl.
    split; [reflexivity |].
    split.
    + split.
      * unfold leftmost.
        apply Forall_nil.
      * exact I.
    + split; [exact I |].
      split; [exact I |].
      split.
      * unfold is_max_hull'.
        apply Forall_nil.
      * split.
        -- intros q Hq.
           contradiction.
        -- intros Hbad.
           contradiction Hbad.
           reflexivity.
  - assert (Hsort_W : sort p W).
    {
      apply (sort_ind p [a] W).
      exact Hsort.
    }
    specialize (IH Hsort_W)
      as [C [Hfold [Hsort_C [Hcon_C [Hanchor_C [Hmax_C [Hsub_C Hnonempty_C]]]]]]].
    simpl rev.
    rewrite fold_left_app.
    simpl.
    rewrite Hfold.
    assert (Hsort_aC : sort p (a :: C)).
    {
      eapply gs_sort_cons_subset; eauto.
    }
    assert (Hpush : is_max_hull' p (a :: C) (a :: W)).
    {
      apply gs_is_max_hull'_push.
      - destruct Hsort_aC as [_ Hweak].
        exact Hweak.
      - intros HCnil.
        destruct W as [| w W']; [reflexivity |].
        exfalso.
        apply (Hnonempty_C ltac:(discriminate)).
        exact HCnil.
      - exact Hmax_C.
    }
	    destruct (gs_cleanup_closed_stack p a C W Hsort_aC Hcon_C Hanchor_C Hpush Hsub_C)
	      as [C' [Hscan [Hsort_C' [Hcon_C' [Hanchor_C' [Hmax_C' Hsub_C']]]]]].
	    exists C'.
	    split.
	    + rewrite Hscan.
	      reflexivity.
	    + split; [exact Hsort_C' |].
	      split; [exact Hcon_C' |].
	      split; [exact Hanchor_C' |].
	      split; [exact Hmax_C' |].
	      split; [exact Hsub_C' |].
	      intros _.
	      destruct C' as [| x C'']; [| discriminate].
	      unfold is_max_hull' in Hmax_C'.
	      rewrite Forall_cons_iff in Hmax_C'.
	      destruct Hmax_C' as [Ha _].
	      simpl in Ha.
	      contradiction.
Qed.

Theorem graham_scan_closed_convex_hull_final : forall p l,
  sort p (rev l) ->
  l <> [] ->
  is_convex_hull (p :: l) (graham_scan (rev (p :: l))).
Proof.
  intros p l Hsort Hne.
  pose proof (gs_closed_scan_fold_spec p (rev l) Hsort)
    as [C [Hfold [Hsort_C [Hcon_C [Hanchor_C [Hmax_C [Hsub_C Hnonempty_C]]]]]]].
  rewrite rev_involutive in Hfold.
  assert (Hstack : graham_scan (rev (p :: l)) = C ++ [p]).
  {
    rewrite <- fold_left_graham_scan_inc_cons.
    exact Hfold.
  }
  rewrite Hstack.
  split.
  - apply gs_rev_ccw_convex_rotate1.
    apply gs_rev_ccw_convex_anchor; assumption.
  - apply gs_is_max_hull'_edges_rotate1.
    apply gs_is_max_hull'_edges_cons_rev_tail.
    apply gs_is_max_hull'_edges_with_anchor; try assumption.
    + apply Hnonempty_C.
      intro Hrev_nil.
      apply Hne.
      apply (f_equal (@rev point)) in Hrev_nil.
      rewrite rev_involutive in Hrev_nil.
      exact Hrev_nil.
Qed.

Theorem build_hull_convex_hull_final : forall p l,
  sort p (rev l) ->
  l <> [] ->
  Hoare (fun T0 => T0 = [])
        (build_hull p l)
        (fun _ T => is_convex_hull (p :: l) T).
Proof.
  intros p l Hsort Hne.
  eapply Hoare_conseq_post.
  2: apply build_hull_hoare_final.
  intros [] T HT.
  rewrite HT.
  apply graham_scan_closed_convex_hull_final; assumption.
Qed.
