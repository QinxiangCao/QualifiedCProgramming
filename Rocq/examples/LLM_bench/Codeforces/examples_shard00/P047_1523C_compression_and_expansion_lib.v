Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition NextNestedItem (previous next : list Z) : Prop :=
  next = previous ++ (1::nil) \/
  exists prefix last suffix,
    previous = prefix ++ last :: suffix /\
    next = prefix ++ (last+1)::nil /\
    Forall (fun x => x <> last) suffix.
Definition Pre (last_numbers : list Z) : Prop := 1 <= Zlength last_numbers <= 1000 /\
  Forall (fun x => 1 <= x <= Zlength last_numbers) last_numbers /\
  exists items, Zlength items = Zlength last_numbers /\ Znth 0 items nil = 1::nil /\
    (forall i, 0 <= i < Zlength items-1 -> NextNestedItem (Znth i items nil) (Znth (i+1) items nil)) /\
    Forall2
      (fun item last_number =>
        Znth (Zlength item - 1) item 0 = last_number)
      items last_numbers.
Definition Spec (last_numbers : list Z) (out : list (list Z)) : Prop :=
  Zlength out = Zlength last_numbers /\ Znth 0 out nil = 1::nil /\
  (forall i, 0 <= i < Zlength out-1 -> NextNestedItem (Znth i out nil) (Znth (i+1) out nil)) /\
  Forall2
    (fun item last_number =>
      Znth (Zlength item - 1) item 0 = last_number)
    out last_numbers.

Definition CurrentItem (items : list (list Z)) (count : Z)
    (active : list Z) : Prop :=
  (count = 0 /\ active = nil) \/
  (0 < count /\ active = Znth (count - 1) items nil).

Definition PopTarget (active target : list Z) (x : Z) : Prop :=
  exists prefix last suffix,
    active = prefix ++ last :: suffix /\
    target = prefix ++ (last + 1) :: nil /\
    x = last + 1 /\
    Forall (fun y => y <> last) suffix.

Definition FlatPrefix (items : list (list Z)) (count : Z)
    (flat_data : list Z) : Prop :=
  flat_data = concat (sublist 0 count items).

Definition LengthsPrefix (items : list (list Z)) (count : Z)
    (lengths_data : list Z) : Prop :=
  Zlength lengths_data = count /\
  forall i, 0 <= i < count ->
    Znth i lengths_data 0 = Zlength (Znth i items nil).

Definition BoundedItem (bound : Z) (item : list Z) : Prop :=
  Forall (fun value => 1 <= value <= bound) item.

Lemma BoundedItem_nil : forall bound,
  BoundedItem bound nil.
Proof.
  intros bound. constructor.
Qed.

Lemma BoundedItem_Znth : forall bound item i,
  BoundedItem bound item ->
  0 <= i < Zlength item ->
  1 <= Znth i item 0 <= bound.
Proof.
  intros bound item i Hbounded Hi.
  unfold BoundedItem in Hbounded.
  apply (proj1 (Forall_Znth (fun value => 1 <= value <= bound) 0 item));
    assumption.
Qed.

Lemma BoundedItem_append_one : forall bound item,
  1 <= bound ->
  BoundedItem bound item ->
  BoundedItem bound (item ++ 1 :: nil).
Proof.
  intros bound item Hbound Hitem.
  unfold BoundedItem in *.
  apply Forall_app. split; [exact Hitem |].
  constructor.
  - split; [apply Z.le_refl | exact Hbound].
  - constructor.
Qed.

Lemma BoundedItem_prefix : forall bound prefix suffix,
  BoundedItem bound (prefix ++ suffix) ->
  BoundedItem bound prefix.
Proof.
  intros bound prefix suffix Hbounded.
  unfold BoundedItem in *.
  apply Forall_app in Hbounded as [Hprefix Hsuffix].
  exact Hprefix.
Qed.

Lemma PopTarget_preserves_bounds : forall bound active target x,
  BoundedItem bound active ->
  1 <= x <= bound ->
  PopTarget active target x ->
  BoundedItem bound target.
Proof.
  intros bound active target x Hactive Hx Hpop.
  destruct Hpop as
      [prefix [last [suffix [Hactive_eq [Htarget [Hx_eq Hsuffix]]]]]].
  subst active target.
  unfold BoundedItem in *.
  apply Forall_app in Hactive as [Hprefix Hrest].
  apply Forall_app. split; [exact Hprefix |].
  constructor; [rewrite <- Hx_eq; exact Hx | constructor].
Qed.

Require Import Coq.micromega.Lia.
Lemma Forall_Znth__semantic_transitions :
  forall (A : Type) (P : A -> Prop) (values : list A) default i,
    Forall P values ->
    0 <= i < Zlength values ->
    P (Znth i values default).
Proof.
  intros A P values default i Hforall.
  revert i.
  induction Hforall as [|value values Hvalue Hforall IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons. exact Hvalue.
    + assert (0 < i) by lia.
      rewrite Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Forall2_Znth__semantic_transitions :
  forall (A B : Type) (R : A -> B -> Prop)
         (left : list A) (right : list B) (left_default : A)
         (right_default : B) i,
    Forall2 R left right ->
    0 <= i < Zlength left ->
    R (Znth i left left_default) (Znth i right right_default).
Proof.
  intros A B R left right left_default right_default i Hrel.
  revert i.
  induction Hrel as [|a b left right Hab Hrel IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite !Znth0_cons. exact Hab.
    + assert (0 < i) by lia.
      rewrite !Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Forall_removelast__semantic_transitions :
  forall (A : Type) (P : A -> Prop) (values : list A),
    Forall P values -> Forall P (removelast values).
Proof.
  intros A P values Hforall.
  induction Hforall as [|value values Hvalue Hforall IH].
  - constructor.
  - destruct values as [|next rest].
    + constructor.
    + simpl. constructor; assumption.
Qed.
Lemma Zlength_removelast_nonempty__semantic_transitions :
  forall (A : Type) (values : list A),
    values <> nil ->
    Zlength (removelast values) = Zlength values - 1.
Proof.
  intros A values.
  induction values as [|value values IH]; intros Hnonempty.
  - contradiction.
  - destruct values as [|next rest].
    + reflexivity.
    + change (Zlength (value :: removelast (next :: rest)) =
        Zlength (value :: next :: rest) - 1).
      repeat rewrite Zlength_cons.
      rewrite IH by discriminate.
      rewrite Zlength_cons. lia.
Qed.
Lemma Spec_step_and_last__semantic_transitions :
  forall last_numbers items active line,
    Spec last_numbers items ->
    CurrentItem items line active ->
    0 < line < Zlength items ->
    NextNestedItem active (Znth line items nil) /\
    Znth (Zlength (Znth line items nil) - 1)
      (Znth line items nil) 0 = Znth line last_numbers 0.
Proof.
  intros last_numbers items active line Hspec Hcurrent Hline.
  destruct Hspec as [Hlength [Hfirst [Hstep Hlast]]].
  destruct Hcurrent as [[Hzero Hactive] | [Hpos Hactive]]; [lia |].
  split.
  - subst active.
    replace line with ((line - 1) + 1) at 2 by lia.
    apply Hstep. lia.
  - eapply (Forall2_Znth__semantic_transitions
      (list Z) Z
      (fun item last_number =>
         Znth (Zlength item - 1) item 0 = last_number)
      items last_numbers nil 0 line).
    + exact Hlast.
    + lia.
Qed.
Lemma PopTarget_remove_last__semantic_transitions :
  forall bound active target x,
    BoundedItem bound active ->
    PopTarget active target x ->
    Znth (Zlength active - 1) active 0 + 1 <> x ->
    2 <= Zlength active /\
    Zlength (removelast active) = Zlength active - 1 /\
    PopTarget (removelast active) target x /\
    BoundedItem bound (removelast active) /\
    (forall i, 0 <= i < Zlength (removelast active) ->
       Znth i (removelast active) 0 = Znth i active 0).
Proof.
  intros bound active target x Hbounded Hpop Hmismatch.
  destruct Hpop as
      [prefix [last [suffix [Hactive [Htarget [Hx Hsuffix]]]]]].
  destruct suffix as [|next rest].
  - subst active target x.
    exfalso. apply Hmismatch. f_equal.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite app_Znth2 by lia.
    replace (Zlength prefix + Z.succ 0 - 1 - Zlength prefix) with 0 by lia.
    apply Znth0_cons.
  - subst active target x.
    assert (Hnonempty : last :: next :: rest <> nil) by discriminate.
    assert (Hremove :
      removelast (prefix ++ last :: next :: rest) =
      prefix ++ removelast (last :: next :: rest)).
    { apply removelast_app. exact Hnonempty. }
    split; [|split; [|split; [|split]]].
    + pose proof (Zlength_nonneg prefix).
      pose proof (Zlength_nonneg rest).
      rewrite Zlength_app. repeat rewrite Zlength_cons. lia.
    + apply Zlength_removelast_nonempty__semantic_transitions.
      intro Hnil.
      apply (f_equal (@length Z)) in Hnil.
      rewrite length_app in Hnil. simpl in Hnil. lia.
    + unfold PopTarget.
      exists prefix, last, (removelast (next :: rest)).
      split.
      * rewrite Hremove. reflexivity.
      * split; [reflexivity |].
        split; [reflexivity |].
        apply Forall_removelast__semantic_transitions.
        inversion Hsuffix. assumption.
    + unfold BoundedItem in *.
      apply Forall_removelast__semantic_transitions. exact Hbounded.
    + intros i Hi.
      pose proof (app_removelast_last
        (l := prefix ++ last :: next :: rest) 0
        ltac:(intro Hnil; apply (f_equal (@length Z)) in Hnil;
          rewrite length_app in Hnil; simpl in Hnil; lia)) as Hdecomp.
      rewrite Hdecomp at 2.
      rewrite app_Znth1 by exact Hi. reflexivity.
Qed.
Lemma PopTarget_last_match__semantic_transitions :
  forall bound active target x,
    BoundedItem bound active ->
    1 <= x <= bound ->
    PopTarget active target x ->
    Znth (Zlength active - 1) active 0 + 1 = x ->
    target = replace_Znth (Zlength active - 1) x active /\
    BoundedItem bound target.
Proof.
  intros bound active target x Hbounded Hxbound Hpop Hphysical.
  pose proof (PopTarget_preserves_bounds
    bound active target x Hbounded Hxbound Hpop) as Htargetbounded.
  destruct Hpop as
      [prefix [last [suffix [Hactive [Htarget [Hx Hsuffix]]]]]].
  destruct suffix as [|next rest].
  - subst active target x.
    split; [|exact Htargetbounded].
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (Zlength prefix + Z.succ 0 - 1 - Zlength prefix) with 0 by lia.
    reflexivity.
  - exfalso.
    subst active target x.
    pose proof (proj1
      (Forall_Znth (fun value => value <> last) 0 (next :: rest))
      Hsuffix (Zlength (next :: rest) - 1)
      ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia))
      as Hlastneq.
    rewrite Zlength_app in Hphysical.
    rewrite app_Znth2 in Hphysical by
      (rewrite Zlength_cons; pose proof (Zlength_nonneg (next :: rest)); lia).
    rewrite Zlength_cons in Hphysical.
    replace
      (Zlength prefix + Z.succ (Zlength (next :: rest)) - 1 - Zlength prefix)
      with (Zlength (next :: rest)) in Hphysical by lia.
    rewrite Znth_cons in Hphysical by
      (rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia).
    apply Hlastneq. lia.
Qed.
Lemma Znth_last_snoc__semantic_transitions :
  forall (A : Type) (prefix : list A) value default,
    Znth (Zlength (prefix ++ value :: nil) - 1)
      (prefix ++ value :: nil) default = value.
Proof.
  intros A prefix value default.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite app_Znth2 by lia.
  replace (Zlength prefix + Z.succ 0 - 1 - Zlength prefix) with 0 by lia.
  apply Znth0_cons.
Qed.
Lemma Spec_nonone_pop__semantic_transitions :
  forall last_numbers items active line,
    Spec last_numbers items ->
    CurrentItem items line active ->
    0 <= line < Zlength items ->
    Znth line last_numbers 0 <> 1 ->
    0 < line /\
    PopTarget active (Znth line items nil) (Znth line last_numbers 0).
Proof.
  intros last_numbers items active line Hspec Hcurrent Hline Hnonone.
  assert (Hpositive : 0 < line).
  { destruct (Z.eq_dec line 0) as [-> | Hneq]; [|lia].
    destruct Hspec as [Hlength [Hfirst [Hstep Hlast]]].
    pose proof (Forall2_Znth__semantic_transitions
      (list Z) Z
      (fun item last_number =>
         Znth (Zlength item - 1) item 0 = last_number)
      items last_numbers nil 0 0 Hlast ltac:(lia)) as Hrelation.
    rewrite Hfirst in Hrelation. simpl in Hrelation.
    exfalso. apply Hnonone. symmetry. exact Hrelation. }
  split; [exact Hpositive |].
  pose proof (Spec_step_and_last__semantic_transitions
    last_numbers items active line Hspec Hcurrent ltac:(lia))
    as [Hnext Hlast].
  unfold NextNestedItem in Hnext.
  destruct Hnext as [Happend | Hpop].
  - rewrite Happend in Hlast.
    rewrite Znth_last_snoc__semantic_transitions in Hlast.
    exfalso. apply Hnonone. symmetry. exact Hlast.
  - destruct Hpop as
      [prefix [last [suffix [Hactive [Htarget Hsuffix]]]]].
    unfold PopTarget.
    exists prefix, last, suffix.
    split; [exact Hactive |].
    split; [exact Htarget |].
    split.
    + rewrite Htarget in Hlast.
      rewrite Znth_last_snoc__semantic_transitions in Hlast.
      symmetry. exact Hlast.
    + exact Hsuffix.
Qed.
Lemma Spec_one_append__semantic_transitions :
  forall bound last_numbers items active line,
    Spec last_numbers items ->
    CurrentItem items line active ->
    0 <= line < Zlength items ->
    BoundedItem bound active ->
    1 <= bound ->
    Znth line last_numbers 0 = 1 ->
    Znth line items nil = active ++ 1 :: nil.
Proof.
  intros bound last_numbers items active line Hspec Hcurrent Hline
    Hbounded Hbound Hone.
  destruct (Z.eq_dec line 0) as [-> | Hneq].
  - destruct Hcurrent as [[Hzero Hactive] | [Hpositive Hactive]]; [|lia].
    destruct Hspec as [Hlength [Hfirst [Hstep Hlast]]].
    subst active. rewrite Hfirst. reflexivity.
  - assert (Hpositive : 0 < line) by lia.
    pose proof (Spec_step_and_last__semantic_transitions
      last_numbers items active line Hspec Hcurrent ltac:(lia))
      as [Hnext Hlast].
    unfold NextNestedItem in Hnext.
    destruct Hnext as [Happend | Hpop]; [exact Happend |].
    destruct Hpop as
      [prefix [last [suffix [Hactive [Htarget Hsuffix]]]]].
    exfalso.
    rewrite Htarget in Hlast.
    rewrite Znth_last_snoc__semantic_transitions in Hlast.
    subst active.
    unfold BoundedItem in Hbounded.
    apply Forall_app in Hbounded as [Hprefix Hrest].
    inversion Hrest as [|? ? Hlastbound ?].
    lia.
Qed.
Lemma stack_append_one_invariant__semantic_transitions :
  forall cells active depth default,
    depth = Zlength active ->
    0 <= depth < Zlength cells ->
    (forall k, 0 <= k < depth ->
      Znth k cells default = Some (Znth k active 0)) ->
    Zlength (replace_Znth depth (Some 1) cells) = Zlength cells /\
    (forall k, 0 <= k < depth + 1 ->
      Znth k (replace_Znth depth (Some 1) cells) default =
      Some (Znth k (active ++ 1 :: nil) 0)).
Proof.
  intros cells active depth default Hdepth Hcell Hprior.
  split.
  - clear Hdepth Hcell Hprior active default.
    revert depth.
    induction cells as [|cell cells IH]; intros depth; [reflexivity |].
    unfold replace_Znth in *.
    destruct (Z.to_nat depth) as [|index].
    + simpl. repeat rewrite Zlength_cons. reflexivity.
    + simpl. repeat rewrite Zlength_cons.
      specialize (IH (Z.of_nat index)).
      replace (Z.to_nat (Z.of_nat index)) with index in IH by lia.
      rewrite IH. reflexivity.
  - intros k Hk.
    destruct (Z.eq_dec k depth) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by exact Hcell.
      rewrite app_Znth2 by lia.
      replace (depth - Zlength active) with 0 by lia.
      reflexivity.
    + assert (Hlt : k < depth) by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Hprior by lia.
      f_equal.
      rewrite app_Znth1 by lia. reflexivity.
Qed.
Lemma sublist_snoc_Znth__flattening_and_completion :
  forall (A : Type) (d : A) (i : Z) (xs : list A),
    0 <= i < Zlength xs ->
    sublist 0 (i + 1) xs = sublist 0 i xs ++ Znth i xs d :: nil.
Proof.
  intros A d i xs Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single d i xs) by lia.
  reflexivity.
Qed.
Lemma FlatPrefix_snoc__flattening_and_completion :
  forall items line flat,
    FlatPrefix items line flat ->
    0 <= line < Zlength items ->
    FlatPrefix items (line + 1) (flat ++ Znth line items nil).
Proof.
  intros items line flat Hflat Hline.
  unfold FlatPrefix in *.
  rewrite Hflat.
  rewrite (sublist_snoc_Znth__flattening_and_completion
    (list Z) nil line items Hline).
  rewrite concat_app.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma FlatPrefix_full__flattening_and_completion :
  forall items count flat,
    FlatPrefix items count flat ->
    count = Zlength items ->
    flat = concat items.
Proof.
  intros items count flat Hflat Hcount.
  unfold FlatPrefix in Hflat.
  rewrite Hflat, Hcount.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.
Lemma LengthsPrefix_snoc__flattening_and_completion :
  forall items line lengths,
    LengthsPrefix items line lengths ->
    0 <= line < Zlength items ->
    LengthsPrefix items (line + 1)
      (lengths ++ Zlength (Znth line items nil) :: nil).
Proof.
  intros items line lengths [Hlen Hnth] Hline.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros i Hi.
    destruct (Z_lt_ge_dec i line) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      apply Hnth; lia.
    + assert (i = line) by lia.
      subst i.
      rewrite app_Znth2 by lia.
      rewrite Hlen.
      replace (line - line) with 0 by lia.
      reflexivity.
Qed.
Lemma LengthsPrefix_full__flattening_and_completion :
  forall items count lengths,
    count = Zlength items ->
    LengthsPrefix items count lengths ->
    Zlength lengths = count /\
    forall i, 0 <= i < count ->
      Znth i lengths 0 = Zlength (Znth i items nil).
Proof.
  intros items count lengths Hcount Hlengths.
  exact Hlengths.
Qed.
