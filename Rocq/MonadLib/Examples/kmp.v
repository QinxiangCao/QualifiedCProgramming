Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
Require Import ListLib.Base.Positional ListLib.Base.Inductive ListLib.General.Length.
Require Import MonadLib.MonadErr.StateRelMonadErr.




Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.


Export MonadNotation.
Local Open Scope monad.

Section inner_loop_monad.

Context {A: Type}
        (default: A)
        (str: list A)
        (vnext: list Z)
        (ch: A).

Definition inner_body: Z -> program unit (CntOrBrk Z Z) :=
  fun j =>
    assert (0 <= j < Zlength str);;
    assert (j < Zlength vnext);;
    choice (assume!!(ch = Znth j str default);;
            break (j + 1))
            (assume!!(ch <> Znth j str default);;
            choice (assume!!(j = 0);;
                    break (0)) 
                    (assume!!(j <> 0);;
                    continue (Znth (j-1) vnext 0))).

Definition inner_loop: Z -> program unit Z :=
  repeat_break inner_body.

End inner_loop_monad.

Section constr_loop_monad.

Context {A: Type}
        (default: A)
        (str: list A).

Definition constr_body:
  Z -> list Z * Z -> program unit (list Z * Z) :=
  fun i =>
    fun '(vnext, j) =>
      assert (i < Zlength str);;
      let ch := Znth i str default in
      j' <- inner_loop default str vnext ch j;;
      ret (vnext ++ [j'], j').

Definition constr_loop: program unit (list Z) :=
  '(vnext, j) <- range_iter 1 (Zlength str) constr_body ([0], 0);;
  ret vnext.

End constr_loop_monad.

Section match_loop_monad.

Context {A: Type}
        (default: A)
        (patn text: list A)
        (vnext: list Z).

Definition match_body:
  Z -> Z -> program unit (CntOrBrk Z Z) :=
  fun i j =>
      assert (i < Zlength text);;
      let ch := Znth i text default in
      j' <- inner_loop default patn vnext ch j;;
      choice
        (assume!! (j' = Zlength patn);;
         break (i - Zlength patn + 1))
        (assume!! (j' < Zlength patn);;
         continue (j')).

Definition match_loop: program unit (option Z) :=
  res <- range_iter_break 0 (Zlength text) match_body 0;;
  match res with
  | by_continue _ => ret None
  | by_break i => ret (Some i)
  end.

End match_loop_monad.

Definition is_prefix {A: Type} (l1 l2: list A): Prop :=
  exists l,
    l2 = l1 ++ l.

Definition is_suffix {A: Type} (l1 l2: list A): Prop :=
  exists l,
    l2 = l ++ l1.

Notation "l1 'is_a_prefix_of' l2" := (is_prefix l1 l2) (at level 10, no associativity).

Notation "l1 'is_a_suffix_of' l2" := (is_suffix l1 l2) (at level 10, no associativity).

Definition presuffix {A: Type} (l1 l2: list A): Prop :=
  l1 is_a_prefix_of l2 /\
  l1 is_a_suffix_of l2.

Definition partial_match_result {A: Type} (patn text res: list A): Prop :=
  res is_a_suffix_of text /\
  res is_a_prefix_of patn.

Definition best_partial_match_result {A: Type} (patn text res: list A): Prop :=
  partial_match_result patn text res /\
  (forall res', partial_match_result patn text res' -> Zlength res' <= Zlength res).

Definition proper_presuffix {A: Type} (l1 l2: list A): Prop :=
  presuffix l1 l2 /\ Zlength l1 < Zlength l2.

Definition max_proper_presuffix {A: Type} (l1 l2: list A): Prop :=
  proper_presuffix l1 l2 /\
  (forall l3, proper_presuffix l3 l2 -> presuffix l3 l1).

Definition is_prefix_func {A: Type} (vnext: list Z) (patn: list A): Prop :=
forall i0: Z,
  0 <= i0 < Zlength vnext ->
  0 <= Znth i0 vnext 0 <= i0 /\
  max_proper_presuffix
    (sublist 0 (Znth i0 vnext 0) patn)
    (sublist 0 (i0 + 1) patn).

Notation "l1 'is_prefix_func_of' l2" := (is_prefix_func l1 l2) (at level 10, no associativity).

Lemma is_suffix_snoc_snoc_iff: forall {A: Type} (l1 l2: list A) a1 a2,
  (l1 ++ [a1]) is_a_suffix_of (l2 ++ [a2]) <->
  l1 is_a_suffix_of l2 /\ a1 = a2.
Proof.
  intros.
  split; intros.
  + destruct H as [l ?].
    rewrite app_assoc in H.
    apply app_inj_tail in H.
    destruct H.
    split; [eexists; eauto | congruence].
  + destruct H as [ [l ?] ?].
    exists l.
    subst.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma prefix_Zlength: forall {A: Type} (l1 l2: list A),
  l1 is_a_prefix_of l2 ->
  Zlength l1 <= Zlength l2.
Proof.
  intros.
  destruct H as [? ?].
  subst.
  rewrite Zlength_app.
  pose proof Zlength_nonneg x.
  lia.
Qed.

Lemma suffix_Zlength: forall {A: Type} (l1 l2: list A),
  l1 is_a_suffix_of l2 ->
  Zlength l1 <= Zlength l2.
Proof.
  intros.
  destruct H as [? ?].
  subst.
  rewrite Zlength_app.
  pose proof Zlength_nonneg x.
  lia.
Qed.

Lemma presuffix_Zlength: forall {A: Type} (l1 l2: list A),
  presuffix l1 l2 ->
  Zlength l1 <= Zlength l2.
Proof.
  unfold presuffix; intros.
  apply prefix_Zlength; tauto.
Qed.

Lemma prefix_iff: forall {A: Type} (default: A) (l1 l2: list A),
  l1 is_a_prefix_of l2 <->
  (Zlength l1 <= Zlength l2 /\
   forall i, 0 <= i < Zlength l1 -> Znth i l1 default = Znth i l2 default)%Z.
Proof.
  intros.
  split; intros.
  + pose proof prefix_Zlength _ _ H.
    destruct H as [? ?].
    split; [tauto |].
    intros.
    subst.
    rewrite app_Znth1 by lia.
    reflexivity.
  + destruct H.
    pose proof Zlength_nonneg l1.
    exists (sublist (Zlength l1) (Zlength l2) l2).
    rewrite (list_eq_ext _ _ default).
    split.
    - rewrite Zlength_app.
      rewrite Zlength_sublist by lia.
      lia.
    - intros.
      destruct (Z_lt_ge_dec i (Zlength l1)).
      * rewrite app_Znth1 by lia.
        symmetry; apply H0; lia.
      * rewrite app_Znth2 by lia.
        rewrite Znth_sublist by lia.
        f_equal; lia.
Qed.

Lemma prefix_iff': forall {A: Type} (l1 l2: list A),
  l1 is_a_prefix_of l2 <->
  (Zlength l1 <= Zlength l2 /\
   forall default i, 0 <= i < Zlength l1 ->
                     Znth i l1 default = Znth i l2 default)%Z.
Proof.
  intros.
  split; intros.
  + pose proof prefix_Zlength _ _ H.
    split; [tauto |].
    intros d.
    rewrite (prefix_iff d) in H.
    tauto.
  + destruct H.
    destruct l1.
    - exists l2.
      reflexivity.
    - specialize (H0 a).
      rewrite (prefix_iff a).
      tauto.
Qed.

Lemma suffix_iff: forall {A: Type} (default: A) (l1 l2: list A),
  l1 is_a_suffix_of l2 <->
  (Zlength l1 <= Zlength l2 /\
   forall i, 0 <= i < Zlength l1 ->
             Znth (Zlength l1 - 1 - i) l1 default =
             Znth (Zlength l2 - 1 - i) l2 default)%Z.
Proof.
intros.
split; intros.
+ pose proof suffix_Zlength _ _ H.
  destruct H as [? ?].
  split; [tauto |].
  intros.
  subst.
  rewrite Zlength_app.
  rewrite app_Znth2 by lia.
  f_equal. lia.
+ destruct H.
  pose proof Zlength_nonneg l1.
  exists (sublist 0 (Zlength l2 - Zlength l1) l2).
  rewrite (list_eq_ext _ _ default).
  split.
  - rewrite Zlength_app.
    rewrite Zlength_sublist by lia.
    lia.
  - intros.
    destruct (Z_lt_ge_dec i (Zlength l2 - Zlength l1)).
    * rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia).
      rewrite Znth_sublist by lia.
      f_equal; lia.
    * rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
      rewrite Zlength_sublist by lia.
      replace (i - (Zlength l2 - Zlength l1 - 0)) with
              (Zlength l1 - 1 - (Zlength l2 - 1 - i)) by lia.
      rewrite H0 by lia.
      f_equal; lia.
Qed.

Lemma suffix_iff': forall {A: Type} (l1 l2: list A),
  l1 is_a_suffix_of l2 <->
  (Zlength l1 <= Zlength l2 /\
   forall default i, 0 <= i < Zlength l1 ->
             Znth (Zlength l1 - 1 - i) l1 default =
             Znth (Zlength l2 - 1 - i) l2 default)%Z.
Proof.
  intros.
  split; intros.
  + pose proof suffix_Zlength _ _ H.
    split; [tauto |].
    intros d.
    rewrite (suffix_iff d) in H.
    tauto.
  + destruct H.
    destruct l1.
    - exists l2.
      rewrite app_nil_r.
      reflexivity.
    - specialize (H0 a).
      rewrite (suffix_iff a).
      tauto.
Qed.

Lemma is_prefix_snoc_iff: forall {A: Type} default (l1 l2: list A) a,
  (l1 ++ [a]) is_a_prefix_of l2 <->
  (Zlength l1 < Zlength l2 /\
   l1 is_a_prefix_of l2 /\
   a = Znth (Zlength l1) l2 default).
Proof.
  intros.
  rewrite !(prefix_iff default).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  split; intros.
  + destruct H.
    split; [| split; [split |]].
    - lia.
    - lia.
    - intros.
      specialize (H0 i ltac:(lia)).
      rewrite <- H0.
      rewrite app_Znth1 by lia.
      reflexivity.
    - pose proof Zlength_nonneg l1.
      specialize (H0 (Zlength l1) ltac:(lia)).
      rewrite <- H0.
      rewrite app_Znth2 by lia.
      replace (Zlength l1 - Zlength l1) with 0 by lia.
      rewrite Znth0_cons.
      reflexivity.
  + destruct H as [? [[_ ?] ?]].
    split; [lia |].
    intros.
    destruct (Z_lt_ge_dec i (Zlength l1)).
    - rewrite app_Znth1 by lia.
      apply H0; lia.
    - rewrite app_Znth2 by lia.
      replace (i - Zlength l1) with 0 by lia.
      rewrite Znth0_cons.
      rewrite H1; f_equal; lia.
Qed.

Lemma prefix_trans: forall {A: Type} (l1 l2 l3: list A),
  l1 is_a_prefix_of l2 ->
  l2 is_a_prefix_of l3 ->
  l1 is_a_prefix_of l3.
Proof.
  intros.
  destruct H as [? ?], H0 as [? ?].
  exists (x ++ x0).
  subst.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma suffix_trans: forall {A: Type} (l1 l2 l3: list A),
  l1 is_a_suffix_of l2 ->
  l2 is_a_suffix_of l3 ->
  l1 is_a_suffix_of l3.
Proof.
  intros.
  destruct H as [? ?], H0 as [? ?].
  exists (x0 ++ x).
  subst.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma presuffix_trans: forall {A: Type} (l1 l2 l3: list A),
  presuffix l1 l2 ->
  presuffix l2 l3 ->
  presuffix l1 l3.
Proof.
  unfold presuffix; intros; split.
  - apply (prefix_trans _ l2); tauto.
  - apply (suffix_trans _ l2); tauto.
Qed.

Lemma prefix_total_order:
  forall {A: Type} (l1 l2 l: list A),
    l1 is_a_prefix_of l ->
    l2 is_a_prefix_of l ->
    Zlength l1 <= Zlength l2 ->
    l1 is_a_prefix_of l2.
Proof.
  intros ? ? ? ?.
  rewrite !prefix_iff'.
  intros [? ?] [? ?] ?.
  split; [lia |].
  intros.
  rewrite H0, H2 by lia.
  reflexivity.
Qed.

Lemma suffix_total_order:
  forall {A: Type} (l1 l2 l: list A),
    l1 is_a_suffix_of l ->
    l2 is_a_suffix_of l ->
    Zlength l1 <= Zlength l2 ->
    l1 is_a_suffix_of l2.
Proof.
  intros ? ? ? ?.
  rewrite !suffix_iff'.
  intros [? ?] [? ?] ?.
  split; [lia |].
  intros.
  rewrite H0, H2 by lia.
  reflexivity.
Qed.

Lemma partial_match_result_total_order:
  forall {A: Type} (l1 l2 patn text: list A),
    partial_match_result patn text l1 ->
    partial_match_result patn text l2 ->
    Zlength l1 <= Zlength l2 ->
    presuffix l1 l2.
Proof.
  intros.
  destruct H, H0.
  pose proof prefix_total_order _ _ _ H2 H3 H1.
  pose proof suffix_total_order _ _ _ H H0 H1.
  split; tauto.
Qed.

Lemma partial_match_result_iff:
  forall {A: Type} (res0 patn text: list A),
    best_partial_match_result patn text res0 ->
    forall res,
      partial_match_result patn text res <->
      presuffix res res0.
Proof.
  intros.
  split; intros.
  + destruct H.
    specialize (H1 _ H0).
    pose proof partial_match_result_total_order _ _ _ _ H0 H H1.
    tauto.
  + destruct H as [ [? ?] _].
    destruct H0.
    pose proof prefix_trans _ _ _ H0 H1.
    pose proof suffix_trans _ _ _ H2 H.
    split; tauto.
Qed.

Lemma partial_match_result_snoc_iff:
  forall {A: Type} default (res patn text: list A) ch,
    partial_match_result patn (text ++ [ch]) res <->
    res = [] \/
    exists res',
      res = res' ++ [ch] /\
      Zlength res' < Zlength patn /\
      Znth (Zlength res') patn default = ch /\
      partial_match_result patn text res'.
Proof.
  intros.
  split; intros.
  + destruct (list_snoc_destruct res) as [? | [ch0 [res' ?] ] ]; subst res.
    - left.
      tauto.
    - right.
      exists res'.
      destruct H.
      apply is_suffix_snoc_snoc_iff in H.
      destruct H; subst ch0.
      split; [auto | ].
      split; [| split].
      * apply prefix_Zlength in H0.
        rewrite Zlength_app, Zlength_cons, Zlength_nil in H0.
        lia.
      * destruct H0.
        subst patn.
        rewrite <- app_assoc.
        rewrite app_Znth2 by lia.
        replace (Zlength res' - Zlength res') with 0 by lia.
        simpl app.
        rewrite Znth0_cons.
        reflexivity.
      * split; auto.
        eapply prefix_trans; [ | apply H0].
        exists [ch]; reflexivity.
  + destruct H as [? | [? [? ?] ] ].
    - subst.
      split.
      * exists (text ++ [ch]).
        rewrite app_nil_r.
        reflexivity.
      * exists patn.
        reflexivity.
    - destruct H0 as [? [? [? ?] ]].
      subst.
      split; auto.
      * apply is_suffix_snoc_snoc_iff.
        tauto.
      * rewrite (is_prefix_snoc_iff default).
        tauto.
Qed.

Lemma sublist_one_ele {A: Type}: 
  forall i (text: list A) (ch default: A),
    0 <= i < Zlength text ->
    ch = Znth i text default -> 
    sublist 0 i text ++ [ch] = sublist 0 (i + 1) text.
Proof.
  intros.
  apply (list_eq_ext _ _ default).
  split.
  + rewrite Zlength_app.
    rewrite ! Zlength_sublist by lia.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  + intros.
    destruct (Z_lt_ge_dec i0 i).
    - rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia).
      rewrite !Znth_sublist by lia.
      reflexivity.
    - rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
      rewrite Zlength_app, Zlength_sublist in H1 by lia.
      rewrite Zlength_cons, Zlength_nil in H1.
      rewrite !Znth_sublist by lia.
      rewrite Zlength_sublist by lia.
      replace (i0 - (i - 0)) with 0 by lia.
      rewrite Znth0_cons.
      subst ch.
      f_equal; lia.
Qed.

Lemma sublist_one_ele' {A: Type}:
  forall i (text: list A) default,
    0 <= i < Zlength text ->
    sublist 0 (i + 1) text = sublist 0 i text ++ [Znth i text default].
Proof.
  intros.
  rewrite (sublist_one_ele i text (Znth i text default) default) by easy.
  reflexivity.
Qed.

Lemma sublist_single' {A: Type}:
  forall (n : Z) (l : list A) (a : A),
    0 < n <= Z.of_nat (Datatypes.length l) ->
    sublist (n - 1) n l = [Znth (n - 1) l a].
Proof.
  intros.
  remember (n-1) as t.
  assert (n = t + 1) by lia.
  rewrite H0.
  apply sublist_single.
  rewrite Zlength_correct. lia.
Qed.

Lemma prefix_iff_sublist {A: Type}:
  forall (l1 l2: list A),
    l1 is_a_prefix_of l2 <->
    (exists j, 0 <= j <= Zlength l2 /\ l1 = sublist 0 j l2).
Proof.
  split; intros.
  - unfold is_prefix in H.
    destruct H as [l3 H].
    exists (Zlength l1).
    pose proof Zlength_app l1 l3.
    pose proof Zlength_nonneg l1.
    pose proof Zlength_nonneg l3.
    subst; split; try lia.
    rewrite sublist_split_app_l; try lia.
    rewrite sublist_self; easy.
  - destruct H as [j [? ?]].
    unfold is_prefix.
    exists (sublist j (Zlength l2) l2).
    rewrite <- sublist_self at 1 by eauto.
    rewrite (sublist_split 0 (Zlength l2) j); try lia.
    subst; easy.
Qed.

Lemma nil_prefix {A: Type}:
  forall (l: list A), [] is_a_prefix_of l.
Proof.
  intros; unfold is_prefix.
  exists l; easy.
Qed.

Lemma nil_suffix {A: Type}:
  forall (l: list A), [] is_a_suffix_of l.
Proof.
  intros; unfold is_suffix.
  exists l. rewrite app_nil_r; easy.
Qed.

Lemma nil_presuffix {A: Type}:
  forall (l: list A), presuffix [] l.
Proof. 
  intros; unfold presuffix.
  split; [apply nil_prefix | apply nil_suffix].
Qed.

Lemma presuffix_nil_iff {A: Type}:
  forall (l:list A), presuffix l [] <-> l = [].
Proof.
  intros; split; intros.
  - unfold presuffix in H.
    pose proof prefix_Zlength _ _ (proj1 H).
    rewrite Zlength_nil in H0.
    pose proof Zlength_nonneg l.
    apply Zlength_nil_inv; lia.
  - subst; apply nil_presuffix.
Qed.

Lemma partial_match_nil {A: Type}:
  forall (patn text: list A),
    partial_match_result patn text [].
Proof.
  intros; unfold partial_match_result.
  split; [apply nil_suffix | apply nil_prefix].
Qed.

Lemma Zlength_nonnil {A: Type}:
  forall (l: list A),
    l <> [] <-> Zlength l > 0.
Proof.
  intros; split; intros; destruct l; try easy.
  rewrite Zlength_cons. 
  pose proof Zlength_nonneg l; lia.
Qed.

(** 
  Below are the main proof for properties of the abstract program,
  which consists of properties of three loops in the form of Hoare triple.

  For complicated loop properties, to make the proof more readable,
  we may split the property into several parts,
  prove the loop body maintains each of them respectively (based on some induction hypothesis),
  and then combine them into a loop invariant to prove the property of the whole loop. 
*)

(**
  This section contains the basic properties regarding the range of key variants in 3 loops. 
*)
Section range.

Context {A: Type}
        (default: A)
        (patn text: list A)
        (vnext: list Z).

Definition jrange {B: Type} (j: Z) (array: list B) :=
  0 <= j < Zlength array.

Lemma inner_jrange_inv (i j: Z):
  Zlength vnext <= Zlength patn ->
  (forall i0: Z,
    0 <= i0 < Zlength vnext ->
    0 <= Znth i0 vnext 0 < Zlength vnext) ->
  jrange j vnext ->
  Hoare (fun _ => True)
        (x <- inner_body default patn vnext (Znth i text default) j;; continue_case x)
        (fun j' _ => jrange j' vnext).
Proof.
  intros; unfold jrange in *.
  unfold inner_body.
  hoare_auto; try lia.
  specialize (H0 (j-1) ltac:(lia)).
  lia.
Qed.

Lemma inner_pre_derive_jrange:
  vnext is_prefix_func_of patn ->
  (forall i0: Z,
    0 <= i0 < Zlength vnext ->
    0 <= Znth i0 vnext 0 < Zlength vnext).
Proof.
  intros.
  specialize (H i0 ltac:(lia)).
  lia.
Qed.

Lemma inner_jrange_brk1 (j: Z):
  jrange j vnext -> 0 <= j+1 <= Zlength vnext.
Proof.
  intros; hnf in H; lia.
Qed.

Lemma inner_jrange_brk2:
  0 <= 0 <= Zlength vnext.
Proof.  
  split; [lia | apply Zlength_nonneg].
Qed.

(* Problem: 
   constr inv implicitly implies jrange. 
   Explicitly asserting jrange comes with the cost of redundent inv & spec.  
*)
Lemma constr_pre_jrange:  
  jrange 0 [0].
Proof. easy. Qed.

Lemma constr_inner_post_jrange (j: Z):
  0 <= j <= Zlength vnext ->
  jrange j (vnext ++ [j]).
Proof.
  intros; hnf.
  rewrite Zlength_app.
  replace (Zlength [j]) with 1 by reflexivity.
  lia.
Qed.

Lemma match_pre_jrange:
  patn <> [] ->
  Zlength vnext = Zlength patn ->
  jrange 0 vnext.
Proof.
  intros.
  apply Zlength_nonnil in H.
  hnf; lia.
Qed.

Lemma match_inner_post_jrange (j: Z):
  Zlength vnext = Zlength patn ->
  0 <= j <= Zlength vnext ->
  j < Zlength patn ->
  jrange j vnext.
Proof.
  intros.
  hnf; lia.
Qed.

End range.

Section inner.

Context {A: Type}
        (default: A)
        (patn text: list A)
        (vnext: list Z)
        (i: Z).

Section partial_match_inv.

Definition partial_match_inv (j: Z) :=
  partial_match_result patn (sublist 0 i text) (sublist 0 j patn).

Lemma inner_pre_partial_match_inv (j: Z):
  best_partial_match_result 
    patn (sublist 0 i text) (sublist 0 j patn) ->
  partial_match_inv j.
Proof.
  intros.
  unfold partial_match_inv.
  unfold best_partial_match_result in H; tauto.
Qed.

Lemma inner_partial_match_inv (j_pre j: Z):
  Zlength vnext <= Zlength patn ->
  vnext is_prefix_func_of patn ->
  best_partial_match_result 
    patn (sublist 0 i text) (sublist 0 j_pre patn) ->
  jrange j vnext ->
  partial_match_inv j ->
  Hoare (fun _ => True)
        (x <- inner_body default patn vnext (Znth i text default) j;; continue_case x)
        (fun j' _ => partial_match_inv j').
Proof.
  intros Hl Hf Hb Hjr Hp.
  unfold jrange, partial_match_inv in *.
  unfold inner_body.
  hoare_auto; try lia.
  unfold is_prefix_func in Hf.
  specialize (Hf (j-1) ltac:(lia)). 
  replace (j - 1 + 1) with j in Hf by lia.
  destruct Hf as [Hnj [[Hf _] _]].
  apply (partial_match_result_iff _ _ _ Hb).
  apply (partial_match_result_iff _ _ _ Hb) in Hp.
  eapply presuffix_trans; [apply Hf | auto].
Qed.

End partial_match_inv.

Section presuffix_inv.

Definition presuffix_inv (j: Z) :=
  forall j0,
    0 < j0 <= Zlength patn ->
    (partial_match_result patn 
    (sublist 0 (i + 1) text) (sublist 0 j0 patn) 
    <->  
    Znth (j0 - 1) patn default = Znth i text default /\
    presuffix (sublist 0 (j0 - 1) patn) (sublist 0 j patn)).

Lemma inner_pre_presuffix_inv (j: Z):
  Zlength vnext <= Zlength patn ->
  0 <= i < Zlength text ->
  best_partial_match_result patn 
    (sublist 0 i text) (sublist 0 j patn) ->
  presuffix_inv j.
Proof.
  intros Hz Hi Hb. 
  unfold presuffix_inv.
  intros j0 Hj0.
  rewrite <- (sublist_one_ele _ _ (Znth i text default) default); try lia; auto.
  rewrite partial_match_result_snoc_iff with (default:=default).
  assert (Hj0': 0 < j0 <= Z.of_nat (length patn)).
  rewrite <- Zlength_correct; lia.
  split; intros.
  - destruct H. 
    {
      pose proof Zlength_sublist 0 j0 patn ltac:(lia).
      rewrite H in H0.
      unfold Zlength in H0; simpl in H0.
      lia.
    }
    destruct H as [res [? [? [? ?]]]].
    pose proof (f_equal (@Zlength _) H) as Hl.
    rewrite Zlength_sublist in Hl by lia.
    rewrite Zlength_app in Hl.
    change (Zlength [Znth i text default]) with 1 in Hl.
    assert (j0 - 1 = Zlength res) by lia.
    split; [rewrite H3; auto | ].
    rewrite <- (partial_match_result_iff _ _ _ Hb).
    rewrite (sublist_split 0 j0 (j0-1)) in H by lia.
    rewrite (sublist_single' _ _ default) in H by lia.
    rewrite <- H1 in *; rewrite <- H3 in H.
    apply app_inv_tail in H.
    rewrite H; auto.
  - right; exists (sublist 0 (j0 - 1) patn).
    destruct H. 
    split; [| split; [ | split]].
    + rewrite (sublist_split 0 j0 (j0-1)); try lia.
      rewrite sublist_single' with (a:=default) by lia.
      rewrite H; auto.
    + rewrite Zlength_sublist; lia.
    + rewrite Zlength_sublist by lia.
      replace (j0 - 1 - 0) with (j0 - 1) by lia; auto.
    + rewrite partial_match_result_iff with (res0:=(sublist 0 j patn)); auto.
Qed.

Lemma inner_presuffix_inv (j: Z):
  Zlength vnext <= Zlength patn ->
  vnext is_prefix_func_of patn ->
  jrange j vnext ->
  presuffix_inv j ->
  Hoare (fun _ => True)
        (x <- inner_body default patn vnext (Znth i text default) j;; continue_case x)
        (fun j' _ => presuffix_inv j').
Proof.
  intros H Hf H0 Hj.
  unfold jrange in *.
  unfold inner_body; hoare_auto; try lia.
  clear s H5; unfold is_prefix_func in Hf.
  specialize (Hf (j-1) ltac:(lia)). 
  replace (j - 1 + 1) with j in Hf by lia.
  unfold presuffix_inv in *.
  intros j0 Hj0.
  specialize (Hj j0 Hj0).
  rewrite Hj; clear Hj.
  destruct Hf as [Hfj Hf]. 
  split; intros Hp; split; try easy.
  2:{
    destruct Hf as [[Hf _] _].
    eapply presuffix_trans; [apply Hp | tauto].
  }
  destruct Hp as [Hj1 Hj2].
  pose proof (Zlength_sublist 0 (j0 - 1) patn ltac:(lia)) as Hj0len.
  pose proof (Zlength_sublist 0 j patn ltac:(lia)) as Hjlen.
  pose proof presuffix_Zlength _ _ Hj2.
  destruct (j - (j0 - 1)) eqn:Ej; try lia.
  replace (j0 - 1) with j in Hj1 by lia.
  rewrite Hj1 in H3; easy.
  assert (Hlen: Zlength (sublist 0 (j0 - 1) patn) < Zlength (sublist 0 j patn)) by lia.
  destruct Hf as [_ Hf]; apply Hf.
  unfold proper_presuffix; tauto.
Qed.

End presuffix_inv.

Ltac hoare_conj := try (apply Hoare_conj; [ | hoare_conj]).

Definition inner_inv (j: Z) :=
  jrange j vnext /\ partial_match_inv j /\ presuffix_inv j.

Section inner_brk.

Context (j: Z).
Hypothesis H0: inner_inv j.

(* case1: ch = patn[j] *)
Lemma inner_body_prop_brk1:
  Zlength vnext <= Zlength patn ->
  0 <= i < Zlength text ->
  Znth i text default = Znth j patn default ->
  0 <= j + 1 <= Zlength vnext /\ 
  best_partial_match_result patn (sublist 0 (i + 1) text) (sublist 0 (j+1) patn).
Proof.
  intros; unfold inner_inv in *.
  split. apply inner_jrange_brk1; tauto.
  unfold jrange, partial_match_inv, presuffix_inv in H0.
  destruct H0 as [Hjrange [Ha1 Ha2]]; clear H0.
  split.
  {
    rewrite (sublist_one_ele' i _ default) by lia.
    rewrite (sublist_one_ele' j _ default) by lia.
    apply (partial_match_result_snoc_iff default).
    right; exists (sublist 0 j patn).
    split. apply app_inj_tail_iff; easy.
    pose proof Zlength_sublist 0 j patn ltac:(lia).
    replace (j - 0) with j in H0 by lia.
    split; try lia.
    rewrite H0; split; try easy.
  }
  intros res Hr.
  pose proof (proj2 Hr) as Hrp.
  apply prefix_iff_sublist in Hrp.
  destruct Hrp as [j0 [Hj ?]]; subst res.
  destruct j0; try lia.
  { 
    rewrite Zsublist_nil by easy.
    rewrite Zlength_nil.
    apply Zlength_nonneg.
  }
  remember (Z.pos p) as j0; assert (j0 > 0) by lia; clear Heqj0.
  specialize (Ha2 j0 ltac:(lia)).
  rewrite Ha2 in Hr; clear Ha2.
  destruct Hr as [_ Hr].
  apply presuffix_Zlength in Hr.
  repeat rewrite Zlength_sublist in Hr by lia.
  repeat rewrite Zlength_sublist by lia; lia.
Qed.

(* case2: ch <> patn[j], i.e. j = 0 *)
Lemma inner_body_prop_brk2:
  Znth i text default <> Znth j patn default ->
  j = 0 ->
  0 <= 0 <= Zlength vnext /\
  best_partial_match_result patn (sublist 0 (i + 1) text) (sublist 0 0 patn).
Proof.
  intros; unfold inner_inv in *.
  subst j.
  rewrite (Zsublist_nil patn) by lia.
  split. apply inner_jrange_brk2.
  split. apply partial_match_nil.
  intros res Hr.
  pose proof (proj2 Hr) as Hrp.
  apply prefix_iff_sublist in Hrp.
  destruct Hrp as [j0 [Hj ?]]; subst res.
  destruct j0; try lia.
  rewrite Zsublist_nil by lia; easy.
  remember (Z.pos p) as j0; assert (j0 > 0) by lia; clear Heqj0.
  destruct H0 as [_ [_ H4]].
  unfold presuffix_inv in H4.
  specialize (H4 j0 ltac:(lia)).
  rewrite H4 in Hr.
  destruct Hr as [Hc Hr].
  rewrite (Zsublist_nil _ 0 0) in Hr by lia.
  apply presuffix_Zlength in Hr.
  rewrite Zlength_sublist in Hr by lia.
  rewrite Zlength_nil in Hr.
  assert (j0 = 1) by lia; subst.
  replace (1-1) with 0 in Hc by lia.
  congruence.
Qed.

End inner_brk.

Definition inner_pre (j_pre: Z):=
  Zlength vnext <= Zlength patn /\
  vnext is_prefix_func_of patn /\
  0 <= i < Zlength text /\
  0 <= j_pre < Zlength vnext /\
  best_partial_match_result patn 
    (sublist 0 i text) (sublist 0 j_pre patn).

Definition inner_post (j: Z) :=
  0 <= j <= Zlength vnext /\
  best_partial_match_result patn 
    (sublist 0 (i + 1) text) (sublist 0 j patn).

Lemma inner_body_prop_inv (j_pre j: Z):
  inner_pre j_pre ->
  inner_inv j ->
  Hoare (fun _ => True)
        (x <- inner_body default patn vnext (Znth i text default) j;; continue_case x)
        (fun j' _ => inner_inv j').
Proof.
  intros; unfold inner_pre, inner_inv in *.
  hoare_conj.
  - apply inner_jrange_inv; try tauto.
    eapply inner_pre_derive_jrange. apply H.
  - apply (inner_partial_match_inv j_pre); tauto.
  - apply inner_presuffix_inv; tauto.
Qed.

Lemma inner_body_prop_brk (j: Z):
  Zlength vnext <= Zlength patn ->
  0 <= i < Zlength text ->
  inner_inv j ->
  Hoare (fun _ => True)
        (x <- inner_body default patn vnext (Znth i text default) j;; break_case x)
        (fun j' _ => inner_post j').
Proof.
  intros; unfold inner_body, inner_post.
  hoare_auto.
  - unfold inner_pre, inner_inv, jrange in *; lia.
  - unfold inner_pre, inner_inv, jrange in *; lia.
  - apply inner_body_prop_brk1; auto.
  - eapply inner_body_prop_brk2; eauto.
Qed.

Lemma inner_loop_prop (j: Z):
  inner_pre j ->
  Hoare (fun _ => True)
        (inner_loop default patn vnext (Znth i text default) j)
        (fun j' _ => inner_post j').
Proof.
  intros.
  unfold inner_loop, inner_post; unfold inner_pre in H.
  eapply Hoare_cons_pre. 
  2: eapply (Hoare_repeat_break  _ 
       (fun j' _ => inner_inv j')) .
  - intros ? _; simpl.
    split; [ |split].
    + hnf; tauto.
    + apply inner_pre_partial_match_inv; tauto.
    + apply inner_pre_presuffix_inv; tauto. 
  - intros; apply Hoare_sum; stateless_intros.
    eapply inner_body_prop_inv; eauto.
    apply inner_body_prop_brk; tauto.
Qed.

End inner.

Lemma prefix_app_iff {A: Type}:
  forall (l1 l2 l3: list A),
    l1 is_a_prefix_of l2 <->
    Zlength l1 <= Zlength l2 /\ l1 is_a_prefix_of (l2 ++ l3).
Proof.
  split; intros.
  - split. apply prefix_Zlength, H.
    unfold is_prefix in *.
    destruct H. exists (x ++ l3).
    rewrite H. rewrite app_assoc; auto.
  - destruct H as [H0 H1].
    rewrite prefix_iff' in *.
    destruct H1 as [_ H1]; split; try easy.
    intros. specialize (H1 default i H).
    rewrite app_Znth1 in H1 by lia; auto.
Qed.

Lemma suffix_app_iff {A: Type}:
  forall (l1 l2 l3: list A),
    l1 is_a_suffix_of l2 <->
    Zlength l1 <= Zlength l2 /\ l1 is_a_suffix_of (l3 ++ l2) .
Proof.
  split; intros.
  - split. apply suffix_Zlength, H.
    unfold is_suffix in *.
    destruct H. exists (l3 ++ x).
    rewrite H. rewrite app_assoc; auto.
  - destruct H as [H0 H1].
    rewrite suffix_iff' in *.
    destruct H1 as [_ H1]; split; try easy.
    intros. specialize (H1 default i H).
    rewrite Zlength_app in H1.
    rewrite app_Znth2 in H1 by lia.
    replace (Zlength l3 + Zlength l2 - 1 - i - Zlength l3) 
      with (Zlength l2 - 1 - i) in H1 by lia; auto.
Qed.

Lemma prefix_sublist_iff {A: Type}:
  forall (l0 l: list A) i,
    0 <= i <= Zlength l ->
    l0 is_a_prefix_of (sublist 0 i l) <->
    Zlength l0 <= i /\ l0 is_a_prefix_of l.
Proof.
  intros.
  rewrite <- (sublist_self l) at 2; eauto.
  rewrite (sublist_split 0 (Zlength l) i); try lia.
  pose proof Zlength_sublist 0 i l ltac:(lia).
  replace (i - 0) with i in H0 by lia.
  rewrite <- H0 at 2.
  apply prefix_app_iff.
Qed.

Lemma suffix_sublist_cons_iff {A: Type}:
  forall (l0 l: list A) i,
    1 <= i <= Zlength l ->
    l0 is_a_suffix_of (sublist 1 i l) <->
    Zlength l0 <= i - 1 /\ l0 is_a_suffix_of (sublist 0 i l).
Proof.
  intros.
  rewrite (sublist_split 0 i 1); try lia.
  pose proof Zlength_sublist 1 i l ltac:(lia).
  rewrite <- H0.
  apply suffix_app_iff.
Qed.

Lemma max_proper_best_partial {A: Type}:
  forall (l: list A) i j,
    1 <= i <= Zlength l ->
    max_proper_presuffix (sublist 0 j l) (sublist 0 i l) <->
    best_partial_match_result l (sublist 1 i l) (sublist 0 j l).
Proof.
   intros; unfold max_proper_presuffix, best_partial_match_result.
   unfold partial_match_result; split; intros; destruct H0.
   - destruct H0 as [[Hp Hs] Hl].
     remember (sublist 0 j l) as lj.
     rewrite Zlength_sublist in Hl; try lia.
     rewrite Z.sub_0_r in Hl.
     split; [split | ].
     + apply suffix_sublist_cons_iff; try lia.
       split; [lia | auto].
     + apply prefix_sublist_iff in Hp; [easy | lia].
     + intros. destruct H0.
       apply presuffix_Zlength. apply H1.
       pose proof suffix_Zlength _ _ H0.
       rewrite Zlength_sublist in H3 by lia.
       split; [split | ].
       apply prefix_sublist_iff; try lia.
       split; [lia | auto].
       apply suffix_sublist_cons_iff; [lia | easy].
       rewrite Zlength_sublist by lia. lia.
   - unfold proper_presuffix.
     destruct H0.
     pose proof suffix_Zlength _ _ H0.
     remember (sublist 0 j l) as lj.
     rewrite Zlength_sublist in H3 by lia.
     split; [split; [split |] |].
     + apply prefix_sublist_iff; try lia.
       split; [lia | auto].
     + apply suffix_sublist_cons_iff in H0; [tauto | lia].
     + rewrite Zlength_sublist by lia; lia.
     + intros. destruct H4 as [[? ? ] ?].
       rewrite Zlength_sublist in H6 by lia.
       assert (Zlength l3 <= Zlength lj).
       {
        apply H1; split.
        apply suffix_sublist_cons_iff; try lia.
        split; [lia | auto].
        apply prefix_sublist_iff in H4; try lia; tauto.
       }
       clear H1; split.
       apply prefix_sublist_iff in H4; try lia.
       apply (prefix_total_order _ _ l); tauto.
       apply suffix_total_order with (l:=(sublist 1 i l)); try tauto.
       apply suffix_sublist_cons_iff; try lia.
       split; auto; lia.
Qed.

Lemma sublist_sublist01: 
  forall {A : Type} (i j : Z) (l : list A),
   0 <= i < j -> sublist 0 i (sublist 1 j l) = sublist 1 (i+1) l.
Proof.
  intros. 
  rewrite Zsublist_Zsublist ; try lia.
  auto.
Qed.

Section constr.

Context {A: Type}
        (default: A)
        (patn: list A).

Definition constr_inv (vnext: list Z) (i j: Z) :=
  jrange j vnext /\
  Zlength vnext = i /\
  vnext is_prefix_func_of patn /\
  j = Znth (i-1) vnext 0.

Lemma constr_pre_derive_inv:
  Zlength patn > 0 -> constr_inv [0] 1 0.
Proof.
  intros; unfold constr_inv.
  split. apply constr_pre_jrange.
  split; [ | split]; try reflexivity.
  unfold is_prefix_func; intros.
  rewrite Zlength_correct in H0; simpl in H0.
  assert (i0 = 0) by lia; subst i0; simpl.
  split; try easy.
  assert (Znth 0 [0] 0 = 0) by easy. rewrite H1.
  rewrite Zsublist_nil by lia.
  pose proof Zlength_nil A.
  pose proof Zlength_sublist 0 1 patn ltac:(lia).
  split. split; try lia.
  apply nil_presuffix.
  intros. destruct H4 as [_ ?].
  pose proof Zlength_nonneg l3.
  assert (Zlength l3 = 0) by lia.
  apply Zlength_nil_inv in H6; rewrite H6.
  apply nil_presuffix.
Qed.

(* spec derivation *)
Section inner_spec_vnext.

Context (vnext: list Z) (i j: Z).
Hypothesis Hi: 1 <= i < Zlength patn.
Hypothesis H: constr_inv vnext i j.

Lemma constr_inner_spec_pre: 
  inner_pre patn (sublist 1 (Zlength patn) patn) vnext (i - 1) j.
Proof.
  destruct H as [Hj [H0 [H1 H2]]].
  pose proof (H1 (i-1) ltac:(lia)); try lia.
  unfold inner_pre.
  split; try lia.
  split; auto.
  rewrite Zlength_sublist by lia. 
  split; try lia.
  split. apply Hj.
  rewrite <- H2 in *; clear H2.
  rewrite sublist_sublist01 by lia.
  replace (i - 1 + 1) with i in * by lia.
  apply max_proper_best_partial; [lia | tauto].
Qed.

Lemma constr_inner_spec_post (j': Z):
  inner_post patn (sublist 1 (Zlength patn) patn) vnext (i - 1) j'->
  jrange j' (vnext ++ [j']) /\ (vnext ++ [j']) is_prefix_func_of patn.
Proof.
  destruct H as [_ [H0 [H1 _]]].
  intros H4; hnf in H4.
  split. apply constr_inner_post_jrange; tauto.
  unfold is_prefix_func in *.
  rewrite Zlength_app.
  rewrite (Zlength_correct [j']). simpl.
  intros. rewrite H0 in *.
  destruct (i - i0) eqn: Ei; try lia.
  2: {
    rewrite app_Znth1 by lia.
    apply H1; lia.
  }
  assert (i = i0) by lia; subst i0. 
  clear Ei.
  assert (Znth i (vnext ++ [j']) 0 = j').
  {
    rewrite app_Znth2 by lia.
    replace (i - Zlength vnext) with 0 by lia.
    reflexivity.
  }
  rewrite H3; clear H3.
  split; try lia.
  replace (i - 1 + 1) with i in H4 by lia.
  rewrite sublist_sublist01 in H4 by lia.
  apply max_proper_best_partial; try lia; tauto.
Qed.

Lemma inner_loop_prop_vnext: 
  Hoare (fun _ => True)
        (inner_loop default patn vnext (Znth i patn default) j)
        (fun j' _ => jrange j' (vnext ++ [j']) /\ (vnext ++ [j']) is_prefix_func_of patn).
Proof.
  intros.
  destruct H as [Hj [H0 [H1 H2]]].
  assert (Znth i patn default = Znth (i-1) (sublist 1 (Zlength patn) patn) default).
  {
    rewrite Znth_sublist by lia.
    replace (i - 1 + 1) with i by lia. auto.
  }
  rewrite H3.
  eapply Hoare_cons_post.
  2:{
    apply inner_loop_prop; try tauto; try lia;
    apply constr_inner_spec_pre.
  }
  simpl; intros.
  apply constr_inner_spec_post; auto.
Qed.

End inner_spec_vnext.

Lemma constr_body_prop:
  forall (vnext: list Z) (i j: Z),
    1 <= i < Zlength patn ->
    constr_inv vnext i j ->
    Hoare (fun _ => True)
          (constr_body default patn i (vnext, j))
          (fun (res: list Z * Z) _ => 
            let (vnext', j') := res in
            constr_inv vnext' (i+1) j').
Proof.
  intros; unfold constr_body.
  hoare_step. tauto.
  eapply Hoare_bind.
  apply inner_loop_prop_vnext; auto.
  destruct H0 as [Hj [? [? ?]]].
  intros; hoare_step.
  destruct H4.
  split. tauto.
  split; [ | split]; auto.
  rewrite Zlength_app.
  rewrite H0; reflexivity.
  rewrite app_Znth2; try lia.
  rewrite H0. replace (i+1-1-i) with 0 by lia.
  reflexivity.
Qed.

Theorem constr_loop_sound:
  patn <> [] ->
  Hoare (fun _ => True) 
        (constr_loop default patn) 
        (fun vnext _ => vnext is_prefix_func_of patn /\ Zlength vnext = Zlength patn).
Proof.
  intros. apply Zlength_nonnil in H.
  unfold constr_loop.
  eapply Hoare_bind.
  apply Hoare_range_iter with (P := fun k (res: list Z * Z) _ =>
                              let (vnext, j) := res in                      
                              constr_inv vnext k j); try lia.
  - intros; apply constr_pre_derive_inv; auto.
  - intros. eapply (Hoare_implies _ (fun _ => True)).
    intros. split; auto. exact H1.
    intros. destruct a as [vnext j].
    apply constr_body_prop; easy.
  - intros. destruct a as [vnext j].
    apply Hoare_ret; intros.
    unfold constr_inv in H0; easy.
Qed.

End constr.

Lemma suffix_Zlength_inv {A: Type}:
  forall l1 l2: list A,
    Zlength l1 = Zlength l2 ->
    l1 is_a_suffix_of l2 ->
    l1 = l2.
Proof.
  intros.  unfold is_suffix in H0.
  destruct H0 as [l3 H0].
  pose proof Zlength_app l3 l1.
  subst l2.
  assert (Zlength l3 = 0) by lia.
  apply Zlength_nil_inv in H0; subst.
  reflexivity.
Qed.
    
Lemma best_partial_match_inv {A: Type}:
  forall (patn text l1 l2: list A),
    best_partial_match_result patn text l1 ->
    best_partial_match_result patn text l2 ->
    l1 = l2.
Proof.
  intros.
  destruct H as [H1 H2]; destruct H0 as [H3 H4].
  pose proof H2 _ H3; pose proof H4 _ H1.
  assert (presuffix l1 l2).
  { apply (partial_match_result_total_order _ _ patn text); auto. }
  destruct H5 as [_ H5].
  apply suffix_Zlength_inv; [lia | auto].
Qed.

Lemma best_partial_match_iff {A: Type}:
  forall (patn text: list A) r,
    0 <= r <= Zlength text - Zlength patn ->
    best_partial_match_result patn (sublist 0 (r + Zlength patn) text) patn <->
    sublist r (r + Zlength patn) text = patn.
Proof.
  intros; unfold best_partial_match_result.
  pose proof (Zlength_nonneg text).
  pose proof (Zlength_nonneg patn).
  split; intros.
  - destruct H2 as [[H2 _] _].
    rewrite (sublist_split 0 (r + Zlength patn) r) in H2; try lia.
    assert (patn is_a_suffix_of (sublist r (r + Zlength patn) text)).
    { 
      rewrite suffix_app_iff with (l3:=sublist 0 r text).
      split; auto.
      rewrite Zlength_sublist by lia; lia.
    }
    pose proof Zlength_sublist r (r + Zlength patn) text ltac:(lia).
    symmetry.
    apply suffix_Zlength_inv; [lia | tauto].
  - split; intros.
    2:{
      destruct H3 as [_ H3].
      apply prefix_Zlength; auto.
    }
    split.
    2:{ 
      unfold is_prefix. 
      exists nil; rewrite app_nil_r; easy. 
    }
    unfold is_suffix.
    exists (sublist 0 r text).
    rewrite <- H2 at 2. 
    apply sublist_split; try lia.
Qed.

Definition no_occurance {A: Type} (patn: list A) (text: list A) :=
  forall i, 0 <= i <= Zlength text - Zlength patn -> 
    sublist i (i + Zlength patn) text <> patn.

Definition first_occur {A: Type} (patn: list A) (text: list A) (z: Z) :=
  sublist z (z + Zlength patn) text = patn /\
  no_occurance patn (sublist 0 (z + Zlength patn - 1) text).

Section Match.

Context {A: Type}
        (default: A)
        (patn text: list A)
        (vnext: list Z).

Definition match_pre :=
  Zlength vnext = Zlength patn /\
  vnext is_prefix_func_of patn /\
  patn <> [].

Definition match_inv (i j: Z) :=
  0 <= j < Zlength vnext /\
  best_partial_match_result patn (sublist 0 i text) (sublist 0 j patn) /\
  no_occurance patn (sublist 0 i text).

Lemma match_pre_derive_inv:
  match_pre -> 
  match_inv 0 0.
Proof.
  intros; unfold match_pre, match_inv in *.
  destruct H as [? [? ?]].
  split. 
  apply match_pre_jrange with (patn:=patn); tauto.
  repeat rewrite Zsublist_nil by lia.
  repeat split.
  apply nil_suffix.
  apply nil_prefix.
  intros. destruct H2 as [? _].
  apply suffix_Zlength; auto.
  unfold no_occurance; intros.
  rewrite Zsublist_of_nil; auto.
Qed.

Lemma match_inv_no_occur(i a: Z):
  0 <= i < Zlength text ->
  no_occurance patn (sublist 0 i text) ->
  0 <= a < Zlength patn ->
  best_partial_match_result 
    patn (sublist 0 (i + 1) text) (sublist 0 a patn) ->
  no_occurance patn (sublist 0 (i + 1) text).
Proof.
  intros Hi H1 H2 H3.
  unfold no_occurance in *; intros i0 Hi0.
  rewrite Zlength_sublist in H1 by lia.
  rewrite Zlength_sublist in Hi0 by lia.
  remember (Zlength patn) as lp.
  destruct (Z_lt_ge_dec i0 (i-lp+1)).
  - rewrite (sublist_split 0 (i+1) i); try lia.
    rewrite sublist_split_app_l; try lia.
    apply H1; lia.
    rewrite Zlength_sublist by lia; lia.
  - assert (i0 = i - lp + 1) by lia; subst i0; clear Hi0 g.
    intros con. subst lp.
    destruct (Z_lt_ge_dec i (Zlength patn - 1)).
    {
      apply (f_equal (@Zlength A)) in con.
      rewrite Zlength_sublist' in con.
      pose proof Zlength_sublist 0 (i+1) text ltac:(lia); lia.
    } 
    apply best_partial_match_iff in con.
    2:{ rewrite Zlength_sublist; lia. }
    replace (i - Zlength patn + 1 + Zlength patn) with (i + 1) in con by lia. 
    rewrite Zsublist_Zsublist00 in con by lia.
    pose proof best_partial_match_inv _ _ _ _ con H3 as Ep.
    apply (f_equal (@Zlength A)) in Ep.
    rewrite Zlength_sublist in Ep; lia.
Qed.

Section match_body.
Context (i j: Z).
Hypothesis Hi: 0 <= i < Zlength text.
Hypothesis H: match_pre.
Hypothesis H0: match_inv i j.

Lemma match_body_cnt_prop:
  Hoare (fun _ => True)
        (x <- match_body default patn text vnext i j;; continue_case x)
        (fun z _ => match_inv (i+1) z).
Proof.
  pose proof H as H'; unfold match_pre in H'.
  pose proof H0 as H0'; unfold match_inv in H0'.
  unfold match_body.
  hoare_auto; try lia.
  eapply Hoare_bind; unfold match_inv in H0. 
  apply inner_loop_prop; try lia.
  split; [lia | tauto].
  intros; hoare_auto.
  destruct H3 as [Ha Hb].
  hnf in H.
  split; [ | split].
  - apply match_inner_post_jrange with (patn:=patn); tauto.
  - tauto.
  - apply match_inv_no_occur with (a:=a); tauto. 
Qed.

Lemma match_body_brk_prop:
  Hoare (fun _ => True)
        (x <- match_body default patn text vnext i j;; break_case x)
        (fun z _ => first_occur patn text z).
Proof.
  intros; unfold match_body.
  rename H0 into H2.
  destruct H as [H3 [H0 H1]]; clear H; rename H3 into H. 
  hoare_auto; try lia.
  eapply Hoare_bind; unfold match_inv in H2. 
  apply inner_loop_prop; try lia.
  split; [lia | tauto].
  intros; prog_nf; hoare_auto.
  destruct H5 as [? H5]. 
  remember (i - Zlength patn + 1) as z.
  replace (i + 1) with (z + Zlength patn)  in H5 by lia.
  rewrite H4 in H5. rewrite (sublist_self patn) in H5 by easy.
  split.
  2:{ replace (z + Zlength patn - 1) with i by lia; tauto. }
  apply best_partial_match_iff in H5; try tauto.
  destruct H5 as [[? _] _].
  apply suffix_Zlength in H5.
  rewrite Zlength_sublist in H5 by lia. lia.
Qed.

Lemma match_body_prop:
  Hoare (fun _ => True)
        (match_body default patn text vnext i j)
        (fun res _ => 
            match res with
            | by_break z => first_occur patn text z
            | by_continue z => match_inv (i+1) z 
            end).
Proof.
  apply Hoare_sum.
  - apply match_body_cnt_prop; auto.
  - apply match_body_brk_prop; auto. 
Qed.

End match_body.

Theorem match_loop_sound:
  patn <> [] ->
  Zlength vnext = Zlength patn ->
  vnext is_prefix_func_of patn ->
  Hoare (fun _ => True) 
        (match_loop default patn text vnext) 
        (fun res _ =>
          match res with
          | Some r => 
              first_occur patn text r
          | None =>
              no_occurance patn text
          end).
Proof.
  intros; unfold match_loop.
  eapply Hoare_bind.
  - eapply (Hoare_range_iter_break
      (match_body default patn text vnext)
      (fun i j _ => match_inv i j)
      (fun _ => True)); intros.
    + apply Zlength_nonneg.
    + apply match_pre_derive_inv; hnf; tauto. 
    + stateless_intros.
      eapply Hoare_cons_post.
      2:{ apply match_body_prop; hnf; auto. }
      intros. destruct a0; auto. eapply H4.
 - intros; destruct a; hoare_step; auto.
   unfold match_inv in H2.
   rewrite sublist_self in H2; tauto.
Qed.

End Match.
