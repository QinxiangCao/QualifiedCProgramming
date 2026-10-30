Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import AUXLib.ListLib.
Local Open Scope Z_scope.

Definition Pre (k : Z) (a : list Z) : Prop :=
  1 <= k <= 200000 /\
  1 <= Zlength a <= 200000 /\
  Forall (fun x => -1000000000 <= x <= 1000000000) a.

#[local] Instance finite_index_pair (n : Z) :
    Finite (fun p : Z * Z => 0 <= fst p < n /\ 0 <= snd p < n) :=
  Finite_prod (fun i : Z => 0 <= i < n) (fun j : Z => 0 <= j < n).

#[local] Instance finite_index_triple (n : Z) :
    Finite (fun q : Z * (Z * Z) =>
      0 <= fst q < n /\ 0 <= fst (snd q) < n /\ 0 <= snd (snd q) < n) :=
  Finite_prod (fun i : Z => 0 <= i < n)
    (fun p : Z * Z => 0 <= fst p < n /\ 0 <= snd p < n).

Definition Spec (k : Z) (a : list Z) (out : Z) : Prop :=
  out = #(fun q : Z * (Z * Z) =>
    (0 <= fst q < Zlength a /\
     0 <= fst (snd q) < Zlength a /\
     0 <= snd (snd q) < Zlength a) /\
    fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
    Znth (fst (snd q)) a 0 = Znth (fst q) a 0 * k /\
    Znth (snd (snd q)) a 0 = Znth (fst (snd q)) a 0 * k).

(** [LowerBoundResult xs x r] gives the mathematical meaning of a lower-bound
    search.  It deliberately describes the partition around [r], rather than
    the binary-search control flow used to find it. *)
Definition LowerBoundResult (xs : list Z) (x r : Z) : Prop :=
  0 <= r <= Zlength xs /\
  (forall i, 0 <= i < r -> Znth i xs 0 < x) /\
  (forall i, r <= i < Zlength xs -> x <= Znth i xs 0).

Definition CompareResult (x y out : Z) : Prop :=
  (x < y /\ out = -1) \/
  (x = y /\ out = 0) \/
  (y < x /\ out = 1).

Definition KeyAt (keys : list Z) (x index : Z) : Prop :=
  0 <= index < Zlength keys /\ Znth index keys 0 = x.

(** [UniqueKeys values keys] says that [keys] is a duplicate-free table for
    exactly the values occurring in [values]. *)
Definition UniqueKeys (values keys : list Z) : Prop :=
  increasing keys /\
  (forall i, 0 <= i < Zlength values ->
    exists j, 0 <= j < Zlength keys /\
      Znth i values 0 = Znth j keys 0) /\
  (forall j, 0 <= j < Zlength keys ->
    exists i, 0 <= i < Zlength values /\
      Znth j keys 0 = Znth i values 0) /\
  (forall p q,
    0 <= p < Zlength keys ->
    0 <= q < Zlength keys ->
    Znth p keys 0 = Znth q keys 0 -> p = q).

(** The processed prefix of the sorted input has already been compressed into
    the leading [used] cells of [storage]. *)
Definition CompressionState
    (sorted : list Z) (processed used : Z) (storage : list Z) : Prop :=
  0 <= processed <= Zlength sorted /\
  0 <= used <= processed /\
  Zlength storage = Zlength sorted /\
  UniqueKeys (sublist 0 processed sorted) (sublist 0 used storage) /\
  (forall i, processed - 1 <= i < Zlength sorted ->
    Znth i storage 0 = Znth i sorted 0).

Definition FrequencyProfile
    (values : list Z) (lo hi : Z) (keys counts : list Z) : Prop :=
  Zlength counts = Zlength keys /\
  0 <= lo <= hi /\ hi <= Zlength values /\
  forall j, 0 <= j < Zlength keys ->
    Znth j counts 0 =
      #(fun i : Z => lo <= i < hi /\
        Znth i values 0 = Znth j keys 0).

Definition RightBuildState
    (values : list Z) (processed : Z) (keys counts : list Z) : Prop :=
  FrequencyProfile values 0 processed keys counts.

(** At loop position [middle], [left] counts the strict prefix, [right]
    counts the current suffix, and [answer] counts exactly the completed
    triples whose middle index is already in the strict prefix. *)
Definition CountingState
    (k : Z) (values : list Z) (middle : Z)
    (keys left right : list Z) (answer : Z) : Prop :=
  FrequencyProfile values 0 middle keys left /\
  FrequencyProfile values middle (Zlength values) keys right /\
  answer = #(fun q : Z * (Z * Z) =>
    (0 <= fst q < Zlength values /\
     0 <= fst (snd q) < Zlength values /\
     0 <= snd (snd q) < Zlength values) /\
    fst (snd q) < middle /\
    fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
    Znth (fst (snd q)) values 0 = Znth (fst q) values 0 * k /\
    Znth (snd (snd q)) values 0 =
      Znth (fst (snd q)) values 0 * k).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.Zquot.
Lemma compression_state_init__compression :
  forall sorted,
    CompressionState sorted 0 0 sorted.
Proof.
  intros sorted.
  unfold CompressionState.
  split.
  - split; [lia | apply Zlength_nonneg].
  - split.
    + split; lia.
    + split.
      * reflexivity.
      * split.
        -- unfold UniqueKeys.
           rewrite !Zsublist_nil by lia.
           split; [simpl; exact I |].
           split.
           ++ intros i Hi. rewrite Zlength_correct in Hi. simpl in Hi. lia.
           ++ split.
              ** intros j Hj. rewrite Zlength_correct in Hj. simpl in Hj. lia.
              ** intros p q Hp Hq _.
                 rewrite !Zlength_correct in Hp, Hq.
                 simpl in Hp, Hq. lia.
        -- intros i _. reflexivity.
Qed.
Lemma increasing_aux_tail_increasing__compression :
  forall l x,
    increasing_aux l x ->
    increasing l.
Proof.
  intros l x Hinc.
  destruct l; simpl in *; auto.
  destruct Hinc as [_ Hrest].
  exact Hrest.
Qed.
Lemma increasing_aux_head_le_all__compression :
  forall l x k,
    increasing_aux l x ->
    0 <= k < Zlength l ->
    x <= Znth k l 0.
Proof.
  induction l; intros x k Hinc Hk.
  - rewrite Zlength_correct in Hk. simpl in Hk. lia.
  - simpl in Hinc.
    destruct Hinc as [Hxa Hrest].
    destruct (Z.eq_dec k 0) as [-> | Hneq].
    + exact Hxa.
    + rewrite Znth_cons by lia.
      eapply Z.le_trans.
      * exact Hxa.
      * apply IHl with (x := a); auto.
        rewrite Zlength_cons in Hk. lia.
Qed.
Lemma increasing_order__compression :
  forall l i j,
    increasing l ->
    0 <= i <= j ->
    j < Zlength l ->
    Znth i l 0 <= Znth j l 0.
Proof.
  induction l as [| a l IH]; intros i j Hinc Hij Hj.
  - rewrite Zlength_correct in Hj. simpl in Hj. lia.
  - destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + subst i.
      destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
      * subst j. reflexivity.
      * rewrite (@Znth_cons Z 0 j a l) by lia.
        apply increasing_aux_head_le_all__compression with (x := a).
        -- simpl in Hinc. exact Hinc.
        -- rewrite Zlength_cons in Hj. lia.
    + destruct (Z.eq_dec j 0) as [Hj0 | Hj0].
      * subst j. lia.
      * rewrite !(@Znth_cons Z 0) by lia.
        apply IH.
        -- apply increasing_aux_tail_increasing__compression with (x := a).
           simpl in Hinc. exact Hinc.
        -- lia.
        -- rewrite Zlength_cons in Hj. lia.
Qed.
Lemma sublist0_extend__compression :
  forall (l : list Z) i,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ (Znth i l 0 :: nil).
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (@sublist_single Z 0 i l) by lia.
  reflexivity.
Qed.
Lemma sublist0_replace_prefix__compression :
  forall (l : list Z) i v,
    0 <= i <= Zlength l ->
    sublist 0 i (replace_Znth i v l) = sublist 0 i l.
Proof.
  intros l i v Hi.
  destruct (Z.eq_dec i (Zlength l)) as [Hi_end | Hi_inside].
  - subst i.
    rewrite replace_Znth_nothing by lia.
    reflexivity.
  - apply (proj2 (list_eq_ext _ _ 0)).
    split.
    + rewrite !Zlength_sublist0; try rewrite Zlength_replace_Znth; lia.
    + intros k Hk.
      rewrite Zlength_sublist0 in Hk by
        (rewrite Zlength_replace_Znth; lia).
      rewrite !Znth_sublist0 by
        (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity.
Qed.
Lemma sublist0_replace_extend__compression :
  forall (l : list Z) i v,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) (replace_Znth i v l) =
      sublist 0 i l ++ (v :: nil).
Proof.
  intros l i v Hi.
  rewrite sublist0_extend__compression by
    (rewrite Zlength_replace_Znth; lia).
  rewrite sublist0_replace_prefix__compression by lia.
  rewrite Znth_replace_Znth_Same by lia.
  reflexivity.
Qed.
Lemma sublist0_In_Znth_exists__compression :
  forall (l : list Z) n x,
    0 <= n <= Zlength l ->
    In x (sublist 0 n l) ->
    exists i, 0 <= i < n /\ Znth i l 0 = x.
Proof.
  intros l n x Hn Hin.
  pose proof (In_nth (sublist 0 n l) x 0 Hin) as [k [Hk Hnth]].
  rewrite sublist_length in Hk by lia.
  exists (Z.of_nat k).
  split.
  - lia.
  - rewrite <- Hnth.
    unfold Znth, sublist.
    rewrite skipn_O.
    replace (Z.to_nat (Z.of_nat k)) with k by lia.
    rewrite nth_firstn by lia.
    reflexivity.
Qed.
Lemma compression_state_insert_new__compression :
  forall sorted processed used storage,
    increasing sorted ->
    processed < Zlength sorted ->
    (processed = 0 \/
      Znth processed storage 0 <> Znth (processed - 1) storage 0) ->
    CompressionState sorted processed used storage ->
    CompressionState sorted (processed + 1) (used + 1)
      (replace_Znth used (Znth processed storage 0) storage).
Proof.
  intros sorted processed used storage Hsorted Hprocessed Hnew Hstate.
  unfold CompressionState in Hstate |- *.
  destruct Hstate as
    [Hprocessed_bounds [Hused_bounds [Hlength [Hkeys Htail]]]].
  set (current := Znth processed storage 0).
  assert (Hused_storage : 0 <= used < Zlength storage) by lia.
  assert (Hcurrent_sorted : current = Znth processed sorted 0).
  {
    unfold current.
    apply Htail. lia.
  }
  assert (Hprior_lt :
    forall index, 0 <= index < processed ->
      Znth index sorted 0 < current).
  {
    intros index Hindex.
    destruct (Z.eq_dec processed 0) as [Hzero | Hnonzero].
    - lia.
    - assert (Hindex_le :
        Znth index sorted 0 <= Znth (processed - 1) sorted 0).
      {
        eapply increasing_order__compression; eauto; lia.
      }
      assert (Hprev_le :
        Znth (processed - 1) sorted 0 <= Znth processed sorted 0).
      {
        eapply increasing_order__compression; eauto; lia.
      }
      assert (Hprev_storage :
        Znth (processed - 1) storage 0 =
        Znth (processed - 1) sorted 0) by
        (apply Htail; lia).
      destruct Hnew as [Hbad | Hneq]; [congruence |].
      unfold current in *.
      lia.
  }
  unfold UniqueKeys in Hkeys.
  destruct Hkeys as [Hkey_inc [Hcover [Hback Hunique]]].
  assert (Hold_lt :
    forall j, 0 <= j < Zlength (sublist 0 used storage) ->
      Znth j (sublist 0 used storage) 0 < current).
  {
    intros j Hj.
    destruct (Hback j Hj) as [index [Hindex Heq]].
    rewrite Zlength_sublist0 in Hindex by lia.
    rewrite (@Znth_sublist0 Z 0 index processed sorted) in Heq by lia.
    rewrite (@Znth_sublist0 Z 0 j used storage) in Heq by
      (rewrite Zlength_sublist0 in Hj by lia; lia).
    rewrite (@Znth_sublist0 Z 0 j used storage) by
      (rewrite Zlength_sublist0 in Hj by lia; lia).
    rewrite Heq.
    apply Hprior_lt. exact Hindex.
  }
  split.
  - lia.
  - split.
    + lia.
    + split.
      * rewrite Zlength_replace_Znth. exact Hlength.
      * split.
        -- unfold UniqueKeys.
           rewrite (sublist0_extend__compression sorted processed) by lia.
           rewrite (sublist0_replace_extend__compression storage used current)
             by lia.
           split.
           ++ apply (proj2 (increasing_app _ _)).
              split; [exact Hkey_inc |].
              split; [simpl; exact I |].
              intros a b Ha Hb.
              simpl in Hb. destruct Hb as [Hb | Hb]; [subst b | contradiction].
              destruct (sublist0_In_Znth_exists__compression
                storage used a ltac:(lia) Ha) as [j [Hj Hja]].
              rewrite <- Hja.
              apply Z.lt_le_incl.
              rewrite <- (@Znth_sublist0 Z 0 j used storage) by lia.
              apply Hold_lt.
              rewrite Zlength_sublist0 by lia. exact Hj.
           ++ split.
              ** intros index Hindex.
                 rewrite Zlength_app_cons in Hindex.
                 rewrite Zlength_sublist0 in Hindex by lia.
                 destruct (Z_lt_ge_dec index processed) as [Hlt | Hge].
                 --- specialize (Hcover index).
                     rewrite Zlength_sublist0 in Hcover by lia.
                     destruct (Hcover ltac:(lia)) as [j [Hj Heq]].
                     exists j. split.
                     +++ rewrite Zlength_app_cons.
                         rewrite Zlength_sublist0 by lia.
                         rewrite Zlength_sublist0 in Hj by lia. lia.
                     +++ rewrite (@app_Znth1 Z 0
                           (sublist 0 used storage)
                           (current :: nil) j) by exact Hj.
                         rewrite app_Znth1 by
                           (rewrite Zlength_sublist0; lia).
                         exact Heq.
                 --- assert (Hindex_eq : index = processed) by lia.
                     subst index.
                     exists used. split.
                     +++ rewrite Zlength_app_cons.
                         rewrite Zlength_sublist0 by lia. lia.
                     +++ rewrite !app_Znth2 by
                           (rewrite Zlength_sublist0; lia).
                         rewrite !Zlength_sublist0 by lia.
                         replace (used - used) with 0 by lia.
                         replace (processed - processed) with 0 by lia.
                         rewrite !Znth0_cons.
                         symmetry. exact Hcurrent_sorted.
              ** split.
                 --- intros j Hj.
                     rewrite Zlength_app_cons in Hj.
                     rewrite Zlength_sublist0 in Hj by lia.
                     destruct (Z_lt_ge_dec j used) as [Hlt | Hge].
                     +++ specialize (Hback j).
                         rewrite Zlength_sublist0 in Hback by lia.
                         destruct (Hback ltac:(lia)) as [index [Hindex Heq]].
                         exists index. split.
                         *** rewrite Zlength_app_cons.
                             rewrite Zlength_sublist0 by lia.
                             rewrite Zlength_sublist0 in Hindex by lia.
                             lia.
                         *** rewrite !app_Znth1 by
                               (try rewrite Zlength_sublist0; lia).
                             rewrite app_Znth1 by
                               exact Hindex.
                             exact Heq.
                     +++ assert (Hj_eq : j = used) by lia.
                         subst j.
                         exists processed. split.
                         *** rewrite Zlength_app_cons.
                             rewrite Zlength_sublist0 by lia. lia.
                         *** rewrite !app_Znth2 by
                               (rewrite Zlength_sublist0; lia).
                             rewrite !Zlength_sublist0 by lia.
                             replace (used - used) with 0 by lia.
                             replace (processed - processed) with 0 by lia.
                             rewrite !Znth0_cons.
                             exact Hcurrent_sorted.
                 --- intros p q Hp Hq Heq.
                     rewrite !Zlength_app_cons in Hp, Hq.
                     rewrite !Zlength_sublist0 in Hp, Hq by lia.
                     destruct (Z_lt_ge_dec p used) as [Hpold | Hpnew];
                       destruct (Z_lt_ge_dec q used) as [Hqold | Hqnew].
                     +++ apply Hunique.
                         *** rewrite Zlength_sublist0 by lia. lia.
                         *** rewrite Zlength_sublist0 by lia. lia.
                         *** rewrite !app_Znth1 in Heq by
                               (rewrite Zlength_sublist0; lia).
                             exact Heq.
                     +++ assert (Hqeq : q = used) by lia. subst q.
                         rewrite app_Znth1 in Heq by
                           (rewrite Zlength_sublist0; lia).
                         rewrite app_Znth2 in Heq by
                           (rewrite Zlength_sublist0; lia).
                         rewrite Zlength_sublist0 in Heq by lia.
                         replace (used - used) with 0 in Heq by lia.
                         rewrite Znth0_cons in Heq.
                         specialize (Hold_lt p ltac:(rewrite Zlength_sublist0; lia)).
                         lia.
                     +++ assert (Hpeq : p = used) by lia. subst p.
                         rewrite app_Znth2 in Heq by
                           (rewrite Zlength_sublist0; lia).
                         rewrite app_Znth1 in Heq by
                           (rewrite Zlength_sublist0; lia).
                         rewrite Zlength_sublist0 in Heq by lia.
                         replace (used - used) with 0 in Heq by lia.
                         rewrite Znth0_cons in Heq.
                         specialize (Hold_lt q ltac:(rewrite Zlength_sublist0; lia)).
                         lia.
                     +++ lia.
        -- intros index Hindex.
           destruct (Z.eq_dec index used) as [Heq | Hneq].
           ++ subst index.
              rewrite Znth_replace_Znth_Same by lia.
              assert (Hused_eq : used = processed) by lia.
              subst used.
              exact Hcurrent_sorted.
           ++ rewrite Znth_replace_Znth_Diff by lia.
              apply Htail. lia.
Qed.
Lemma compression_state_skip_duplicate__compression :
  forall sorted processed used storage,
    0 < processed < Zlength sorted ->
    Znth processed storage 0 = Znth (processed - 1) storage 0 ->
    CompressionState sorted processed used storage ->
    CompressionState sorted (processed + 1) used storage.
Proof.
  intros sorted processed used storage Hprocessed Hdup Hstate.
  unfold CompressionState in Hstate |- *.
  destruct Hstate as
    [Hprocessed_bounds [Hused_bounds [Hlength [Hkeys Htail]]]].
  assert (Hcur : Znth processed storage 0 = Znth processed sorted 0) by
    (apply Htail; lia).
  assert (Hprev :
    Znth (processed - 1) storage 0 = Znth (processed - 1) sorted 0) by
    (apply Htail; lia).
  assert (Hsorted_dup :
    Znth processed sorted 0 = Znth (processed - 1) sorted 0) by
    congruence.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * exact Hlength.
      * split.
        -- unfold UniqueKeys in Hkeys |- *.
           destruct Hkeys as [Hincreasing [Hcover [Hback Hunique]]].
           split; [exact Hincreasing |].
           split.
           ++ intros index Hindex.
              rewrite Zlength_sublist0 in Hindex by lia.
              destruct (Z_lt_ge_dec index processed) as [Hlt | Hge].
              ** specialize (Hcover index).
                 rewrite Zlength_sublist0 in Hcover by lia.
                 destruct (Hcover ltac:(lia)) as [j [Hj Heq]].
                 exists j. split.
                 --- exact Hj.
                 --- rewrite !Znth_sublist0 in * by lia.
                     exact Heq.
              ** assert (Hindex_eq : index = processed) by lia.
                 subst index.
                 specialize (Hcover (processed - 1)).
                 rewrite Zlength_sublist0 in Hcover by lia.
                 destruct (Hcover ltac:(lia)) as [j [Hj Heq]].
                 exists j. split.
                 --- exact Hj.
                 --- rewrite !Znth_sublist0 in * by lia.
                     rewrite Hsorted_dup.
                     exact Heq.
           ++ split.
              ** intros j Hj.
                 destruct (Hback j Hj) as [index [Hindex Heq]].
                 exists index. split.
                 --- rewrite Zlength_sublist0 by lia.
                     rewrite Zlength_sublist0 in Hindex by lia.
                     lia.
                 --- rewrite (@Znth_sublist0 Z 0 index (processed + 1) sorted)
                       by (rewrite Zlength_sublist0 in Hindex by lia; lia).
                     rewrite (@Znth_sublist0 Z 0 index processed sorted) in Heq
                       by (rewrite Zlength_sublist0 in Hindex by lia; lia).
                     exact Heq.
              ** exact Hunique.
        -- intros index Hindex.
           apply Htail. lia.
Qed.
Lemma compression_state_finish__compression :
  forall sorted used storage,
    1 <= Zlength sorted ->
    CompressionState sorted (Zlength sorted) used storage ->
    1 <= used <= Zlength sorted /\
    Zlength (sublist 0 used storage) = used /\
    Zlength (sublist used (Zlength sorted) storage) =
      Zlength sorted - used /\
    UniqueKeys sorted (sublist 0 used storage).
Proof.
  intros sorted used storage Hnonempty Hstate.
  unfold CompressionState in Hstate.
  destruct Hstate as
    [Hprocessed [Hused [Hlength [Hkeys Htail]]]].
  rewrite sublist_self in Hkeys by reflexivity.
  assert (Hused_pos : 1 <= used).
  {
    unfold UniqueKeys in Hkeys.
    destruct Hkeys as [_ [Hcover _]].
    specialize (Hcover 0 ltac:(lia)).
    destruct Hcover as [j [Hj _]].
    rewrite Zlength_sublist0 in Hj by lia.
    lia.
  }
  split; [lia |].
  split.
  - rewrite Zlength_sublist0 by lia. reflexivity.
  - split.
    + rewrite Zlength_sublist by lia. reflexivity.
    + exact Hkeys.
Qed.
Lemma Znth_In_bounds__compression :
  forall (l : list Z) i,
    0 <= i < Zlength l ->
    In (Znth i l 0) l.
Proof.
  intros l i Hi.
  apply Znth_In_Zlength.
  exact Hi.
Qed.
Lemma In_Znth_exists__compression :
  forall (l : list Z) x,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros l x Hin.
  pose proof (In_nth l x 0 Hin) as [i [Hi Hnth]].
  exists (Z.of_nat i).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth.
    replace (Z.to_nat (Z.of_nat i)) with i by lia.
    exact Hnth.
Qed.
Lemma unique_keys_bounds__compression :
  forall values sorted keys lo hi,
    Forall (fun x => lo <= x <= hi) values ->
    Permutation values sorted ->
    UniqueKeys sorted keys ->
    forall j, 0 <= j < Zlength keys ->
      lo <= Znth j keys 0 <= hi.
Proof.
  intros values sorted keys lo hi Hbounds Hperm Hkeys j Hj.
  unfold UniqueKeys in Hkeys.
  destruct Hkeys as [_ [_ [Hback _]]].
  destruct (Hback j Hj) as [i [Hi Heq]].
  rewrite Heq.
  apply Forall_forall with (x := Znth i sorted 0) in Hbounds.
  - exact Hbounds.
  - eapply Permutation_in.
    + apply Permutation_sym. exact Hperm.
    + apply Znth_In_bounds__compression. exact Hi.
Qed.
Lemma In_Znth_Zlength__counting_init :
  forall (l : list Z) x,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros l x Hin.
  pose proof (In_nth l x 0 Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth.
    replace (Z.to_nat (Z.of_nat n)) with n by lia.
    exact Hnth.
Qed.
Lemma set_card_empty__right_frequency :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma set_card_Z_as_sum__right_frequency :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__right_frequency :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange Htrue.
  rewrite !set_card_Z_as_sum__right_frequency.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)); [reflexivity | contradiction].
Qed.
Lemma set_card_Z_extend_false__right_frequency :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange Hfalse.
  rewrite !set_card_Z_as_sum__right_frequency.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)); [contradiction | lia].
Qed.
Lemma lower_bound_unique_key__right_frequency :
  forall values sorted keys i r,
    0 <= i < Zlength values ->
    Permutation values sorted ->
    UniqueKeys sorted keys ->
    LowerBoundResult keys (Znth i values 0) r ->
    KeyAt keys (Znth i values 0) r.
Proof.
  intros values sorted keys i r Hi Hperm Hkeys Hlower.
  assert (Hin_values : In (Znth i values 0) values).
  {
    unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
  }
  assert (Hin_sorted : In (Znth i values 0) sorted).
  { eapply Permutation_in; eauto. }
  destruct (In_nth sorted (Znth i values 0) 0 Hin_sorted)
    as [p [Hp Hnth]].
  assert (HpZ : 0 <= Z.of_nat p < Zlength sorted).
  { rewrite Zlength_correct. lia. }
  assert (Hsorted_value :
    Znth (Z.of_nat p) sorted 0 = Znth i values 0).
  {
    unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
  }
  unfold UniqueKeys in Hkeys.
  destruct Hkeys as [Hincreasing [Hcover [_ Hunique]]].
  destruct (Hcover (Z.of_nat p) HpZ) as [j [Hj Hkeyj]].
  assert (Hkey_value : Znth j keys 0 = Znth i values 0) by congruence.
  unfold LowerBoundResult in Hlower.
  destruct Hlower as [Hr [Hbefore Hafter]].
  assert (Hrj : r = j).
  {
    destruct (Z_lt_ge_dec j r) as [Hjr | Hrj].
    - specialize (Hbefore j ltac:(lia)). lia.
    - destruct (Z.eq_dec r j) as [Heq | Hneq]; [exact Heq |].
      assert (Hr_inside : r < Zlength keys) by lia.
      specialize (Hafter r ltac:(lia)).
      pose proof (proj2 (mono_nondec_iff_increasing keys) Hincreasing)
        as Hmono.
      unfold mono_nondec in Hmono.
      specialize (Hmono r j ltac:(lia) ltac:(lia) ltac:(lia)).
      apply Hunique; try lia.
  }
  subst j.
  unfold KeyAt.
  split; [lia | exact Hkey_value].
Qed.
Lemma frequency_profile_increment__right_frequency :
  forall values lo hi keys counts source ix,
    hi < Zlength values ->
    UniqueKeys source keys ->
    KeyAt keys (Znth hi values 0) ix ->
    FrequencyProfile values lo hi keys counts ->
    FrequencyProfile values lo (hi + 1) keys
      (replace_Znth ix (Znth ix counts 0 + 1) counts).
Proof.
  intros values lo hi keys counts source ix Hinside Hunique Hkey Hprofile.
  unfold FrequencyProfile in Hprofile |- *.
  destruct Hprofile as [Hlength [[Hlo Hlohi] [Hhi Hcounts]]].
  unfold KeyAt in Hkey.
  destruct Hkey as [Hix Hixvalue].
  unfold UniqueKeys in Hunique.
  destruct Hunique as [_ [_ [_ Hindices]]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlength.
  - split; [lia |].
    split; [lia |].
    intros j Hj.
    specialize (Hcounts j Hj).
    destruct (Z.eq_dec j ix) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      rewrite set_card_Z_extend_true__right_frequency by
        (try lia; symmetry; exact Hixvalue).
      lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite set_card_Z_extend_false__right_frequency by
        (try lia; intro Heq; apply Hneq; apply Hindices; try lia; congruence).
      exact Hcounts.
Qed.
Lemma set_card_empty__counting_init :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma set_card_positive_of_member__counting_init :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) (x : A),
    P x -> 0 < @set_card A P FP.
Proof.
  intros A P FP x Hx.
  assert (Hnonneg : 0 <= @set_card A P FP).
  {
    unfold set_card.
    apply SumLib.Sum.sum_nonneg.
    intros y Hy. lia.
  }
  assert (Hnonzero : @set_card A P FP <> 0).
  {
    intro Hzero.
    unfold set_card in Hzero.
    pose proof (@SumLib.Sum.sum_nonneg_eq_zero_elim
      A P FP (fun _ => 1)
      ltac:(intros y Hy; lia) Hzero x Hx) as Hone.
    lia.
  }
  lia.
Qed.
Lemma counting_state_zero__counting_init :
  forall k values keys left right,
    FrequencyProfile values 0 0 keys left ->
    FrequencyProfile values 0 (Zlength values) keys right ->
    CountingState k values 0 keys left right 0.
Proof.
  intros k values keys left right Hleft Hright.
  unfold CountingState.
  split; [exact Hleft |].
  split; [exact Hright |].
  symmetry.
  apply set_card_empty__counting_init.
  intros [x [y z]] Hq. simpl in Hq. lia.
Qed.
Lemma lower_bound_key_at__counting_init :
  forall values sorted keys i r,
    0 <= i < Zlength values ->
    Permutation values sorted ->
    UniqueKeys sorted keys ->
    LowerBoundResult keys (Znth i values 0) r ->
    KeyAt keys (Znth i values 0) r.
Proof.
  intros values sorted keys i r Hi Hperm Hkeys Hlower.
  assert (Hin_values : In (Znth i values 0) values).
  {
    unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
  }
  assert (Hin_sorted : In (Znth i values 0) sorted).
  {
    eapply Permutation_in; eauto.
  }
  destruct (In_Znth_Zlength__counting_init
    sorted (Znth i values 0) Hin_sorted) as [p [Hp Heqp]].
  unfold UniqueKeys in Hkeys.
  destruct Hkeys as [Hincreasing [Hcover _]].
  destruct (Hcover p Hp) as [j [Hj Heqj]].
  unfold LowerBoundResult in Hlower.
  destruct Hlower as [Hr [Hbefore Hafter]].
  assert (Hrj : r <= j).
  {
    destruct (Z_lt_ge_dec j r); [|lia].
    specialize (Hbefore j ltac:(lia)).
    lia.
  }
  assert (Horder : Znth r keys 0 <= Znth j keys 0).
  {
    pose proof (proj2 (mono_nondec_iff_increasing keys) Hincreasing)
      as Hmono.
    unfold mono_nondec in Hmono.
    apply Hmono; lia.
  }
  specialize (Hafter r ltac:(lia)).
  unfold KeyAt.
  split; [lia |].
  lia.
Qed.
Lemma frequency_profile_current_positive__counting_init :
  forall values i keys counts r,
    0 <= i < Zlength values ->
    KeyAt keys (Znth i values 0) r ->
    FrequencyProfile values i (Zlength values) keys counts ->
    1 <= Znth r counts 0.
Proof.
  intros values i keys counts r Hi Hkey Hprofile.
  unfold KeyAt in Hkey.
  unfold FrequencyProfile in Hprofile.
  destruct Hkey as [Hr Hvalue].
  destruct Hprofile as [_ [Hlo [Hhi Hcounts]]].
  specialize (Hcounts r Hr).
  rewrite Hcounts.
  assert (Hmember : i <= i < Zlength values /\
    Znth i values 0 = Znth r keys 0).
  { split; [lia |]. symmetry. exact Hvalue. }
  pose proof (set_card_positive_of_member__counting_init
    (fun i0 : Z => i <= i0 < Zlength values /\
      Znth i0 values 0 = Znth r keys 0) _ i Hmember) as Hpositive.
  lia.
Qed.
Lemma fold_ones_length__counting_transitions :
  forall {A : Type} (xs : list A),
    List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
      Z.of_nat (List.length xs).
Proof.
  intros A xs.
  induction xs as [|x xs IH]; [reflexivity |].
  change (1 + List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
    Z.of_nat (S (List.length xs))).
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Lemma set_card_as_Zlength__counting_transitions :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    @set_card A P FP = Z.of_nat (List.length (@enum A P FP)).
Proof.
  intros A P FP. unfold set_card, SumLib.Sum.sum.
  apply fold_ones_length__counting_transitions.
Qed.
Lemma set_card_extensional__counting_transitions :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  rewrite !set_card_as_Zlength__counting_transitions.
  f_equal.
  apply Permutation_length.
  apply NoDup_Permutation.
  - exact (@enum_nodup A P FP).
  - exact (@enum_nodup A Q FQ).
  - intro x.
    rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
    apply Hequiv.
Qed.
Lemma set_card_empty__counting_transitions :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  rewrite set_card_as_Zlength__counting_transitions.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso. apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)). rewrite Hen. simpl. auto.
Qed.
Lemma set_card_nonnegative__counting_transitions :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    0 <= @set_card A P FP.
Proof.
  intros A P FP. rewrite set_card_as_Zlength__counting_transitions. lia.
Qed.
Lemma set_card_subset_le__counting_transitions :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x -> Q x) ->
    @set_card A P FP <= @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hsub.
  rewrite !set_card_as_Zlength__counting_transitions.
  apply Nat2Z.inj_le.
  apply NoDup_incl_length.
  - exact (@enum_nodup A P FP).
  - intros x Hx.
    apply (proj1 (@enum_ok A Q FQ x)), Hsub.
    apply (proj2 (@enum_ok A P FP x)); exact Hx.
Qed.
Lemma set_card_disjoint_union__counting_transitions :
  forall {A : Type} (R P Q : A -> Prop)
      (FR : Finite R) (FP : Finite P) (FQ : Finite Q),
    (forall x, R x <-> P x \/ Q x) ->
    (forall x, ~ (P x /\ Q x)) ->
    @set_card A R FR = @set_card A P FP + @set_card A Q FQ.
Proof.
  intros A R P Q FR FP FQ Hunion Hdisjoint.
  rewrite !set_card_as_Zlength__counting_transitions.
  rewrite <- Nat2Z.inj_add. f_equal.
  rewrite <- length_app.
  apply Permutation_length.
  apply NoDup_Permutation.
  - exact (@enum_nodup A R FR).
  - apply NoDup_app.
    + exact (@enum_nodup A P FP).
    + exact (@enum_nodup A Q FQ).
    + intros x HxP HxQ.
      apply (Hdisjoint x).
      split.
      * apply (proj2 (@enum_ok A P FP x)); exact HxP.
      * apply (proj2 (@enum_ok A Q FQ x)); exact HxQ.
  - intro x. rewrite in_app_iff.
    rewrite <- (@enum_ok A R FR x), <- (@enum_ok A P FP x),
      <- (@enum_ok A Q FQ x).
    exact (Hunion x).
Qed.
Lemma set_card_bijection__counting_transitions :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q) (f : A -> B),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> exists x, P x /\ f x = y) ->
    (forall x y, P x -> P y -> f x = f y -> x = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmap Hsurj Hinj.
  rewrite !set_card_as_Zlength__counting_transitions.
  f_equal.
  rewrite <- length_map with (f := f) (l := @enum A P FP).
  apply Permutation_length.
  apply NoDup_Permutation.
  - apply Injective_map_NoDup_in.
    + intros x y Hx Hy Hxy. apply Hinj.
      * apply (proj2 (@enum_ok A P FP x)); exact Hx.
      * apply (proj2 (@enum_ok A P FP y)); exact Hy.
      * exact Hxy.
    + exact (@enum_nodup A P FP).
  - exact (@enum_nodup B Q FQ).
  - intro y. rewrite in_map_iff, <- (@enum_ok B Q FQ y).
    split.
    + intros [x [<- Hx]]. apply Hmap.
      apply (proj2 (@enum_ok A P FP x)); exact Hx.
    + intro Hy. destruct (Hsurj y Hy) as [x [Hx Hxy]].
      exists x. split; [exact Hxy |].
      apply (proj1 (@enum_ok A P FP x)); exact Hx.
Qed.
Lemma set_card_product__counting_transitions :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q),
    @set_card (A * B) (fun p => P (fst p) /\ Q (snd p))
      (@Finite_prod A B P Q FP FQ) =
    @set_card A P FP * @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ.
  rewrite !set_card_as_Zlength__counting_transitions.
  assert (Hprod : forall (xs : list A) (ys : list B),
    List.length (list_prod xs ys) =
      (List.length xs * List.length ys)%nat).
  { intros xs ys. induction xs as [|x xs IH]; simpl; [reflexivity |].
    rewrite length_app, length_map, IH. lia. }
  change (Z.of_nat (List.length
      (list_prod (@enum A P FP) (@enum B Q FQ))) =
    Z.of_nat (List.length (@enum A P FP)) *
      Z.of_nat (List.length (@enum B Q FQ))).
  rewrite Hprod, Nat2Z.inj_mul. reflexivity.
Qed.
Lemma set_card_Z_as_sum__counting_transitions :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_interval_step__counting_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) +
      (if prop_dec (P high) then 1 else 0).
Proof.
  intros low high P Hrange.
  rewrite !set_card_Z_as_sum__counting_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  reflexivity.
Qed.
Lemma set_card_interval_drop_left__counting_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low < high ->
    #(fun z : Z => low <= z < high /\ P z) =
      #(fun z : Z => low + 1 <= z < high /\ P z) +
      (if prop_dec (P low) then 1 else 0).
Proof.
  intros low high P Hrange.
  rewrite !set_card_Z_as_sum__counting_transitions.
  rewrite SumLib.ZRange.sum_Z_range_cons by exact Hrange.
  ring.
Qed.
Lemma frequency_profile_replace_increment__counting_transitions :
  forall values lo hi keys counts source ix,
    hi < Zlength values ->
    UniqueKeys source keys ->
    KeyAt keys (Znth hi values 0) ix ->
    FrequencyProfile values lo hi keys counts ->
    FrequencyProfile values lo (hi + 1) keys
      (replace_Znth ix (Znth ix counts 0 + 1) counts).
Proof.
  intros values lo hi keys counts source ix Hinside Hunique Hkey Hprofile.
  unfold FrequencyProfile in Hprofile |- *.
  destruct Hprofile as [Hlength [[Hlo Hlohi] [Hhi Hcounts]]].
  unfold KeyAt in Hkey.
  destruct Hkey as [Hix Hixvalue].
  unfold UniqueKeys in Hunique.
  destruct Hunique as [_ [_ [_ Hindices]]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlength.
  - split; [lia |].
    split; [lia |].
    intros j Hj.
    specialize (Hcounts j Hj).
    rewrite (set_card_interval_step__counting_transitions lo hi
      (fun z => Znth z values 0 = Znth j keys 0)) by lia.
    destruct (Z.eq_dec j ix) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      destruct (prop_dec (Znth hi values 0 = Znth ix keys 0))
        as [Heq | Hneqvalue].
      * lia.
      * exfalso. apply Hneqvalue. symmetry. exact Hixvalue.
    + rewrite Znth_replace_Znth_Diff by lia.
      destruct (prop_dec (Znth hi values 0 = Znth j keys 0)) as [Heq | _].
      * exfalso. apply Hneq. apply Hindices.
        -- lia.
        -- lia.
        -- congruence.
      * lia.
Qed.
Lemma frequency_profile_replace_decrement__counting_transitions :
  forall values lo hi keys counts source ix,
    lo < hi ->
    UniqueKeys source keys ->
    KeyAt keys (Znth lo values 0) ix ->
    FrequencyProfile values lo hi keys counts ->
    FrequencyProfile values (lo + 1) hi keys
      (replace_Znth ix (Znth ix counts 0 - 1) counts).
Proof.
  intros values lo hi keys counts source ix Hinside Hunique Hkey Hprofile.
  unfold FrequencyProfile in Hprofile |- *.
  destruct Hprofile as [Hlength [[Hlo Hlohi] [Hhi Hcounts]]].
  unfold KeyAt in Hkey.
  destruct Hkey as [Hix Hixvalue].
  unfold UniqueKeys in Hunique.
  destruct Hunique as [_ [_ [_ Hindices]]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlength.
  - split; [lia |].
    split; [lia |].
    intros j Hj.
    specialize (Hcounts j Hj).
    rewrite (set_card_interval_drop_left__counting_transitions lo hi
      (fun z => Znth z values 0 = Znth j keys 0)) in Hcounts by lia.
    destruct (Z.eq_dec j ix) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      destruct (prop_dec (Znth lo values 0 = Znth ix keys 0))
        as [Heq | Hneqvalue].
      * lia.
      * exfalso. apply Hneqvalue. symmetry. exact Hixvalue.
    + rewrite Znth_replace_Znth_Diff by lia.
      destruct (prop_dec (Znth lo values 0 = Znth j keys 0)) as [Heq | _].
      * exfalso. apply Hneq. apply Hindices.
        -- lia.
        -- lia.
        -- congruence.
      * lia.
Qed.
Lemma lower_bound_absent_from_values__counting_transitions :
  forall values sorted keys target r,
    Permutation values sorted ->
    UniqueKeys sorted keys ->
    LowerBoundResult keys target r ->
    (r = Zlength keys \/ Znth r keys 0 <> target) ->
    forall index, 0 <= index < Zlength values ->
      Znth index values 0 <> target.
Proof.
  intros values sorted keys target r Hperm Hunique Hlower Hmiss index Hindex Heq.
  assert (Hin_values : In target values).
  {
    rewrite <- Heq.
    unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hindex.
    lia.
  }
  assert (Hin_sorted : In target sorted).
  { eapply Permutation_in; eauto. }
  destruct (In_nth sorted target 0 Hin_sorted) as [m [Hm Hnth]].
  unfold UniqueKeys in Hunique.
  destruct Hunique as [Hincreasing [Hcover _]].
  specialize (Hcover (Z.of_nat m)).
  assert (HmZ : 0 <= Z.of_nat m < Zlength sorted).
  { rewrite Zlength_correct. lia. }
  specialize (Hcover HmZ).
  destruct Hcover as [j [Hj Hkeyj]].
  assert (Hsorted_target : Znth (Z.of_nat m) sorted 0 = target).
  {
    unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
  }
  assert (Hkey_target : Znth j keys 0 = target) by congruence.
  unfold LowerBoundResult in Hlower.
  destruct Hlower as [Hr [Hbefore Hafter]].
  destruct (Z_lt_ge_dec j r) as [Hjr | Hrj].
  - specialize (Hbefore j ltac:(lia)). lia.
  - destruct Hmiss as [Hr_end | Hr_mismatch].
    + lia.
    + assert (Hr_inside : r < Zlength keys) by lia.
      specialize (Hafter r ltac:(lia)).
      pose proof (proj2 (mono_nondec_iff_increasing keys) Hincreasing)
        as Hmono.
      unfold mono_nondec in Hmono.
      specialize (Hmono r j ltac:(lia) ltac:(lia) ltac:(lia)).
      lia.
Qed.
Lemma Zrange_aux_length__counting_transitions :
  forall low m, List.length (Zrange_aux low m) = m.
Proof.
  intros low m. revert low. induction m; intros; simpl; congruence.
Qed.
Lemma set_card_Z_range__counting_transitions :
  forall low high, low <= high ->
    @set_card Z (fun z => low <= z < high) (finite_Z_range low high) =
      high - low.
Proof.
  intros low high Hrange.
  rewrite set_card_as_Zlength__counting_transitions.
  change (Z.of_nat (List.length (Zrange low high)) = high - low).
  unfold Zrange.
  rewrite Zrange_aux_length__counting_transitions, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma set_card_bounded_triples__counting_transitions :
  forall n, 0 <= n ->
    #(fun q : Z * (Z * Z) =>
      0 <= fst q < n /\
      0 <= fst (snd q) < n /\
      0 <= snd (snd q) < n) = n * n * n.
Proof.
  intros n Hn.
  change
    (@set_card (Z * (Z * Z))
      (fun q : Z * (Z * Z) =>
        0 <= fst q < n /\
        0 <= fst (snd q) < n /\
        0 <= snd (snd q) < n)
      (finite_index_triple n) = n * n * n).
  transitivity
    (@set_card Z (fun x : Z => 0 <= x < n) (finite_Z_range 0 n) *
     @set_card (Z * Z)
       (fun p : Z * Z => 0 <= fst p < n /\ 0 <= snd p < n)
       (finite_index_pair n)).
  - exact (@set_card_product__counting_transitions
      Z (Z * Z)
      (fun x : Z => 0 <= x < n)
      (fun p : Z * Z => 0 <= fst p < n /\ 0 <= snd p < n)
      (finite_Z_range 0 n) (finite_index_pair n)).
  - unfold finite_index_pair.
    rewrite (@set_card_product__counting_transitions
      Z Z
      (fun x : Z => 0 <= x < n)
      (fun x : Z => 0 <= x < n)
      (finite_Z_range 0 n) (finite_Z_range 0 n)).
  rewrite !set_card_Z_range__counting_transitions by lia.
  ring.
Qed.
Lemma set_card_counting_middle_step__counting_transitions :
  forall k values i,
    0 <= i < Zlength values ->
    #(fun q : Z * (Z * Z) =>
      (0 <= fst q < Zlength values /\
       0 <= fst (snd q) < Zlength values /\
       0 <= snd (snd q) < Zlength values) /\
      fst (snd q) < i + 1 /\
      fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
      Znth (fst (snd q)) values 0 = Znth (fst q) values 0 * k /\
      Znth (snd (snd q)) values 0 =
        Znth (fst (snd q)) values 0 * k) =
    #(fun q : Z * (Z * Z) =>
      (0 <= fst q < Zlength values /\
       0 <= fst (snd q) < Zlength values /\
       0 <= snd (snd q) < Zlength values) /\
      fst (snd q) < i /\
      fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
      Znth (fst (snd q)) values 0 = Znth (fst q) values 0 * k /\
      Znth (snd (snd q)) values 0 =
        Znth (fst (snd q)) values 0 * k) +
    #(fun q : Z * (Z * Z) =>
      (0 <= fst q < Zlength values /\
       0 <= fst (snd q) < Zlength values /\
       0 <= snd (snd q) < Zlength values) /\
      fst (snd q) = i /\
      fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
      Znth (fst (snd q)) values 0 = Znth (fst q) values 0 * k /\
      Znth (snd (snd q)) values 0 =
        Znth (fst (snd q)) values 0 * k).
Proof.
  intros k values i Hi.
  apply set_card_disjoint_union__counting_transitions.
  - intros [x [y z]]. simpl. intuition lia.
  - intros [x [y z]]. simpl. intuition lia.
Qed.
Lemma counting_middle_card_product__counting_transitions :
  forall k values i,
    0 <= i < Zlength values ->
    #(fun q : Z * (Z * Z) =>
      (0 <= fst q < Zlength values /\
       0 <= fst (snd q) < Zlength values /\
       0 <= snd (snd q) < Zlength values) /\
      fst (snd q) = i /\
      fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
      Znth (fst (snd q)) values 0 = Znth (fst q) values 0 * k /\
      Znth (snd (snd q)) values 0 =
        Znth (fst (snd q)) values 0 * k) =
    #(fun x : Z => 0 <= x < i /\
      Znth i values 0 = Znth x values 0 * k) *
    #(fun z : Z => i + 1 <= z < Zlength values /\
      Znth z values 0 = Znth i values 0 * k).
Proof.
  intros k values i Hi.
  transitivity
    (@set_card (Z * Z)
      (fun p : Z * Z =>
        (0 <= fst p < i /\ Znth i values 0 = Znth (fst p) values 0 * k) /\
        (i + 1 <= snd p < Zlength values /\
          Znth (snd p) values 0 = Znth i values 0 * k))
      (@Finite_prod Z Z
        (fun x : Z => 0 <= x < i /\
          Znth i values 0 = Znth x values 0 * k)
        (fun z : Z => i + 1 <= z < Zlength values /\
          Znth z values 0 = Znth i values 0 * k)
        (finite_Z_range' 0 i
          (fun x : Z => Znth i values 0 = Znth x values 0 * k))
        (finite_Z_range' (i + 1) (Zlength values)
          (fun z : Z => Znth z values 0 = Znth i values 0 * k)))).
  - symmetry.
    eapply set_card_bijection__counting_transitions with
      (f := fun p : Z * Z => (fst p, (i, snd p))).
    + intros [x z]. simpl. intuition lia.
    + intros [x [y z]]. simpl. intros Hq.
      exists (x, z). destruct Hq as [Hb [Hy Hrest]].
      subst y. simpl in *. intuition lia.
    + intros [x z] [x' z']. simpl. intros _ _ Heq.
      inversion Heq. reflexivity.
  - apply set_card_product__counting_transitions.
Qed.
Lemma predecessor_card_from_profile__counting_transitions :
  forall k values i keys left pred,
    1 <= k ->
    Z.rem (Znth i values 0) k = 0 ->
    KeyAt keys (Znth i values 0 ÷ k) pred ->
    FrequencyProfile values 0 i keys left ->
    #(fun x : Z => 0 <= x < i /\
      Znth i values 0 = Znth x values 0 * k) =
      Znth pred left 0.
Proof.
  intros k values i keys left pred Hk Hmod Hkey Hprofile.
  unfold FrequencyProfile in Hprofile.
  destruct Hprofile as [_ [_ [_ Hcounts]]].
  unfold KeyAt in Hkey. destruct Hkey as [Hpred Hkey].
  rewrite Hcounts by exact Hpred. symmetry.
  apply set_card_extensional__counting_transitions.
  intro x. rewrite Hkey.
  pose proof (proj2 (Z_quot_exact_full (Znth i values 0) k) Hmod)
    as Hdivmod.
  intuition nia.
Qed.
Lemma successor_card_from_profile__counting_transitions :
  forall k values i keys right succ,
    KeyAt keys (Znth i values 0 * k) succ ->
    FrequencyProfile values (i + 1) (Zlength values) keys right ->
    #(fun z : Z => i + 1 <= z < Zlength values /\
      Znth z values 0 = Znth i values 0 * k) =
      Znth succ right 0.
Proof.
  intros k values i keys right succ Hkey Hprofile.
  unfold FrequencyProfile in Hprofile.
  destruct Hprofile as [_ [_ [_ Hcounts]]].
  unfold KeyAt in Hkey. destruct Hkey as [Hsucc Hkey].
  rewrite Hcounts by exact Hsucc. symmetry.
  apply set_card_extensional__counting_transitions.
  intro z. rewrite Hkey. tauto.
Qed.
Lemma counting_state_advance_by_card__counting_transitions :
  forall k values i keys left right left' right' answer contribution,
    0 <= i < Zlength values ->
    CountingState k values i keys left right answer ->
    FrequencyProfile values 0 (i + 1) keys left' ->
    FrequencyProfile values (i + 1) (Zlength values) keys right' ->
    #(fun q : Z * (Z * Z) =>
      (0 <= fst q < Zlength values /\
       0 <= fst (snd q) < Zlength values /\
       0 <= snd (snd q) < Zlength values) /\
      fst (snd q) = i /\
      fst q < fst (snd q) /\ fst (snd q) < snd (snd q) /\
      Znth (fst (snd q)) values 0 = Znth (fst q) values 0 * k /\
      Znth (snd (snd q)) values 0 =
        Znth (fst (snd q)) values 0 * k) = contribution ->
    CountingState k values (i + 1) keys left' right'
      (answer + contribution).
Proof.
  intros k values i keys left right left' right' answer contribution
    Hi Hstate Hleft Hright Hcontribution.
  unfold CountingState in Hstate |- *.
  destruct Hstate as [_ [_ Hanswer]].
  split; [exact Hleft |]. split; [exact Hright |].
  rewrite Hanswer, set_card_counting_middle_step__counting_transitions by exact Hi.
  rewrite Hcontribution. reflexivity.
Qed.
Lemma counting_state_bounds__counting_transitions :
  forall k values middle keys left right answer,
    CountingState k values middle keys left right answer ->
    0 <= answer <= Zlength values * Zlength values * Zlength values.
Proof.
  intros k values middle keys left right answer Hstate.
  unfold CountingState in Hstate.
  destruct Hstate as [_ [_ ->]].
  split.
  - apply set_card_nonnegative__counting_transitions.
  - transitivity
      (#(fun q : Z * (Z * Z) =>
        0 <= fst q < Zlength values /\
        0 <= fst (snd q) < Zlength values /\
        0 <= snd (snd q) < Zlength values)).
    + apply set_card_subset_le__counting_transitions.
      intros [x [y z]]. simpl. intuition (auto with *).
    + rewrite set_card_bounded_triples__counting_transitions by
        apply Zlength_nonneg.
      reflexivity.
Qed.
Lemma frequency_profile_bounds__counting_transitions :
  forall values lo hi keys counts,
    FrequencyProfile values lo hi keys counts ->
    forall j, 0 <= j < Zlength keys ->
      0 <= Znth j counts 0 <= hi - lo.
Proof.
  intros values lo hi keys counts Hprofile j Hj.
  unfold FrequencyProfile in Hprofile.
  destruct Hprofile as [_ [[Hlo Hlohi] [Hhi Hcounts]]].
  rewrite Hcounts by exact Hj.
  split.
  - apply set_card_nonnegative__counting_transitions.
  - transitivity (#(fun z : Z => lo <= z < hi)).
    + apply set_card_subset_le__counting_transitions.
      intros z Hz. tauto.
    + rewrite set_card_Z_range__counting_transitions by lia.
      reflexivity.
Qed.
Lemma counting_state_advance_hit__counting_transitions :
  forall k values i keys left right answer source ix pred succ,
    0 <= i < Zlength values ->
    1 <= k ->
    UniqueKeys source keys ->
    KeyAt keys (Znth i values 0) ix ->
    Z.rem (Znth i values 0) k = 0 ->
    KeyAt keys (Znth i values 0 ÷ k) pred ->
    KeyAt keys (Znth i values 0 * k) succ ->
    CountingState k values i keys left right answer ->
    CountingState k values (i + 1) keys
      (replace_Znth ix (Znth ix left 0 + 1) left)
      (replace_Znth ix (Znth ix right 0 - 1) right)
      (answer + Znth pred left 0 *
        Znth succ (replace_Znth ix (Znth ix right 0 - 1) right) 0).
Proof.
  intros k values i keys left right answer source ix pred succ
    Hi Hk Hunique Hcurrent Hmod Hpred Hsucc Hstate.
  assert (Hleft_old : FrequencyProfile values 0 i keys left).
  { exact (proj1 Hstate). }
  assert (Hright_old :
    FrequencyProfile values i (Zlength values) keys right).
  { exact (proj1 (proj2 Hstate)). }
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys
    (replace_Znth ix (Znth ix left 0 + 1) left)).
  { eapply frequency_profile_replace_increment__counting_transitions.
    - lia.
    - exact Hunique.
    - exact Hcurrent.
    - exact Hleft_old. }
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys
    (replace_Znth ix (Znth ix right 0 - 1) right)).
  { eapply frequency_profile_replace_decrement__counting_transitions.
    - lia.
    - exact Hunique.
    - exact Hcurrent.
    - exact Hright_old. }
  eapply counting_state_advance_by_card__counting_transitions;
    [exact Hi | exact Hstate | exact Hleft_new | exact Hright_new |].
  rewrite counting_middle_card_product__counting_transitions by exact Hi.
  rewrite (predecessor_card_from_profile__counting_transitions
    k values i keys left pred) by assumption.
  rewrite (successor_card_from_profile__counting_transitions
    k values i keys
    (replace_Znth ix (Znth ix right 0 - 1) right) succ) by assumption.
  reflexivity.
Qed.
Lemma counting_state_advance_miss__counting_transitions :
  forall k values i keys left right answer source ix,
    0 <= i < Zlength values ->
    UniqueKeys source keys ->
    KeyAt keys (Znth i values 0) ix ->
    CountingState k values i keys left right answer ->
    ((forall x, 0 <= x < i ->
        Znth i values 0 <> Znth x values 0 * k) \/
     (forall z, i + 1 <= z < Zlength values ->
        Znth z values 0 <> Znth i values 0 * k)) ->
    CountingState k values (i + 1) keys
      (replace_Znth ix (Znth ix left 0 + 1) left)
      (replace_Znth ix (Znth ix right 0 - 1) right)
      answer.
Proof.
  intros k values i keys left right answer source ix
    Hi Hunique Hcurrent Hstate Hmiss.
  assert (Hleft_old : FrequencyProfile values 0 i keys left).
  { exact (proj1 Hstate). }
  assert (Hright_old :
    FrequencyProfile values i (Zlength values) keys right).
  { exact (proj1 (proj2 Hstate)). }
  assert (Hleft_new : FrequencyProfile values 0 (i + 1) keys
    (replace_Znth ix (Znth ix left 0 + 1) left)).
  { eapply frequency_profile_replace_increment__counting_transitions.
    - lia.
    - exact Hunique.
    - exact Hcurrent.
    - exact Hleft_old. }
  assert (Hright_new : FrequencyProfile values (i + 1) (Zlength values) keys
    (replace_Znth ix (Znth ix right 0 - 1) right)).
  { eapply frequency_profile_replace_decrement__counting_transitions.
    - lia.
    - exact Hunique.
    - exact Hcurrent.
    - exact Hright_old. }
  assert (Hadvance : CountingState k values (i + 1) keys
    (replace_Znth ix (Znth ix left 0 + 1) left)
    (replace_Znth ix (Znth ix right 0 - 1) right)
    (answer + 0)).
  {
    eapply counting_state_advance_by_card__counting_transitions;
      [exact Hi | exact Hstate | exact Hleft_new | exact Hright_new |].
    apply set_card_empty__counting_transitions.
    intros [x [y z]]. simpl. intros Hq.
    destruct Hq as [Hb [Hy [Hxy [Hyz [Hvx Hvz]]]]].
    subst y. simpl in *.
    destruct Hmiss as [Hleft | Hright].
    - apply (Hleft x ltac:(lia)). exact Hvx.
    - apply (Hright z ltac:(lia)). exact Hvz.
  }
  replace (answer + 0) with answer in Hadvance by lia.
  exact Hadvance.
Qed.
Lemma counting_state_advance_mod_miss__counting_transitions :
  forall k values i keys left right answer source ix,
    0 <= i < Zlength values ->
    1 <= k ->
    UniqueKeys source keys ->
    KeyAt keys (Znth i values 0) ix ->
    Z.rem (Znth i values 0) k <> 0 ->
    CountingState k values i keys left right answer ->
    CountingState k values (i + 1) keys
      (replace_Znth ix (Znth ix left 0 + 1) left)
      (replace_Znth ix (Znth ix right 0 - 1) right)
      answer.
Proof.
  intros k values i keys left right answer source ix
    Hi Hk Hunique Hcurrent Hmod Hstate.
  eapply counting_state_advance_miss__counting_transitions;
    eauto.
  left. intros x Hx Heq.
  apply Hmod. rewrite Heq. apply Z_rem_mult.
Qed.
Lemma exact_quotient_as_division__counting_transitions :
  forall x k,
    k <> 0 -> Z.rem x k = 0 -> x ÷ k = x / k.
Proof.
  intros x k Hk Hmod.
  pose proof (proj2 (Z_quot_exact_full x k) Hmod) as Hquot.
  pose proof (Z_div_mod_eq_full x k) as Heq.
  assert (Hmodulo : x mod k = 0).
  { rewrite Hquot at 1. rewrite Z.mul_comm. apply Z_mod_mult. }
  rewrite Hmodulo, Z.add_0_r in Heq.
  nia.
Qed.
Lemma quotient_times_divisor__counting_transitions :
  forall x k,
    Z.rem x k = 0 -> x = (x ÷ k) * k.
Proof.
  intros x k Hrem.
  pose proof (proj2 (Z_quot_exact_full x k) Hrem) as Heq.
  nia.
Qed.
Lemma set_card_extensional__final_result :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intro x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma counting_state_at_end__final_result :
  forall k values keys left right answer,
    CountingState k values (Zlength values) keys left right answer ->
    Spec k values answer.
Proof.
  intros k values keys left right answer Hstate.
  unfold CountingState in Hstate.
  destruct Hstate as (_ & _ & Hanswer).
  unfold Spec.
  rewrite Hanswer.
  apply set_card_extensional__final_result.
  intro q.
  intuition lia.
Qed.
