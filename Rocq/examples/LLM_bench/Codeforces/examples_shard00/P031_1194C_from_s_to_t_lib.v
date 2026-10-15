Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CanInsertFromPool (s p t : list Z) : Prop :=
  exists inserted,
    (exists unused, Permutation p (inserted ++ unused)) /\
    exists positions,
      Zlength positions = Zlength s /\
      (forall i, 0 <= i < Zlength s ->
         0 <= Znth i positions 0 < Zlength t /\
         Znth (Znth i positions 0) t 0 = Znth i s 0) /\
      mono_inc positions /\
      Permutation (s ++ inserted) t.

Definition Pre (s t p : list Z) : Prop :=
  1 <= Zlength s <= 100 /\ 1 <= Zlength t <= 100 /\ 1 <= Zlength p <= 100 /\
  Forall (fun c => 97 <= c <= 122) s /\
  Forall (fun c => 97 <= c <= 122) t /\
  Forall (fun c => 97 <= c <= 122) p.

Definition Spec (s t p : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> CanInsertFromPool s p t).

Definition PrefixEmbedding
    (source target : list Z) (source_len target_len : Z) : Prop :=
  exists positions,
    Zlength positions = source_len /\
    mono_inc positions /\
    (forall k, 0 <= k < source_len ->
      0 <= Znth k positions 0 < target_len /\
      Znth (Znth k positions 0) target 0 = Znth k source 0).

Definition GreedyPrefixMatch
    (source target : list Z) (target_len matched : Z) : Prop :=
  0 <= matched <= Zlength source /\
  0 <= target_len <= Zlength target /\
  PrefixEmbedding source target matched target_len /\
  forall k,
    0 <= k <= Zlength source ->
    PrefixEmbedding source target k target_len ->
    k <= matched.

Definition IsSubsequence (source target : list Z) : Prop :=
  PrefixEmbedding source target (Zlength source) (Zlength target).

Definition NoSubsequence (source target : list Z) : Prop :=
  ~ IsSubsequence source target.

Definition LetterCount (text : list Z) (letter : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec text letter).

Definition CountState
    (source pool target : list Z)
    (source_done pool_done target_done : Z)
    (counts : list Z) : Prop :=
  Zlength counts = 26 /\
  forall c, 0 <= c < 26 ->
    Znth c counts 0 =
      LetterCount (sublist 0 source_done source) (97 + c) +
      LetterCount (sublist 0 pool_done pool) (97 + c) -
      LetterCount (sublist 0 target_done target) (97 + c).

Definition NonnegativeCounts (counts : list Z) : Prop :=
  forall c, 0 <= c < 26 -> 0 <= Znth c counts 0.

Definition SupplyShortage
    (source pool target : list Z) : Prop :=
  exists c,
    0 <= c < 26 /\
    LetterCount (source ++ pool) (97 + c) <
    LetterCount target (97 + c).

Require Import Coq.micromega.Lia.
Lemma letter_count_bounds__count_init_safety :
  forall text letter,
    0 <= LetterCount text letter <= Zlength text.
Proof.
  intros text letter.
  unfold LetterCount.
  split.
  - lia.
  - rewrite Zlength_correct.
    apply Nat2Z.inj_le.
    apply count_occ_bound.
Qed.
Lemma count_state_cell_bounds__count_init_safety :
  forall source pool target source_done pool_done target_done counts c,
    CountState source pool target source_done pool_done target_done counts ->
    0 <= source_done <= Zlength source ->
    0 <= pool_done <= Zlength pool ->
    0 <= target_done <= Zlength target ->
    0 <= c < 26 ->
    - Zlength target <= Znth c counts 0 <= Zlength source + Zlength pool.
Proof.
  intros source pool target source_done pool_done target_done counts c
    Hstate Hsource Hpool Htarget Hc.
  unfold CountState in Hstate.
  destruct Hstate as [_ Hcell].
  specialize (Hcell c Hc).
  rewrite Hcell.
  pose proof
    (letter_count_bounds__count_init_safety
       (sublist 0 source_done source) (97 + c)) as Hsource_count.
  pose proof
    (letter_count_bounds__count_init_safety
       (sublist 0 pool_done pool) (97 + c)) as Hpool_count.
  pose proof
    (letter_count_bounds__count_init_safety
       (sublist 0 target_done target) (97 + c)) as Htarget_count.
  rewrite Zlength_sublist0 in Hsource_count by lia.
  rewrite Zlength_sublist0 in Hpool_count by lia.
  rewrite Zlength_sublist0 in Htarget_count by lia.
  lia.
Qed.
Lemma greedy_prefix_zero__count_init_safety :
  forall source target,
    GreedyPrefixMatch source target 0 0.
Proof.
  intros source target.
  pose proof (Zlength_nonneg source) as Hsource.
  pose proof (Zlength_nonneg target) as Htarget.
  unfold GreedyPrefixMatch.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * unfold PrefixEmbedding.
        exists nil.
        split.
        -- rewrite Zlength_nil. reflexivity.
        -- split.
           ++ apply mono_inc_nil.
           ++ intros k Hk. lia.
      * intros k Hk Hembedding.
        unfold PrefixEmbedding in Hembedding.
        destruct Hembedding as [positions [Hlen [Hmono Hpositions]]].
        destruct (Z.eq_dec k 0) as [-> | Hneq].
        -- lia.
        -- specialize (Hpositions 0 ltac:(lia)).
           lia.
Qed.
Lemma prefix_embedding_drop_last__greedy_match :
  forall source target source_len target_len,
    0 < source_len ->
    PrefixEmbedding source target source_len (target_len + 1) ->
    PrefixEmbedding source target (source_len - 1) target_len.
Proof.
  intros source target source_len target_len Hpos
    (positions & Hlen & Hmono & Helts).
  exists (sublist 0 (source_len - 1) positions).
  split.
  - rewrite Zlength_sublist by lia. lia.
  - split.
    + unfold mono_inc in *.
      intros x y Hx Hxy Hy.
      rewrite Zlength_sublist in Hy by lia.
      rewrite !Znth_sublist0 by lia.
      apply Hmono; lia.
    + intros idx Hidx.
      rewrite Znth_sublist0 by lia.
      pose proof (Helts idx ltac:(lia)) as Hidx_info.
      destruct Hidx_info as (Hrange & Heq).
      split; [|exact Heq].
      split; [lia|].
      specialize (Helts (source_len - 1) ltac:(lia)) as (Hlast & _).
      specialize (Hmono idx (source_len - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      lia.
Qed.
Lemma greedy_prefix_match_equal_step__greedy_match :
  forall source target j i,
    0 <= i < Zlength source ->
    0 <= j < Zlength target ->
    Znth i source 0 = Znth j target 0 ->
    GreedyPrefixMatch source target j i ->
    GreedyPrefixMatch source target (j + 1) (i + 1).
Proof.
  intros source target j i Hi Hj Heq HG.
  unfold GreedyPrefixMatch in *.
  destruct HG as (Hib & Hjb & HE & HM).
  destruct HE as (positions & Hlen & Hmono & Helts).
  split; [lia|].
  split; [lia|].
  split.
  - exists (positions ++ (j :: nil)).
    split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + split.
      * unfold mono_inc in *.
        intros x y Hx Hxy Hy.
        rewrite Zlength_app, Zlength_cons, Zlength_nil in Hy.
        destruct (Z_lt_ge_dec y (Zlength positions)) as [Hyold | Hynew].
        -- rewrite !app_Znth1 by lia. apply Hmono; lia.
        -- assert (y = Zlength positions) by lia. subst y.
           rewrite (app_Znth2 0 positions (j :: nil) (Zlength positions)) by lia.
           rewrite Z.sub_diag, Znth0_cons.
           rewrite app_Znth1 by lia.
           specialize (Helts x ltac:(lia)) as (Hxrange & _).
           lia.
      * intros idx Hidx.
        destruct (Z_lt_ge_dec idx i) as [Hidxold | Hidxnew].
        -- rewrite app_Znth1 by lia.
           specialize (Helts idx ltac:(lia)) as (Hrange & Hchar).
           split; [lia|exact Hchar].
        -- assert (idx = i) by lia. subst idx.
           rewrite (app_Znth2 0 positions (j :: nil) i) by lia.
           replace (i - Zlength positions) with 0 by lia.
           rewrite Znth0_cons.
           split; [lia|]. rewrite <- Heq. reflexivity.
  - intros candidate Hcandidate HEcandidate.
    destruct (Z_le_gt_dec candidate 0) as [Hnonpos | Hpos].
    + lia.
    + assert (Hpositive : 0 < candidate) by lia.
      pose proof
        (prefix_embedding_drop_last__greedy_match
           source target candidate j Hpositive HEcandidate) as Hdrop.
      specialize (HM (candidate - 1) ltac:(lia) Hdrop).
      lia.
Qed.
Lemma greedy_prefix_match_skip_step__greedy_match :
  forall source target j i,
    0 <= i < Zlength source ->
    0 <= j < Zlength target ->
    Znth i source 0 <> Znth j target 0 ->
    GreedyPrefixMatch source target j i ->
    GreedyPrefixMatch source target (j + 1) i.
Proof.
  intros source target j i Hi Hj Hneq HG.
  unfold GreedyPrefixMatch in *.
  destruct HG as (Hib & Hjb & HE & HM).
  split; [lia|].
  split; [lia|].
  split.
  - destruct HE as (positions & Hlen & Hmono & Helts).
    exists positions. split; [exact Hlen|]. split; [exact Hmono|].
    intros idx Hidx. specialize (Helts idx Hidx) as (Hrange & Heq).
    split; [lia|exact Heq].
  - intros candidate Hcandidate HEcandidate.
    destruct (Z_le_gt_dec candidate i) as [Hdone | Hlong]; auto.
    assert (Hkpos : 0 < candidate) by lia.
    pose proof
      (prefix_embedding_drop_last__greedy_match
         source target candidate j Hkpos HEcandidate) as Hdrop.
    pose proof (HM (candidate - 1) ltac:(lia) Hdrop) as Hmax_drop.
    assert (Hki : candidate = i + 1) by lia. subst candidate.
    destruct HEcandidate as (positions & Hlen & Hmono & Helts).
    pose proof (Helts i ltac:(lia)) as Hlast_info.
    destruct Hlast_info as (Hlast & Hchar).
    assert (Hposj : Znth i positions 0 = j).
    {
      destruct Hlast as (Hpos0 & Hposlt).
      assert (Znth i positions 0 <= j) by lia.
      destruct (Z.eq_dec (Znth i positions 0) j) as [Heqj | Hnej]; auto.
      assert (Hstrict : Znth i positions 0 < j) by lia.
      exfalso.
      pose proof (HM (i + 1) ltac:(lia)) as Hmax_next.
      assert (Hembed_old : PrefixEmbedding source target (i + 1) j).
      {
      exists positions. split; [exact Hlen|]. split; [exact Hmono|].
      intros x Hx.
      specialize (Helts x Hx) as (Hxrange & Hxchar).
      split; [|exact Hxchar].
      split; [lia|].
      destruct (Z_lt_ge_dec x i) as [Hxi | Hxi].
      - specialize (Hmono x i ltac:(lia) Hxi ltac:(lia)). lia.
      - assert (x = i) by lia. subst x. exact Hstrict.
      }
      specialize (Hmax_next Hembed_old). lia.
    }
    rewrite Hposj in Hchar.
    exfalso. apply Hneq. symmetry. exact Hchar.
Qed.
Lemma greedy_prefix_match_target_step_complete__greedy_match :
  forall source target j i,
    i = Zlength source ->
    0 <= j < Zlength target ->
    GreedyPrefixMatch source target j i ->
    GreedyPrefixMatch source target (j + 1) i.
Proof.
  intros source target j i Hi Hj HG.
  unfold GreedyPrefixMatch in *.
  destruct HG as (Hib & Hjb & HE & HM).
  split; [lia|].
  split; [lia|].
  split.
  - destruct HE as (positions & Hlen & Hmono & Helts).
    exists positions. split; [exact Hlen|]. split; [exact Hmono|].
    intros k Hk. specialize (Helts k Hk) as (Hrange & Heq).
    split; [lia|exact Heq].
  - intros k Hkb _. lia.
Qed.
Lemma greedy_prefix_match_complete_cases__greedy_match :
  forall source target target_len matched,
    GreedyPrefixMatch source target target_len matched ->
    target_len = Zlength target ->
    (matched = Zlength source -> IsSubsequence source target) /\
    (matched < Zlength source -> NoSubsequence source target).
Proof.
  intros source target target_len matched HG Htarget.
  unfold GreedyPrefixMatch in HG.
  destruct HG as (Hmbounds & _ & HE & HM).
  split.
  - intros Hmatched. unfold IsSubsequence. now rewrite <- Htarget, <- Hmatched.
  - intros Hshort Hsub.
    unfold IsSubsequence in Hsub.
    specialize (HM (Zlength source) ltac:(lia)).
    rewrite Htarget in HM.
    specialize (HM Hsub). lia.
Qed.
Lemma Zlength_replace_Znth__source_pool_updates :
  forall {A : Type} (xs : list A) i (v : A),
    Zlength (replace_Znth i v xs) = Zlength xs.
Proof.
  intros A xs i v.
  assert (Hlen : forall (B : Type) (n : nat) (ys : list B) (w : B),
      length (replace_nth n ys w) = length ys).
  { intros B n ys. revert n.
    induction ys as [| y ys IH]; intros [| n] w; simpl; auto. }
  unfold replace_Znth.
  rewrite !Zlength_correct, Hlen.
  reflexivity.
Qed.
Lemma Znth_app_left__source_pool_updates :
  forall {A : Type} (d : A) (xs ys : list A) i,
    0 <= i < Zlength xs ->
    Znth i (xs ++ ys) d = Znth i xs d.
Proof.
  intros A d xs ys i Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi.
    lia.
Qed.
Lemma Znth_app_last__source_pool_updates :
  forall {A : Type} (d x : A) (xs : list A),
    Znth (Zlength xs) (xs ++ x :: nil) d = x.
Proof.
  intros A d x xs.
  unfold Znth.
  rewrite app_nth2.
  - replace (Z.to_nat (Zlength xs) - length xs)%nat with 0%nat.
    + simpl.
      reflexivity.
    + rewrite Zlength_correct, Nat2Z.id.
      lia.
  - rewrite Zlength_correct, Nat2Z.id.
    lia.
Qed.
Lemma sublist_snoc_at_index__source_pool_updates :
  forall (xs : list Z) i,
    0 <= i < Zlength xs ->
    sublist 0 (i + 1) xs = sublist 0 i xs ++ Znth i xs 0 :: nil.
Proof.
  intros xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (@sublist_single Z 0 i xs) by lia.
  reflexivity.
Qed.
Lemma letter_count_sublist_snoc_eq__source_pool_updates :
  forall (xs : list Z) i v,
    0 <= i < Zlength xs ->
    Znth i xs 0 = v ->
    LetterCount (sublist 0 (i + 1) xs) v =
      LetterCount (sublist 0 i xs) v + 1.
Proof.
  intros xs i v Hi Hv.
  rewrite sublist_snoc_at_index__source_pool_updates by exact Hi.
  unfold LetterCount.
  rewrite count_occ_app.
  simpl.
  rewrite Hv.
  destruct (Z.eq_dec v v); lia.
Qed.
Lemma letter_count_sublist_snoc_neq__source_pool_updates :
  forall (xs : list Z) i v,
    0 <= i < Zlength xs ->
    Znth i xs 0 <> v ->
    LetterCount (sublist 0 (i + 1) xs) v =
      LetterCount (sublist 0 i xs) v.
Proof.
  intros xs i v Hi Hv.
  rewrite sublist_snoc_at_index__source_pool_updates by exact Hi.
  unfold LetterCount.
  rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec (Znth i xs 0) v); lia.
Qed.
Lemma count_state_source_step__source_pool_updates :
  forall source pool target counts i,
    0 <= i < Zlength source ->
    97 <= Znth i source 0 <= 122 ->
    CountState source pool target i 0 0 counts ->
    CountState source pool target (i + 1) 0 0
      (replace_Znth (Znth i source 0 - 97)
        (Znth (Znth i source 0 - 97) counts 0 + 1) counts).
Proof.
  intros source pool target counts i Hi Hchar Hstate.
  unfold CountState in Hstate |- *.
  destruct Hstate as [Hlen Hstate].
  split.
  - rewrite Zlength_replace_Znth__source_pool_updates.
    exact Hlen.
  - intros c Hc.
    assert (Hidx : 0 <= Znth i source 0 - 97 < 26) by lia.
    destruct (Z.eq_dec c (Znth i source 0 - 97)) as [Heq | Hneq].
    + subst c.
      rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hidx).
      rewrite Hstate by exact Hidx.
      rewrite letter_count_sublist_snoc_eq__source_pool_updates by
        (exact Hi || lia).
      lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
      rewrite Hstate by exact Hc.
      rewrite letter_count_sublist_snoc_neq__source_pool_updates by
        (exact Hi || lia).
      lia.
Qed.
Lemma count_state_pool_step__source_pool_updates :
  forall source pool target counts source_done i,
    0 <= i < Zlength pool ->
    97 <= Znth i pool 0 <= 122 ->
    CountState source pool target source_done i 0 counts ->
    CountState source pool target source_done (i + 1) 0
      (replace_Znth (Znth i pool 0 - 97)
        (Znth (Znth i pool 0 - 97) counts 0 + 1) counts).
Proof.
  intros source pool target counts source_done i Hi Hchar Hstate.
  unfold CountState in Hstate |- *.
  destruct Hstate as [Hlen Hstate].
  split.
  - rewrite Zlength_replace_Znth__source_pool_updates.
    exact Hlen.
  - intros c Hc.
    assert (Hidx : 0 <= Znth i pool 0 - 97 < 26) by lia.
    destruct (Z.eq_dec c (Znth i pool 0 - 97)) as [Heq | Hneq].
    + subst c.
      rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hidx).
      rewrite Hstate by exact Hidx.
      rewrite letter_count_sublist_snoc_eq__source_pool_updates by
        (exact Hi || lia).
      lia.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
      rewrite Hstate by exact Hc.
      rewrite letter_count_sublist_snoc_neq__source_pool_updates by
        (exact Hi || lia).
      lia.
Qed.
Lemma nonnegative_counts_increment__source_pool_updates :
  forall counts idx,
    Zlength counts = 26 ->
    0 <= idx < 26 ->
    NonnegativeCounts counts ->
    NonnegativeCounts
      (replace_Znth idx (Znth idx counts 0 + 1) counts).
Proof.
  intros counts idx Hlen Hidx Hnonneg.
  unfold NonnegativeCounts in Hnonneg |- *.
  intros c Hc.
  destruct (Z.eq_dec c idx) as [Heq | Hneq].
  - subst c.
    rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hidx).
    specialize (Hnonneg idx Hidx).
    lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    apply Hnonneg.
    exact Hc.
Qed.
Lemma Zlength_replace_Znth__target_shortage {A : Type}
    (i : Z) (v : A) (l : list A) :
  Zlength (replace_Znth i v l) = Zlength l.
Proof.
  unfold replace_Znth.
  repeat rewrite Zlength_correct.
  assert (Hlen : forall n, length (replace_nth n l v) = length l).
  {
    intro n.
    revert n.
    induction l as [|x l IH]; intros [|n]; simpl; auto.
  }
  rewrite Hlen.
  reflexivity.
Qed.
Lemma letter_count_sublist_succ_same__target_shortage :
  forall (text : list Z) (i : Z),
    0 <= i < Zlength text ->
    LetterCount (sublist 0 (i + 1) text) (Znth i text 0) =
      LetterCount (sublist 0 i text) (Znth i text 0) + 1.
Proof.
  intros text i Hi.
  rewrite (sublist_split 0 (i + 1) i text) by lia.
  rewrite (sublist_single 0 i text) by lia.
  unfold LetterCount.
  rewrite count_occ_app.
  rewrite Nat2Z.inj_add.
  simpl.
  destruct (Z.eq_dec (Znth i text 0) (Znth i text 0)); try contradiction.
  reflexivity.
Qed.
Lemma letter_count_sublist_succ_diff__target_shortage :
  forall (text : list Z) (i letter : Z),
    0 <= i < Zlength text ->
    Znth i text 0 <> letter ->
    LetterCount (sublist 0 (i + 1) text) letter =
      LetterCount (sublist 0 i text) letter.
Proof.
  intros text i letter Hi Hneq.
  rewrite (sublist_split 0 (i + 1) i text) by lia.
  rewrite (sublist_single 0 i text) by lia.
  unfold LetterCount.
  rewrite count_occ_app.
  rewrite Nat2Z.inj_add.
  simpl.
  destruct (Z.eq_dec (Znth i text 0) letter); try contradiction.
  lia.
Qed.
Lemma count_state_target_step__target_shortage :
  forall (source pool target : list Z) (source_done pool_done i : Z)
         (counts : list Z),
    CountState source pool target source_done pool_done i counts ->
    0 <= i < Zlength target ->
    97 <= Znth i target 0 <= 122 ->
    CountState source pool target source_done pool_done (i + 1)
      (replace_Znth (Znth i target 0 - 97)
         (Znth (Znth i target 0 - 97) counts 0 - 1) counts).
Proof.
  intros source pool target source_done pool_done i counts Hstate Hi Hchar.
  destruct Hstate as [Hlen Hstate].
  split.
  - rewrite Zlength_replace_Znth__target_shortage. exact Hlen.
  - intros c Hc.
    assert (Hidx : 0 <= Znth i target 0 - 97 < 26) by lia.
    destruct (Z.eq_dec c (Znth i target 0 - 97)) as [Heq | Hneq].
    + subst c.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Hstate by lia.
      replace (97 + (Znth i target 0 - 97)) with (Znth i target 0) by lia.
      rewrite letter_count_sublist_succ_same__target_shortage by lia.
      lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite Hstate by lia.
      rewrite letter_count_sublist_succ_diff__target_shortage by lia.
      reflexivity.
Qed.
Lemma letter_count_app__target_shortage :
  forall (left right : list Z) (letter : Z),
    LetterCount (left ++ right) letter =
      LetterCount left letter + LetterCount right letter.
Proof.
  intros left right letter.
  unfold LetterCount.
  rewrite count_occ_app.
  rewrite Nat2Z.inj_add.
  reflexivity.
Qed.
Lemma letter_count_prefix_le__target_shortage :
  forall (text : list Z) (k letter : Z),
    0 <= k <= Zlength text ->
    LetterCount (sublist 0 k text) letter <= LetterCount text letter.
Proof.
  intros text k letter Hk.
  assert (Hdecomp :
      text = sublist 0 k text ++ sublist k (Zlength text) text).
  {
    transitivity (sublist 0 (Zlength text) text).
    - symmetry. apply sublist_self. reflexivity.
    - apply sublist_split; lia.
  }
  assert (Hcount :
      LetterCount text letter =
      LetterCount (sublist 0 k text) letter +
      LetterCount (sublist k (Zlength text) text) letter).
  {
    rewrite <- letter_count_app__target_shortage.
    f_equal.
    exact Hdecomp.
  }
  rewrite Hcount.
  unfold LetterCount.
  lia.
Qed.
Lemma negative_target_cell_implies_shortage__target_shortage :
  forall (source pool target counts : list Z) (i : Z),
    CountState source pool target (Zlength source) (Zlength pool) i counts ->
    NonnegativeCounts counts ->
    0 <= i < Zlength target ->
    97 <= Znth i target 0 <= 122 ->
    Znth (Znth i target 0 - 97)
      (replace_Znth (Znth i target 0 - 97)
        (Znth (Znth i target 0 - 97) counts 0 - 1) counts) 0 < 0 ->
    SupplyShortage source pool target.
Proof.
  intros source pool target counts i Hstate Hnonneg Hi Hchar Hnegative.
  destruct Hstate as [Hlen Hstate].
  assert (Hidx : 0 <= Znth i target 0 - 97 < 26) by lia.
  rewrite Znth_replace_Znth_Same in Hnegative by lia.
  pose proof (Hnonneg (Znth i target 0 - 97) Hidx) as Hcell_nonnegative.
  assert (Hcell : Znth (Znth i target 0 - 97) counts 0 = 0) by lia.
  pose proof (Hstate (Znth i target 0 - 97) Hidx) as Hbalance.
  rewrite (sublist_self source (Zlength source) eq_refl) in Hbalance.
  rewrite (sublist_self pool (Zlength pool) eq_refl) in Hbalance.
  replace (97 + (Znth i target 0 - 97)) with (Znth i target 0)
    in Hbalance by lia.
  assert (Hprefix_step :
      LetterCount (sublist 0 (i + 1) target) (Znth i target 0) =
      LetterCount (sublist 0 i target) (Znth i target 0) + 1).
  {
    apply letter_count_sublist_succ_same__target_shortage.
    exact Hi.
  }
  assert (Htarget :
      LetterCount (sublist 0 (i + 1) target) (Znth i target 0) <=
      LetterCount target (Znth i target 0)).
  {
    apply letter_count_prefix_le__target_shortage.
    lia.
  }
  unfold SupplyShortage.
  exists (Znth i target 0 - 97).
  split; [exact Hidx |].
  replace (97 + (Znth i target 0 - 97)) with (Znth i target 0) by lia.
  rewrite letter_count_app__target_shortage.
  lia.
Qed.
Lemma nonnegative_counts_decrement__target_shortage :
  forall (counts : list Z) (idx : Z),
    Zlength counts = 26 ->
    NonnegativeCounts counts ->
    0 <= idx < 26 ->
    0 <= Znth idx
      (replace_Znth idx (Znth idx counts 0 - 1) counts) 0 ->
    NonnegativeCounts
      (replace_Znth idx (Znth idx counts 0 - 1) counts).
Proof.
  intros counts idx Hlen Hnonnegative Hidx Hupdated c Hc.
  destruct (Z.eq_dec c idx) as [Heq | Hneq].
  - subst c. exact Hupdated.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hnonnegative.
    exact Hc.
Qed.
Lemma Znth_app_left__target_shortage :
  forall {A : Type} (d : A) (l1 l2 : list A) i,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A d l1 l2 i Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_last__target_shortage :
  forall {A : Type} (d x : A) (l : list A),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros A d x l.
  unfold Znth.
  rewrite app_nth2.
  - replace (Z.to_nat (Zlength l) - length l)%nat with 0%nat.
    + simpl. reflexivity.
    + rewrite Zlength_correct, Nat2Z.id. lia.
  - rewrite Zlength_correct, Nat2Z.id. lia.
Qed.
Lemma Zlength_map__success_final :
  forall (A B : Type) (f : A -> B) (l : list A),
    Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  rewrite !Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.
Lemma Znth_map_in_range__success_final :
  forall (A B : Type) (f : A -> B) (l : list A)
         (da : A) (db : B) i,
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l.
  induction l as [|a l IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. lia.
Qed.
Lemma mono_inc_map_pred__success_final :
  forall positions,
    mono_inc positions ->
    mono_inc (map (fun z => z - 1) positions).
Proof.
  intros positions Hmono i j Hi Hij Hj.
  rewrite Zlength_map__success_final in Hj.
  rewrite !Znth_map_in_range__success_final with (da := 0) by lia.
  specialize (Hmono i j Hi Hij Hj).
  lia.
Qed.
Lemma embedding_complement__success_final :
  forall target source positions,
    Zlength positions = Zlength source ->
    mono_inc positions ->
    (forall k, 0 <= k < Zlength source ->
      0 <= Znth k positions 0 < Zlength target /\
      Znth (Znth k positions 0) target 0 = Znth k source 0) ->
    exists inserted, Permutation (source ++ inserted) target.
Proof.
  induction target as [|b target IH]; intros source positions Hlen Hmono Hpoint.
  - destruct source as [|a source].
    + exists nil. constructor.
    + specialize (Hpoint 0 ltac:(rewrite Zlength_cons;
                                  pose proof (Zlength_nonneg source); lia)).
      rewrite Zlength_nil in Hpoint. lia.
  - destruct source as [|a source].
    + exists (b :: target). simpl. apply Permutation_refl.
    + destruct positions as [|p positions].
      { rewrite !Zlength_correct in Hlen. simpl in Hlen. lia. }
      assert (Hp : 0 <= p < Zlength (b :: target)).
      { specialize (Hpoint 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg source); lia)).
        rewrite Znth0_cons in Hpoint. tauto. }
      destruct (Z.eq_dec p 0) as [Hp0 | Hp0].
      * subst p.
      assert (Hab : b = a).
      { specialize (Hpoint 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg source); lia)).
        rewrite !Znth0_cons in Hpoint. tauto. }
      subst b.
      apply (proj1 (mono_inc_cons 0 positions)) in Hmono.
      destruct Hmono as [Hpositions_pos Htailmono].
      specialize (IH source (map (fun z => z - 1) positions)).
      assert (Htail_len :
        Zlength (map (fun z => z - 1) positions) = Zlength source).
      { rewrite Zlength_map__success_final.
        rewrite !Zlength_cons in Hlen. lia. }
      assert (Htail_point :
        forall k, 0 <= k < Zlength source ->
          0 <= Znth k (map (fun z => z - 1) positions) 0 < Zlength target /\
          Znth (Znth k (map (fun z => z - 1) positions) 0) target 0 =
          Znth k source 0).
      { intros k Hk.
        specialize (Hpoint (k + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth_cons in Hpoint by lia.
        replace (k + 1 - 1) with k in Hpoint by lia.
        assert (Hkp : 0 <= k < Zlength positions).
        { rewrite !Zlength_cons in Hlen. lia. }
        rewrite Znth_map_in_range__success_final with (da := 0) by exact Hkp.
        assert (Hpos : 0 < Znth k positions 0).
        { apply (proj1 (Forall_Znth (fun y => 0 < y) 0 positions)
                       Hpositions_pos k Hkp). }
        rewrite Znth_cons in Hpoint by lia.
        rewrite Znth_cons in Hpoint by lia.
        destruct Hpoint as [[Hlo Hhi] Heq].
        split.
        - rewrite Zlength_cons in Hhi. lia.
        - replace (k + 1 - 1) with k in Heq by lia. exact Heq. }
      destruct (IH Htail_len
                   (mono_inc_map_pred__success_final positions Htailmono)
                   Htail_point) as [inserted Hperm].
      exists inserted. simpl. apply perm_skip. exact Hperm.
      * assert (Hp_pos : 0 < p) by lia.
      specialize (IH (a :: source)
        (map (fun z => z - 1) (p :: positions))).
      assert (Hall_pos :
        forall k, 0 <= k < Zlength (p :: positions) ->
          0 < Znth k (p :: positions) 0).
      { intros k Hk.
        destruct (Z.eq_dec k 0) as [-> | Hk0].
        - rewrite Znth0_cons. exact Hp_pos.
        - specialize (Hmono 0 k ltac:(lia) ltac:(lia) ltac:(lia)).
          rewrite Znth0_cons in Hmono. lia. }
      assert (Hshift_len :
        Zlength (map (fun z => z - 1) (p :: positions)) =
        Zlength (a :: source)).
      { rewrite Zlength_map__success_final. exact Hlen. }
      assert (Hshift_point :
        forall k, 0 <= k < Zlength (a :: source) ->
          0 <= Znth k (map (fun z => z - 1) (p :: positions)) 0 <
               Zlength target /\
          Znth (Znth k (map (fun z => z - 1) (p :: positions)) 0)
               target 0 = Znth k (a :: source) 0).
      { intros k Hk.
        assert (Hkp : 0 <= k < Zlength (p :: positions)) by lia.
        specialize (Hpoint k Hk).
        specialize (Hall_pos k Hkp).
        rewrite Znth_map_in_range__success_final with (da := 0) by exact Hkp.
        assert (Htarget_shift :
          Znth (Znth k (p :: positions) 0) (b :: target) 0 =
          Znth (Znth k (p :: positions) 0 - 1) target 0).
        { apply Znth_cons. lia. }
        rewrite Htarget_shift in Hpoint.
        destruct Hpoint as [[Hlo Hhi] Heq].
        split.
        - rewrite Zlength_cons in Hhi. lia.
        - exact Heq. }
      destruct (IH Hshift_len
                   (mono_inc_map_pred__success_final (p :: positions) Hmono)
                   Hshift_point) as [inserted Hperm].
      exists (b :: inserted).
      eapply Permutation_trans.
      { apply Permutation_sym. apply Permutation_middle. }
      apply perm_skip. exact Hperm.
Qed.
Lemma multiset_inclusion_decompose__success_final :
  forall need have,
    (forall x,
      (count_occ Z.eq_dec need x <= count_occ Z.eq_dec have x)%nat) ->
    exists rest, Permutation have (need ++ rest).
Proof.
  induction need as [|a need IH]; intros have Hcount.
  - exists have. simpl. apply Permutation_refl.
  - assert (Hin : In a have).
    { apply (proj2 (count_occ_In Z.eq_dec have a)).
      specialize (Hcount a).
      rewrite count_occ_cons_eq in Hcount by reflexivity.
      lia. }
    apply in_split in Hin.
    destruct Hin as [left [right ->]].
    assert (Htail :
      forall x,
        (count_occ Z.eq_dec need x <=
         count_occ Z.eq_dec (left ++ right) x)%nat).
    { intros x. specialize (Hcount x).
      rewrite count_occ_app in Hcount.
      rewrite count_occ_app.
      simpl in Hcount.
      destruct (Z.eq_dec a x); subst; simpl in *; lia. }
    destruct (IH (left ++ right) Htail) as [rest Hperm].
    exists rest. simpl.
    eapply Permutation_trans.
    + apply Permutation_sym. apply Permutation_middle.
    + apply perm_skip. exact Hperm.
Qed.
Lemma complete_counts_to_can_insert__success_final :
  forall source pool target counts,
    (forall k, 0 <= k < Zlength source ->
      97 <= Znth k source 0 <= 122) ->
    (forall k, 0 <= k < Zlength target ->
      97 <= Znth k target 0 <= 122) ->
    (forall k, 0 <= k < Zlength pool ->
      97 <= Znth k pool 0 <= 122) ->
    IsSubsequence source target ->
    CountState source pool target
      (Zlength source) (Zlength pool) (Zlength target) counts ->
    NonnegativeCounts counts ->
    CanInsertFromPool source pool target.
Proof.
  intros source pool target counts Hsource Htarget Hpool
         Hsub Hstate Hnonneg.
  unfold IsSubsequence, PrefixEmbedding in Hsub.
  destruct Hsub as [positions [Hpositions_len [Hpositions_mono Hpositions]]].
  destruct (embedding_complement__success_final
              target source positions Hpositions_len Hpositions_mono Hpositions)
    as [inserted Hinserted].
  assert (Htarget_all : Forall (fun x => 97 <= x <= 122) target).
  { apply (proj2 (Forall_Znth (fun x => 97 <= x <= 122) 0 target)).
    exact Htarget. }
  rewrite Forall_forall in Htarget_all.
  assert (Htotal : forall x,
    (count_occ Z.eq_dec target x <=
     count_occ Z.eq_dec (source ++ pool) x)%nat).
  { intros x.
    destruct (Z_lt_le_dec x 97) as [Hxlo | Hxlo];
      [| destruct (Z_le_gt_dec x 122) as [Hxhi | Hxhi]].
    - assert (Hnotin : ~ In x target).
      { intros Hin.
        pose proof (Htarget_all x Hin). lia. }
      apply (proj1 (count_occ_not_In Z.eq_dec target x)) in Hnotin.
      rewrite Hnotin. lia.
    - destruct Hstate as [_ Hstate].
      specialize (Hstate (x - 97) ltac:(lia)).
      specialize (Hnonneg (x - 97) ltac:(lia)).
      rewrite (sublist_self source (Zlength source) eq_refl) in Hstate.
      rewrite (sublist_self pool (Zlength pool) eq_refl) in Hstate.
      rewrite (sublist_self target (Zlength target) eq_refl) in Hstate.
      replace (97 + (x - 97)) with x in Hstate by lia.
      unfold LetterCount in Hstate.
      rewrite count_occ_app.
      apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_add.
      lia.
    - assert (Hnotin : ~ In x target).
      { intros Hin.
        pose proof (Htarget_all x Hin). lia. }
      apply (proj1 (count_occ_not_In Z.eq_dec target x)) in Hnotin.
      rewrite Hnotin. lia. }
  assert (Hinserted_count : forall x,
    (count_occ Z.eq_dec inserted x <=
     count_occ Z.eq_dec pool x)%nat).
  { intros x.
    specialize (Htotal x).
    rewrite !count_occ_app in Htotal.
    pose proof ((proj1 (Permutation_count_occ Z.eq_dec _ _)) Hinserted x)
      as Hperm_count.
    rewrite count_occ_app in Hperm_count.
    lia. }
  destruct (multiset_inclusion_decompose__success_final
              inserted pool Hinserted_count) as [unused Hpool_perm].
  unfold CanInsertFromPool.
  exists inserted. split.
  - exists unused. exact Hpool_perm.
  - exists positions. split.
    + exact Hpositions_len.
    + split.
      * exact Hpositions.
      * split.
        -- exact Hpositions_mono.
        -- exact Hinserted.
Qed.
Lemma supply_shortage_excludes_can_insert__failure_final :
  forall source pool target,
    SupplyShortage source pool target ->
    ~ CanInsertFromPool source pool target.
Proof.
  intros source pool target [c [_ Hshort]].
  intros [inserted [[unused Hpool] [positions
    [Hpositions [Hitems [Hmono Htarget]]]]]].
  pose proof
    (proj1 (Permutation_count_occ Z.eq_dec pool (inserted ++ unused))
      Hpool (97 + c)) as Hpool_count.
  pose proof
    (proj1 (Permutation_count_occ Z.eq_dec (source ++ inserted) target)
      Htarget (97 + c)) as Htarget_count.
  unfold LetterCount in Hshort.
  rewrite count_occ_app, Nat2Z.inj_add in Hshort.
  rewrite <- Htarget_count in Hshort.
  rewrite count_occ_app, Nat2Z.inj_add in Hshort.
  rewrite Hpool_count in Hshort.
  rewrite count_occ_app, Nat2Z.inj_add in Hshort.
  pose proof (Nat2Z.is_nonneg (count_occ Z.eq_dec unused (97 + c))).
  lia.
Qed.
Lemma can_insert_implies_subsequence__failure_final :
  forall source pool target,
    CanInsertFromPool source pool target ->
    IsSubsequence source target.
Proof.
  intros source pool target
    [inserted [_ [positions [Hlen [Hitems [Hmono _]]]]]].
  unfold IsSubsequence, PrefixEmbedding.
  exists positions.
  split.
  - exact Hlen.
  - split.
    + exact Hmono.
    + exact Hitems.
Qed.
