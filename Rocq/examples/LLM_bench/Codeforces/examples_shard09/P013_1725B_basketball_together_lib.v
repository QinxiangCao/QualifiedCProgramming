Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Signature: solve_case(D:Z,powers:list Z)->Z. Output is the maximum number
   of disjoint teams whose size times their greatest member power exceeds D. *)
Definition CanWinTeams (p : list Z) (D wins : Z) : Prop :=
  exists team_of : Z -> Z,
    (forall i, 0 <= i < Zlength p -> 0 <= team_of i <= wins) /\
    (forall t, 1 <= t <= wins ->
      exists mx leader,
        0 <= leader < Zlength p /\ team_of leader = t /\ mx = Znth leader p 0 /\
        (forall i, 0 <= i < Zlength p -> team_of i = t -> Znth i p 0 <= mx) /\
        #(fun i : Z => 0 <= i < Zlength p /\ team_of i = t) * mx > D).
Definition Pre (D : Z) (p : list Z) : Prop :=
  (* Stated explicitly in the P013 solver Require, so dropped here:
       1 <= Zlength p <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) p /\
       1 <= D <= 1000000000   *)
  True.

Definition Spec (D : Z) (p : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (CanWinTeams p D) (fun x => x) out.

Definition TeamNeed (D power : Z) : Z := D / power + 1.

Definition BasketballGreedyPrefix
    (sorted : list Z) (D done used : Z) : Prop :=
  used = fold_right Z.add 0
    (map (TeamNeed D) (sublist 0 done sorted)).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Lemma permutation_preserves_zindexed_bounds__greedy_initialization :
  forall (xs ys : list Z) (lo hi : Z),
    Permutation xs ys ->
    (forall i, 0 <= i < Zlength xs -> lo <= Znth i xs 0 <= hi) ->
    forall j, 0 <= j < Zlength ys -> lo <= Znth j ys 0 <= hi.
Proof.
  intros xs ys lo hi Hperm Hbounds j Hj.
  assert (Hin_y : In (Znth j ys 0) ys).
  {
    unfold Znth.
    apply nth_In.
    replace (length ys) with (Z.to_nat (Zlength ys)).
    - apply Z2Nat.inj_lt; lia.
    - rewrite Zlength_correct. apply Nat2Z.id.
  }
  assert (Hin_x : In (Znth j ys 0) xs).
  {
    eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hin_y.
  }
  apply In_nth with (d := 0) in Hin_x as [k [Hk Hnth]].
  specialize (Hbounds (Z.of_nat k)).
  assert (HkZ : 0 <= Z.of_nat k < Zlength xs).
  {
    rewrite Zlength_correct.
    lia.
  }
  specialize (Hbounds HkZ).
  unfold Znth in Hbounds.
  rewrite Nat2Z.id in Hbounds.
  rewrite Hnth in Hbounds.
  exact Hbounds.
Qed.
Lemma basketball_greedy_prefix_zero__greedy_initialization :
  forall (sorted : list Z) (D : Z),
    BasketballGreedyPrefix sorted D 0 0.
Proof.
  intros sorted D.
  unfold BasketballGreedyPrefix.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.
Lemma basketball_greedy_prefix_succ__greedy_transition :
  forall (sorted : list Z) (D done used : Z),
    0 <= done < Zlength sorted ->
    BasketballGreedyPrefix sorted D done used ->
    BasketballGreedyPrefix sorted D (done + 1)
      (used + TeamNeed D (Znth done sorted 0)).
Proof.
  intros sorted D done used Hdone Hprefix.
  unfold BasketballGreedyPrefix in *.
  rewrite (sublist_split 0 (done + 1) done sorted) by lia.
  rewrite (sublist_single 0 done sorted) by lia.
  rewrite map_app, fold_right_app.
  simpl.
  assert (Hfold : forall (xs : list Z) z,
      fold_right Z.add z xs = fold_right Z.add 0 xs + z).
  {
    induction xs as [|x xs IH]; intros z; simpl.
    - lia.
    - rewrite IH. lia.
  }
  rewrite Hfold.
  lia.
Qed.
Lemma set_card_bijection__terminal_correctness :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q) (f : A -> B),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> exists x, P x /\ f x = y) ->
    (forall x y, P x -> P y -> f x = f y -> x = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmap Hsurj Hinj.
  assert (Hperm :
    Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  {
    apply NoDup_Permutation.
    - apply Injective_map_NoDup_in.
      + intros x y Hx Hy Hxy. apply Hinj.
        * apply (proj2 (@enum_ok A P FP x)). exact Hx.
        * apply (proj2 (@enum_ok A P FP y)). exact Hy.
        * exact Hxy.
      + exact (@enum_nodup A P FP).
    - exact (@enum_nodup B Q FQ).
    - intros y. rewrite in_map_iff.
      rewrite <- (@enum_ok B Q FQ y). split.
      + intros [x [Hfx Hxin]]. subst y. apply Hmap.
        apply (proj2 (@enum_ok A P FP x)). exact Hxin.
      + intros Hy. destruct (Hsurj y Hy) as [x [Hx Hfx]].
        exists x. split; [exact Hfx |].
        apply (proj1 (@enum_ok A P FP x)). exact Hx.
  }
  unfold set_card, SumLib.Sum.sum.
  assert (Hmap_fold :
    fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0
      (map f (@enum A P FP)) =
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
      (@enum A P FP)).
  {
    assert (Haux : forall xs : list A,
      fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0 (map f xs) =
      fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs).
    {
      induction xs as [|x xs IH].
      - reflexivity.
      - change
          (1 + fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0 (map f xs) =
           1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs).
        rewrite IH. reflexivity.
    }
    apply Haux.
  }
  rewrite <- Hmap_fold. clear Hmap_fold.
  induction Hperm.
  - reflexivity.
  - change
      (1 + fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0 l =
       1 + fold_right (fun (_ : B) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma permutation_index_iso__terminal_correctness : forall p q,
  Permutation p q ->
  exists f g,
    Zlength p = Zlength q /\
    (forall i, 0 <= i < Zlength p ->
      0 <= f i < Zlength q /\ g (f i) = i /\
      Znth (f i) q 0 = Znth i p 0) /\
    (forall j, 0 <= j < Zlength q ->
      0 <= g j < Zlength p /\ f (g j) = j /\
      Znth (g j) p 0 = Znth j q 0).
Proof.
  intros p q Hperm. induction Hperm.
  - exists (fun x => x), (fun x => x).
    simpl.
    repeat split; intros; try lia; reflexivity.
  - destruct IHHperm as [f [g [Hlen [Hf Hg]]]].
    exists (fun i => if Z.eq_dec i 0 then 0 else f (i - 1) + 1),
      (fun j => if Z.eq_dec j 0 then 0 else g (j - 1) + 1).
    rewrite !Zlength_cons. split; [lia |]. split.
    + intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hine]; simpl.
      * destruct (Z.eq_dec 0 0); [|contradiction].
        split; [lia |]. split; [reflexivity |]. rewrite !Znth0_cons. reflexivity.
      * destruct (Z.eq_dec i 0); [contradiction |].
        specialize (Hf (i - 1) ltac:(lia)) as [Hfr [Hgf Hval]].
        split; [lia |]. split.
        -- destruct (Z.eq_dec (f (i - 1) + 1) 0); [lia |].
           replace (f (i - 1) + 1 - 1) with (f (i - 1)) by lia.
           lia.
        -- rewrite !Znth_cons by lia.
           replace (f (i - 1) + 1 - 1) with (f (i - 1)) by lia.
           exact Hval.
    + intros j Hj. destruct (Z.eq_dec j 0) as [-> | Hjne]; simpl.
      * destruct (Z.eq_dec 0 0); [|contradiction].
        split; [lia |]. split; [reflexivity |]. rewrite !Znth0_cons. reflexivity.
      * destruct (Z.eq_dec j 0); [contradiction |].
        specialize (Hg (j - 1) ltac:(lia)) as [Hgr [Hfg Hval]].
        split; [lia |]. split.
        -- destruct (Z.eq_dec (g (j - 1) + 1) 0); [lia |].
           replace (g (j - 1) + 1 - 1) with (g (j - 1)) by lia.
           lia.
        -- rewrite !Znth_cons by lia.
           replace (g (j - 1) + 1 - 1) with (g (j - 1)) by lia.
           exact Hval.
  - exists (fun i => if Z.eq_dec i 0 then 1 else if Z.eq_dec i 1 then 0 else i),
      (fun i => if Z.eq_dec i 0 then 1 else if Z.eq_dec i 1 then 0 else i).
    pose proof (Zlength_nonneg l) as Hln.
    rewrite !Zlength_cons. split; [reflexivity |]. split.
    + intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hi0].
      * simpl. destruct (Z.eq_dec 0 0) as [_ | H]; [|lia].
        destruct (Z.eq_dec 1 0) as [H | _]; [lia |].
        destruct (Z.eq_dec 1 1) as [_ | H]; [|lia].
        split; [lia |]. split; [reflexivity |].
        rewrite Znth0_cons, Znth_cons by lia. replace (1 - 1) with 0 by lia.
        rewrite Znth0_cons. reflexivity.
      * destruct (Z.eq_dec i 1) as [-> | Hi1].
        -- simpl. destruct (Z.eq_dec 1 0) as [H | _]; [lia |].
           destruct (Z.eq_dec 1 1) as [_ | H]; [|lia].
           destruct (Z.eq_dec 0 0) as [_ | H]; [|lia].
           split; [lia |]. split; [reflexivity |].
           rewrite Znth0_cons, Znth_cons by lia. replace (1 - 1) with 0 by lia.
           rewrite Znth0_cons. reflexivity.
        -- simpl. destruct (Z.eq_dec i 0) as [H | _]; [contradiction |].
           destruct (Z.eq_dec i 1) as [H | _]; [contradiction |].
           split; [lia |]. split.
           ++ destruct (Z.eq_dec i 0) as [H | _]; [contradiction |].
              destruct (Z.eq_dec i 1) as [H | _]; [contradiction | reflexivity].
           ++ rewrite !Znth_cons by lia.
              replace (i - 1 - 1) with (i - 2) by lia. reflexivity.
    + intros j Hj. destruct (Z.eq_dec j 0) as [-> | Hj0].
      * simpl. destruct (Z.eq_dec 0 0) as [_ | H]; [|lia].
        destruct (Z.eq_dec 1 0) as [H | _]; [lia |].
        destruct (Z.eq_dec 1 1) as [_ | H]; [|lia].
        split; [lia |]. split; [reflexivity |].
        rewrite Znth0_cons, Znth_cons by lia. replace (1 - 1) with 0 by lia.
        rewrite Znth0_cons. reflexivity.
      * destruct (Z.eq_dec j 1) as [-> | Hj1].
        -- simpl. destruct (Z.eq_dec 1 0) as [H | _]; [lia |].
           destruct (Z.eq_dec 1 1) as [_ | H]; [|lia].
           destruct (Z.eq_dec 0 0) as [_ | H]; [|lia].
           split; [lia |]. split; [reflexivity |].
           rewrite Znth0_cons, Znth_cons by lia. replace (1 - 1) with 0 by lia.
           rewrite Znth0_cons. reflexivity.
        -- simpl. destruct (Z.eq_dec j 0) as [H | _]; [contradiction |].
           destruct (Z.eq_dec j 1) as [H | _]; [contradiction |].
           split; [lia |]. split.
           ++ destruct (Z.eq_dec j 0) as [H | _]; [contradiction |].
              destruct (Z.eq_dec j 1) as [H | _]; [contradiction | reflexivity].
           ++ rewrite !Znth_cons by lia.
              replace (j - 1 - 1) with (j - 2) by lia. reflexivity.
  - destruct IHHperm1 as [f1 [g1 [Hlen1 [Hf1 Hg1]]]].
    destruct IHHperm2 as [f2 [g2 [Hlen2 [Hf2 Hg2]]]].
    exists (fun i => f2 (f1 i)), (fun j => g1 (g2 j)).
    split; [lia |]. split.
    + intros i Hi. specialize (Hf1 i Hi) as [Hr1 [Hinv1 Hv1]].
      specialize (Hf2 (f1 i) Hr1) as [Hr2 [Hinv2 Hv2]].
      split; [exact Hr2 |]. split.
      * rewrite Hinv2, Hinv1. reflexivity.
      * rewrite Hv2, Hv1. reflexivity.
    + intros j Hj. specialize (Hg2 j Hj) as [Hr2 [Hinv2 Hv2]].
      specialize (Hg1 (g2 j) Hr2) as [Hr1 [Hinv1 Hv1]].
      split; [exact Hr1 |]. split.
      * rewrite Hinv1, Hinv2. reflexivity.
      * rewrite Hv1, Hv2. reflexivity.
Qed.
Lemma can_win_teams_permutation__terminal_correctness : forall p q D k,
  Permutation p q -> CanWinTeams p D k -> CanWinTeams q D k.
Proof.
  intros p q D k Hperm [team_of [Hbounds Hteams]].
  destruct (permutation_index_iso__terminal_correctness p q Hperm)
    as [f [g [Hlen [Hf Hg]]]].
  exists (fun j => team_of (g j)). split.
  - intros j Hj. destruct (Hg j Hj) as [Hgj _]. apply Hbounds. exact Hgj.
  - intros t Ht. destruct (Hteams t Ht)
      as [mx [leader [Hleader [Htlabel [Hmx [Hmax Hsize]]]]]].
    exists mx, (f leader). split.
    + apply Hf. exact Hleader.
    + split.
      * destruct (Hf leader Hleader) as [_ [Hgf _]]. simpl. rewrite Hgf. exact Htlabel.
      * split.
        -- destruct (Hf leader Hleader) as [_ [_ Hval]]. rewrite Hval. exact Hmx.
        -- split.
           ++ intros j Hj Hjteam. destruct (Hg j Hj) as [Hgj [_ Hval]].
              rewrite <- Hval. apply Hmax; [exact Hgj | exact Hjteam].
           ++ assert (Hcard :
                #(fun i : Z => 0 <= i < Zlength p /\ team_of i = t) =
                #(fun j : Z => 0 <= j < Zlength q /\ team_of (g j) = t)).
              {
                apply (set_card_bijection__terminal_correctness
                  (fun i : Z => 0 <= i < Zlength p /\ team_of i = t)
                  (fun j : Z => 0 <= j < Zlength q /\ team_of (g j) = t)
                  _ _ f).
                - intros i [Hi Hit]. destruct (Hf i Hi) as [Hfi [Hgfi _]].
                  split; [exact Hfi | simpl; rewrite Hgfi; exact Hit].
                - intros j [Hj Hjt]. exists (g j). destruct (Hg j Hj) as [Hgj [Hfgj _]].
                  split; [split; assumption | exact Hfgj].
                - intros i1 i2 [Hi1 _] [Hi2 _] Heq.
                  destruct (Hf i1 Hi1) as [_ [Hgi1 _]].
                  destruct (Hf i2 Hi2) as [_ [Hgi2 _]].
                  rewrite <- Hgi1, <- Hgi2, Heq. reflexivity.
              }
              rewrite <- Hcard. exact Hsize.
Qed.
Lemma set_card_Z_as_sum__terminal_correctness : forall low high P,
  #(fun z : Z => low <= z < high /\ P z) =
  SumLib.Sum.sum (fun z : Z => low <= z < high)
    (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P. unfold set_card, SumLib.Sum.sum.
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
Lemma fold_Zsum_add__terminal_correctness : forall {A} (l : list A) f g,
  fold_right (fun x acc => f x + acc) 0 l +
  fold_right (fun x acc => g x + acc) 0 l =
  fold_right (fun x acc => (f x + g x) + acc) 0 l.
Proof.
  intros A l f g. induction l as [|x xs IH]; simpl; [lia |].
  rewrite <- IH. lia.
Qed.
Lemma fold_Zsum_swap__terminal_correctness :
  forall {A B} (la : list A) (lb : list B) (f : A -> B -> Z),
  fold_right (fun a acc =>
    fold_right (fun b acc' => f a b + acc') 0 lb + acc) 0 la =
  fold_right (fun b acc =>
    fold_right (fun a acc' => f a b + acc') 0 la + acc) 0 lb.
Proof.
  intros A B la. induction la as [|a la IH]; intros lb f; simpl.
  - induction lb; simpl; [reflexivity | exact IHlb].
  - rewrite IH. apply fold_Zsum_add__terminal_correctness.
Qed.
Lemma sum_Z_range_swap__terminal_correctness : forall alo ahi blo bhi f,
  SumLib.Sum.sum (fun a : Z => alo <= a < ahi)
    (fun a => SumLib.Sum.sum (fun b : Z => blo <= b < bhi) (fun b => f a b)) =
  SumLib.Sum.sum (fun b : Z => blo <= b < bhi)
    (fun b => SumLib.Sum.sum (fun a : Z => alo <= a < ahi) (fun a => f a b)).
Proof.
  intros. unfold SumLib.Sum.sum. cbn [finite_Z_range].
  apply fold_Zsum_swap__terminal_correctness.
Qed.
Lemma indicator_range_sum_le_one__terminal_correctness : forall low high v,
  low <= high ->
  SumLib.Sum.sum (fun t : Z => low <= t < high)
    (fun t => if prop_dec (v = t) then 1 else 0) <= 1.
Proof.
  intros low high v Hrange.
  destruct (Z_lt_le_dec v low) as [Hv | Hv].
  - rewrite sum_Z_range_eq_zero.
    + lia.
    + intros t Ht. destruct (prop_dec (v = t)); [lia | reflexivity].
  - destruct (Z_lt_ge_dec v high) as [Hvh | Hvh].
    + rewrite (sum_Z_range_split low v high) by lia.
      rewrite sum_Z_range_eq_zero.
      2:{ intros t Ht. destruct (prop_dec (v = t)); [lia | reflexivity]. }
      rewrite sum_Z_range_cons by lia.
      destruct (prop_dec (v = v)); [|contradiction].
      rewrite sum_Z_range_eq_zero.
      2:{ intros t Ht. destruct (prop_dec (v = t)); [lia | reflexivity]. }
      lia.
    + assert (Hz : SumLib.Sum.sum (fun t : Z => low <= t < high)
          (fun t => if prop_dec (v = t) then 1 else 0) = 0).
      { apply sum_Z_range_eq_zero. intros t Ht.
        destruct (prop_dec (v = t)); [lia | reflexivity]. }
      rewrite Hz. lia.
Qed.
Lemma list_sum_permutation__terminal_correctness : forall l1 l2,
  Permutation l1 l2 -> ListLib.sum l1 = ListLib.sum l2.
Proof.
  intros l1 l2 H. induction H; simpl.
  - reflexivity.
  - lia.
  - lia.
  - lia.
Qed.
Lemma increasing_nodup_Znth_lower__terminal_correctness :
  forall (l : list Z) (base : Z),
  ListLib.increasing l -> NoDup l -> Forall (fun x => base <= x) l ->
  forall j, 0 <= j < Zlength l -> base + j <= Znth j l 0.
Proof.
  induction l as [|a l IH]; intros base Hinc Hnd Hlow j Hj.
  - rewrite Zlength_nil in Hj. lia.
  - inversion Hnd as [|? ? Hnotin Hnd']; subst.
    inversion Hlow as [|? ? Ha Hlow']; subst.
    destruct (Z.eq_dec j 0) as [-> | Hj0].
    + rewrite Znth0_cons. lia.
    + assert (Htailinc : ListLib.increasing l).
      { apply ListLib.increasing_aux_tail_increasing with (x := a). exact Hinc. }
      assert (Htaillow : Forall (fun x => base + 1 <= x) l).
      {
        apply Forall_forall. intros x Hx.
        pose proof (ListLib.increasing_aux_head_le_all_In l a x Hinc Hx) as Hax.
        assert (a <> x) by (intro Heq; subst x; contradiction).
        lia.
      }
      specialize (IH (base + 1) Htailinc Hnd' Htaillow (j - 1)).
      rewrite Zlength_cons in Hj.
      specialize (IH ltac:(lia)).
      rewrite Znth_cons by lia.
      replace (j - 1) with (j - 1) by reflexivity. lia.
Qed.
Lemma nodup_sorted_indices_rank__terminal_correctness :
  forall (inds : list Z) (n : Z),
  NoDup inds -> Forall (fun x => 0 <= x < n) inds ->
  forall j, 0 <= j < Zlength inds ->
    j <= Znth j (ListLib.sort inds) 0 < n.
Proof.
  intros inds n Hnd Hrange j Hj.
  pose proof (ListLib.sort_list_perm inds) as Hperm.
  assert (Hlen : Zlength (ListLib.sort inds) = Zlength inds).
  { rewrite !Zlength_correct. apply Permutation_length in Hperm. lia. }
  assert (Hndsort : NoDup (ListLib.sort inds)).
  { eapply Permutation_NoDup; [exact Hperm | exact Hnd]. }
  assert (Hrangesort : Forall (fun x => 0 <= x < n) (ListLib.sort inds)).
  {
    apply Forall_forall. intros x Hx.
    apply Forall_forall with (x := x) in Hrange; [exact Hrange |].
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
  }
  split.
  - eapply increasing_nodup_Znth_lower__terminal_correctness with (base := 0).
    + apply ListLib.sort_list_increasing.
    + exact Hndsort.
    + apply Forall_forall. intros x Hx.
      rewrite Forall_forall in Hrangesort. specialize (Hrangesort x Hx). lia.
    + lia.
  - pose proof (proj1 (Forall_Znth (fun x : Z => 0 <= x < n) 0
        (ListLib.sort inds)) Hrangesort) as Hnth.
    assert (Hj' : 0 <= j < Zlength (ListLib.sort inds)).
    { rewrite Hlen. exact Hj. }
    specialize (Hnth j Hj'). exact (proj2 Hnth).
Qed.
Lemma monotone_selected_sum__terminal_correctness :
  forall (g : Z -> Z) (inds : list Z) (k n : Z),
  Zlength inds = k -> 0 <= k ->
  NoDup inds -> Forall (fun x => 0 <= x < n) inds ->
  (forall a b, 0 <= a -> a <= b -> b < n -> g a <= g b) ->
  SumLib.Sum.sum (fun j : Z => 0 <= j < k) g <=
  ListLib.sum (map g inds).
Proof.
  intros g inds k n Hlen Hk Hnd Hrange Hmono.
  pose proof (ListLib.sort_list_perm inds) as Hperm.
  assert (Hlen_sort : Zlength (ListLib.sort inds) = k).
  { rewrite <- Hlen. rewrite !Zlength_correct. apply Permutation_length in Hperm. lia. }
  assert (Hpoint : forall j, 0 <= j < k ->
      g j <= g (Znth j (ListLib.sort inds) 0)).
  {
    intros j Hj. destruct (nodup_sorted_indices_rank__terminal_correctness
      inds n Hnd Hrange j ltac:(lia)) as [Hrank Hupper].
    apply Hmono; lia.
  }
  eapply Z.le_trans.
  - apply sum_Z_range_le. exact Hpoint.
  - rewrite <- Hlen_sort.
    rewrite <- (list_sum_map_as_Z_range_sum 0 g (ListLib.sort inds)).
    apply Z.eq_le_incl. apply list_sum_permutation__terminal_correctness.
    apply Permutation_map. apply Permutation_sym. exact Hperm.
Qed.
Lemma TeamNeed_positive__terminal_correctness : forall D p,
  0 <= D -> 0 < p -> 1 <= TeamNeed D p.
Proof.
  intros D p HD Hp. unfold TeamNeed.
  pose proof (Z_div_nonneg_nonneg D p HD ltac:(lia)). lia.
Qed.
Lemma TeamNeed_antitone__terminal_correctness : forall D p q,
  0 <= D -> 0 < p <= q -> TeamNeed D q <= TeamNeed D p.
Proof.
  intros D p q HD Hpq. unfold TeamNeed.
  pose proof (Z.div_le_compat_l D p q HD Hpq). lia.
Qed.
Lemma Zlength_map__terminal_correctness : forall {A B} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Zlength_Zrange_aux__terminal_correctness : forall low count,
  Zlength (Zrange_aux low count) = Z.of_nat count.
Proof.
  intros low count. revert low. induction count as [|count IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__terminal_correctness : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__terminal_correctness. lia.
Qed.
Lemma Znth_Zrange_aux__terminal_correctness : forall count low i,
  0 <= i < Z.of_nat count ->
  Znth i (Zrange_aux low count) 0 = low + i.
Proof.
  induction count as [|count IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__terminal_correctness : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__terminal_correctness by lia. lia.
Qed.
Lemma list_sum_map_Zrange__terminal_correctness : forall low high f,
  low <= high ->
  ListLib.sum (map f (Zrange low high)) =
  SumLib.Sum.sum (fun x : Z => low <= x < high) f.
Proof.
  intros low high f Hle.
  rewrite (list_sum_map_as_Z_range_sum 0 f (Zrange low high)).
  rewrite Zlength_Zrange__terminal_correctness by exact Hle.
  transitivity (SumLib.Sum.sum (fun x : Z => 0 <= x < high - low)
    (fun x => f (x + low))).
  - apply sum_Z_range_ext. intros i Hi.
    rewrite Znth_Zrange__terminal_correctness by lia. f_equal. lia.
  -
  rewrite <- (sum_Z_range_shift 0 (high - low) low f).
    replace (0 + low) with low by lia.
    replace (high - low + low) with high by lia. reflexivity.
Qed.
Lemma basketball_prefix_as_sum__terminal_correctness : forall sorted D k,
  0 <= k <= Zlength sorted ->
  fold_right Z.add 0 (map (TeamNeed D) (sublist 0 k sorted)) =
  SumLib.Sum.sum (fun j : Z => 0 <= j < k)
    (fun j => TeamNeed D (Znth j sorted 0)).
Proof.
  intros sorted D k Hk. change (ListLib.sum
    (map (TeamNeed D) (sublist 0 k sorted)) =
    SumLib.Sum.sum (fun j : Z => 0 <= j < k)
      (fun j => TeamNeed D (Znth j sorted 0))).
  rewrite (list_sum_map_as_Z_range_sum 0 (TeamNeed D) (sublist 0 k sorted)).
  rewrite Zlength_sublist by lia.
  replace (k - 0) with k by lia.
  apply sum_Z_range_ext. intros j Hj.
  rewrite Znth_sublist by lia. replace (j + 0) with j by lia. reflexivity.
Qed.
Lemma greedy_prefix_lower_bound_for_any_teams__terminal_correctness :
  forall sorted D n k,
  1 <= n -> Zlength sorted = n -> 1 <= D ->
  (forall j, 0 <= j < n -> 1 <= Znth j sorted 0) ->
  mono_noninc sorted -> CanWinTeams sorted D k ->
  fold_right Z.add 0
    (map (TeamNeed D) (sublist 0 k sorted)) <= n.
Proof.
  intros sorted D n k Hn Hlen HD Hpositive Hmono
    [team_of [Hbounds Hteams]].
  assert (Hk : 0 <= k).
  { specialize (Hbounds 0 ltac:(lia)). lia. }
  assert (Hk_le_n : k <= n).
  {
    (* Distinct team leaders embed the labels [1,k] into player indices. *)
    set (leader := fun t : Z =>
      epsilon (inhabits 0) (fun r => exists mx,
        0 <= r < Zlength sorted /\ team_of r = t /\
        mx = Znth r sorted 0 /\
        (forall i, 0 <= i < Zlength sorted -> team_of i = t ->
          Znth i sorted 0 <= mx) /\
        #(fun i : Z => 0 <= i < Zlength sorted /\ team_of i = t) * mx > D)).
    assert (Hleader : forall t, 1 <= t <= k ->
      exists mx,
        0 <= leader t < Zlength sorted /\ team_of (leader t) = t /\
        mx = Znth (leader t) sorted 0 /\
        (forall i, 0 <= i < Zlength sorted -> team_of i = t ->
          Znth i sorted 0 <= mx) /\
        #(fun i : Z => 0 <= i < Zlength sorted /\ team_of i = t) * mx > D).
    {
      intros t Ht. unfold leader. apply epsilon_spec.
      destruct (Hteams t Ht) as [mx [r [Hr [Hrt [Hmx [Hmax Hcard]]]]]].
      exists r, mx. split; [exact Hr |]. split; [exact Hrt |].
      split; [exact Hmx |]. split; assumption.
    }
    set (inds := map leader (Zrange 1 (k + 1))).
    assert (Hnd : NoDup inds).
    {
      unfold inds. apply Injective_map_NoDup_in.
      - intros x y Hxin Hyin Heq.
        apply (proj2 (In_Zrange 1 (k + 1) x)) in Hxin.
        apply (proj2 (In_Zrange 1 (k + 1) y)) in Hyin.
        destruct (Hleader x ltac:(lia)) as [mx [Hrx [Htx _]]].
        destruct (Hleader y ltac:(lia)) as [my [Hry [Hty _]]].
        rewrite Heq in Htx. rewrite Htx in Hty. exact Hty.
      - apply NoDup_Zrange.
    }
    assert (Hrange : Forall (fun x => 0 <= x < n) inds).
    {
      unfold inds. rewrite Forall_forall. intros x Hx.
      apply in_map_iff in Hx as [t [Htx Ht]]. subst x.
      apply (proj2 (In_Zrange 1 (k + 1) t)) in Ht.
      destruct (Hleader t ltac:(lia)) as [mx [Hr _]]. rewrite Hlen in Hr. exact Hr.
    }
    assert (Hincl : incl inds (Zrange 0 n)).
    { intros x Hx. apply (proj1 (In_Zrange 0 n x)).
      rewrite Forall_forall in Hrange. apply Hrange. exact Hx. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hcount.
    unfold inds in Hcount. rewrite length_map in Hcount.
    apply Nat2Z.inj_le in Hcount.
    rewrite <- !Zlength_correct in Hcount.
    rewrite !Zlength_Zrange__terminal_correctness in Hcount by lia. lia.
  }
  rewrite basketball_prefix_as_sum__terminal_correctness by lia.
  set (leader := fun t : Z =>
    epsilon (inhabits 0) (fun r => exists mx,
      0 <= r < Zlength sorted /\ team_of r = t /\
      mx = Znth r sorted 0 /\
      (forall i, 0 <= i < Zlength sorted -> team_of i = t ->
        Znth i sorted 0 <= mx) /\
      #(fun i : Z => 0 <= i < Zlength sorted /\ team_of i = t) * mx > D)).
  assert (Hleader : forall t, 1 <= t <= k ->
    exists mx,
      0 <= leader t < Zlength sorted /\ team_of (leader t) = t /\
      mx = Znth (leader t) sorted 0 /\
      (forall i, 0 <= i < Zlength sorted -> team_of i = t ->
        Znth i sorted 0 <= mx) /\
      #(fun i : Z => 0 <= i < Zlength sorted /\ team_of i = t) * mx > D).
  {
    intros t Ht. unfold leader. apply epsilon_spec.
    destruct (Hteams t Ht) as [mx [r [Hr [Hrt [Hmx [Hmax Hcard]]]]]].
    exists r, mx. split; [exact Hr |]. split; [exact Hrt |].
    split; [exact Hmx |]. split; assumption.
  }
  set (inds := map leader (Zrange 1 (k + 1))).
  assert (Hinds_len : Zlength inds = k).
  { unfold inds. rewrite Zlength_map__terminal_correctness.
    rewrite Zlength_Zrange__terminal_correctness by lia. lia. }
  assert (Hinds_nd : NoDup inds).
  {
    unfold inds. apply Injective_map_NoDup_in.
    - intros x y Hxin Hyin Heq.
      apply (proj2 (In_Zrange 1 (k + 1) x)) in Hxin.
      apply (proj2 (In_Zrange 1 (k + 1) y)) in Hyin.
      destruct (Hleader x ltac:(lia)) as [mx [Hrx [Htx _]]].
      destruct (Hleader y ltac:(lia)) as [my [Hry [Hty _]]].
      rewrite Heq in Htx. rewrite Htx in Hty. exact Hty.
    - apply NoDup_Zrange.
  }
  assert (Hinds_range : Forall (fun x => 0 <= x < n) inds).
  {
    unfold inds. rewrite Forall_forall. intros x Hx.
    apply in_map_iff in Hx as [t [Htx Ht]]. subst x.
    apply (proj2 (In_Zrange 1 (k + 1) t)) in Ht.
    destruct (Hleader t ltac:(lia)) as [mx [Hr _]]. rewrite Hlen in Hr. exact Hr.
  }
  set (g := fun r => TeamNeed D (Znth r sorted 0)).
  assert (Hgmono : forall a b, 0 <= a -> a <= b -> b < n -> g a <= g b).
  {
    intros a b Ha Hab Hb. unfold g.
    assert (Hpa := Hpositive a ltac:(lia)).
    assert (Hpb := Hpositive b ltac:(lia)).
    pose proof (Hmono a b Ha Hab ltac:(rewrite Hlen; lia)) as Hpow.
    apply TeamNeed_antitone__terminal_correctness; lia.
  }
  eapply Z.le_trans.
  - apply (monotone_selected_sum__terminal_correctness g inds k n
      Hinds_len Hk Hinds_nd Hinds_range Hgmono).
  - unfold inds. rewrite map_map.
    rewrite list_sum_map_Zrange__terminal_correctness by lia.
    eapply Z.le_trans.
    + apply sum_Z_range_le. intros t Ht.
      destruct (Hleader t ltac:(lia))
        as [mx [Hr [Hteam [Hmx [Hmax Hcard]]]]].
      unfold g. rewrite <- Hmx.
      assert (Hmxpos : 0 < mx).
      { rewrite Hmx.
        pose proof (Hpositive (leader t) ltac:(rewrite <- Hlen; exact Hr)).
        lia. }
      unfold TeamNeed.
      assert (Hdiv : D / mx <
        #(fun i : Z => 0 <= i < Zlength sorted /\ team_of i = t)).
      { apply Z.div_lt_upper_bound; lia. }
      replace (D / mx + 1) with (Z.succ (D / mx)) by lia.
      exact (Zlt_le_succ _ _ Hdiv).
    + eapply Z.le_trans.
      * apply Z.eq_le_incl. apply sum_Z_range_ext. intros t Ht.
        apply set_card_Z_as_sum__terminal_correctness.
      * rewrite sum_Z_range_swap__terminal_correctness.
        eapply Z.le_trans.
        -- apply sum_Z_range_le. intros i Hi.
           apply indicator_range_sum_le_one__terminal_correctness. lia.
        -- rewrite sum_Z_range_const by lia. lia.
Qed.
Lemma set_card_Z_range__terminal_correctness : forall low high,
  low <= high -> #(fun z : Z => low <= z < high) = high - low.
Proof.
  intros low high Hrange.
  transitivity (#(fun z : Z => low <= z < high /\ True)).
  - eapply set_card_bijection__terminal_correctness with (f := fun z : Z => z).
    + intuition.
    + intros y Hy. exists y. intuition.
    + intros x y Hx Hy Hxy. exact Hxy.
  - rewrite set_card_Z_as_sum__terminal_correctness.
    destruct (prop_dec True) as [_ | Hfalse]; [|contradiction].
    rewrite sum_Z_range_const by lia. lia.
Qed.
Lemma can_win_teams_of_greedy_prefix__terminal_correctness :
  forall sorted D n done,
  1 <= n -> Zlength sorted = n -> 1 <= D ->
  (forall j, 0 <= j < n -> 1 <= Znth j sorted 0) ->
  mono_noninc sorted -> 0 <= done <= n ->
  fold_right Z.add 0
    (map (TeamNeed D) (sublist 0 done sorted)) <= n ->
  CanWinTeams sorted D done.
Proof.
  intros sorted D n done Hn Hlen HD Hpositive Hmono Hdone Hused.
  set (need := fun j => TeamNeed D (Znth j sorted 0)).
  set (pref := fun t => SumLib.Sum.sum (fun j : Z => 0 <= j < t) need).
  assert (Hpref_used : pref done <= n).
  { unfold pref, need. rewrite <- basketball_prefix_as_sum__terminal_correctness by lia.
    exact Hused. }
  assert (Hneed_pos : forall j, 0 <= j < done -> 1 <= need j).
  { intros j Hj. unfold need. apply TeamNeed_positive__terminal_correctness; [lia |].
    pose proof (Hpositive j ltac:(lia)). lia. }
  assert (Hpref_step : forall t, 1 <= t <= done ->
      pref t = pref (t - 1) + need (t - 1)).
  { intros t Ht. unfold pref.
    pose proof (sum_Z_range_extend_right 0 (t - 1) need ltac:(lia)) as Hstep.
    replace (t - 1 + 1) with t in Hstep by lia. exact Hstep. }
  assert (Hoffset_mono : forall a b, 0 <= a -> a <= b -> b <= done ->
      pref a - a <= pref b - b).
  {
    intros a b Ha Hab Hb.
    assert (Hsplit := sum_Z_range_split 0 a b need ltac:(lia)).
    assert (Hlower : b - a <=
      SumLib.Sum.sum (fun j : Z => a <= j < b) need).
    { replace (b - a) with ((b - a) * 1) by lia.
      apply sum_Z_range_lower_bound; [lia |].
      intros j Hj. apply Hneed_pos. lia. }
    unfold pref. lia.
  }
  set (fstart := fun t => done + pref (t - 1) - (t - 1)).
  set (fend := fun t => done + pref t - t).
  set (group := fun t i => i = t - 1 \/ fstart t <= i < fend t).
  assert (Hfend_step : forall t, 1 <= t <= done ->
      fend t = fstart t + need (t - 1) - 1).
  { intros t Ht. unfold fend, fstart. rewrite Hpref_step by exact Ht. lia. }
  assert (Hpref0 : pref 0 = 0).
  { unfold pref. apply sum_Z_range_empty. lia. }
  assert (Hfstart_ge : forall t, 1 <= t <= done -> done <= fstart t).
  { intros t Ht. unfold fstart.
    pose proof (Hoffset_mono 0 (t - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    rewrite Hpref0 in H. lia. }
  assert (Hgroup_bounds : forall t i, 1 <= t <= done -> group t i -> 0 <= i < n).
  {
    intros t i Ht Hi. unfold group in Hi. destruct Hi as [-> | Hi].
    - lia.
    - assert (Hstart : done <= fstart t) by (apply Hfstart_ge; exact Ht).
      assert (Hend : fend t <= pref done).
      { unfold fend. pose proof (Hoffset_mono t done ltac:(lia) ltac:(lia) ltac:(lia)).
        lia. }
      lia.
  }
  assert (Hgroup_unique : forall t u i,
      1 <= t <= done -> 1 <= u <= done -> group t i -> group u i -> t = u).
  {
    intros t u i Ht Hu Hti Hui.
    destruct (Z.lt_trichotomy t u) as [Htu | [Heq | Hut]]; [|exact Heq|].
    - unfold group in Hti, Hui.
      destruct Hti as [Hleader_t | Hfill_t]; destruct Hui as [Hleader_u | Hfill_u].
      + lia.
      + assert (Hsu : done <= fstart u).
        { apply Hfstart_ge. exact Hu. }
        lia.
      + assert (Hst : done <= fstart t).
        { apply Hfstart_ge. exact Ht. }
        lia.
      + assert (Hsep : fend t <= fstart u).
        { unfold fend, fstart.
          pose proof (Hoffset_mono t (u - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
        lia.
    - unfold group in Hti, Hui.
      destruct Hti as [Hleader_t | Hfill_t]; destruct Hui as [Hleader_u | Hfill_u].
      + lia.
      + assert (Hsu : done <= fstart u).
        { apply Hfstart_ge. exact Hu. }
        lia.
      + assert (Hst : done <= fstart t).
        { apply Hfstart_ge. exact Ht. }
        lia.
      + assert (Hsep : fend u <= fstart t).
        { unfold fend, fstart.
          pose proof (Hoffset_mono u (t - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
        lia.
  }
  set (team_of := fun i =>
    if prop_dec (exists t, 1 <= t <= done /\ group t i)
    then epsilon (inhabits 0) (fun t => 1 <= t <= done /\ group t i)
    else 0).
  assert (Hteam_group : forall t i, 1 <= t <= done -> group t i -> team_of i = t).
  {
    intros t i Ht Hgi. unfold team_of.
    destruct (prop_dec (exists u, 1 <= u <= done /\ group u i)) as [Hex | Hnone].
    - pose proof (epsilon_spec (inhabits 0)
        (fun u => 1 <= u <= done /\ group u i) Hex) as Heps.
      destruct Heps as [Hepsr Hepsg].
      eapply Hgroup_unique; eauto.
    - exfalso. apply Hnone. exists t. auto.
  }
  assert (Hteam_inv : forall t i, 1 <= t <= done -> team_of i = t -> group t i).
  {
    intros t i Ht Hti. unfold team_of in Hti.
    destruct (prop_dec (exists u, 1 <= u <= done /\ group u i)) as [Hex | Hnone].
    - pose proof (epsilon_spec (inhabits 0)
        (fun u => 1 <= u <= done /\ group u i) Hex) as Heps.
      destruct Heps as [Hepsr Hepsg]. rewrite Hti in Hepsg. exact Hepsg.
    - lia.
  }
  exists team_of. split.
  - intros i Hi. unfold team_of.
    destruct (prop_dec (exists t, 1 <= t <= done /\ group t i)) as [Hex | Hnone].
    + pose proof (epsilon_spec (inhabits 0)
        (fun t => 1 <= t <= done /\ group t i) Hex) as Heps.
      destruct Heps as [[Heps_lo Heps_hi] Heps_group]. lia.
    + lia.
  - intros t Ht.
    exists (Znth (t - 1) sorted 0), (t - 1).
    assert (Hleader_range : 0 <= t - 1 < Zlength sorted) by (rewrite Hlen; lia).
    split; [exact Hleader_range |].
    split.
    + apply Hteam_group; [exact Ht |]. unfold group. auto.
    + split; [reflexivity |]. split.
      * intros i Hi Hteam.
        apply Hteam_inv in Hteam; [|exact Ht]. unfold group in Hteam.
        destruct Hteam as [-> | Hfill]; [lia |].
        assert (Hstart : done <= fstart t).
        { apply Hfstart_ge. exact Ht. }
        pose proof (Hmono (t - 1) i ltac:(lia) ltac:(lia)
          (proj2 Hi)) as Hpower.
        lia.
      * assert (Hcard :
          #(fun i : Z => 0 <= i < Zlength sorted /\ team_of i = t) = need (t - 1)).
        {
          assert (Hneed : 1 <= need (t - 1)) by (apply Hneed_pos; lia).
          set (slot_to_index := fun s : Z =>
            if Z.eq_dec s 0 then t - 1 else fstart t + (s - 1)).
          assert (Hbijection :
            #(fun s : Z => 0 <= s < need (t - 1)) =
            #(fun i : Z => 0 <= i < Zlength sorted /\ team_of i = t)).
          {
            eapply set_card_bijection__terminal_correctness with (f := slot_to_index).
            - intros s Hs. assert (Hgroup : group t (slot_to_index s)).
              { unfold slot_to_index. destruct (Z.eq_dec s 0) as [-> | Hs0].
                + unfold group. auto.
                + right. unfold fend.
                  rewrite Hpref_step by lia. unfold fstart. lia. }
              split.
              + rewrite Hlen. apply Hgroup_bounds with (t := t); assumption.
              + apply Hteam_group; assumption.
            - intros i [Hi Hteam].
              apply Hteam_inv in Hteam; [|exact Ht]. unfold group in Hteam.
              destruct Hteam as [Hleader | Hfill].
              + exists 0. split; [lia |]. unfold slot_to_index.
                destruct (Z.eq_dec 0 0); [symmetry; exact Hleader | contradiction].
              + exists (i - fstart t + 1). split.
                -- rewrite Hfend_step in Hfill by exact Ht. lia.
                -- unfold slot_to_index.
                   destruct (Z.eq_dec (i - fstart t + 1) 0); lia.
            - intros x y Hx Hy Hxy. unfold slot_to_index in Hxy.
              destruct (Z.eq_dec x 0) as [-> | Hx0];
              destruct (Z.eq_dec y 0) as [-> | Hy0]; try reflexivity.
              + assert (Hstart : done <= fstart t).
                { apply Hfstart_ge. exact Ht. }
                lia.
              + assert (Hstart : done <= fstart t).
                { apply Hfstart_ge. exact Ht. }
                lia.
              + lia.
          }
          rewrite <- Hbijection.
          rewrite set_card_Z_range__terminal_correctness by lia. lia.
        }
        rewrite Hcard. unfold need, TeamNeed.
        set (p := Znth (t - 1) sorted 0).
        assert (Hp : 0 < p).
        { unfold p. pose proof (Hpositive (t - 1) ltac:(lia)). lia. }
        pose proof (Z.div_mod D p ltac:(lia)) as Hdivmod.
        pose proof (Z.mod_pos_bound D p Hp) as Hmod.
        nia.
Qed.
Lemma can_win_teams_count_le_length__terminal_correctness : forall p D k,
  1 <= Zlength p -> CanWinTeams p D k -> k <= Zlength p.
Proof.
  intros p D k Hlen [team_of [Hbounds Hteams]].
  assert (Hk : 0 <= k).
  { specialize (Hbounds 0 ltac:(lia)). lia. }
  set (leader := fun t : Z =>
    epsilon (inhabits 0) (fun r => exists mx,
      0 <= r < Zlength p /\ team_of r = t /\
      mx = Znth r p 0 /\
      (forall i, 0 <= i < Zlength p -> team_of i = t ->
        Znth i p 0 <= mx) /\
      #(fun i : Z => 0 <= i < Zlength p /\ team_of i = t) * mx > D)).
  assert (Hleader : forall t, 1 <= t <= k ->
      0 <= leader t < Zlength p /\ team_of (leader t) = t).
  {
    intros t Ht. unfold leader.
    destruct (Hteams t Ht) as [mx [r [Hr [Hrt [Hmx [Hmax Hcard]]]]]].
    assert (Hex : exists r, exists mx,
        0 <= r < Zlength p /\ team_of r = t /\
        mx = Znth r p 0 /\
        (forall i, 0 <= i < Zlength p -> team_of i = t ->
          Znth i p 0 <= mx) /\
        #(fun i : Z => 0 <= i < Zlength p /\ team_of i = t) * mx > D).
    { exists r, mx. split; [exact Hr |]. split; [exact Hrt |].
      split; [exact Hmx |]. split; assumption. }
    pose proof (epsilon_spec (inhabits 0)
      (fun r => exists mx,
        0 <= r < Zlength p /\ team_of r = t /\
        mx = Znth r p 0 /\
        (forall i, 0 <= i < Zlength p -> team_of i = t ->
          Znth i p 0 <= mx) /\
        #(fun i : Z => 0 <= i < Zlength p /\ team_of i = t) * mx > D)
      Hex) as Hspec.
    destruct Hspec as [mx' [Hr' [Hrt' Hrest]]]. auto.
  }
  set (inds := map leader (Zrange 1 (k + 1))).
  assert (Hnd : NoDup inds).
  {
    unfold inds. apply Injective_map_NoDup_in.
    - intros x y Hxin Hyin Heq.
      apply (proj2 (In_Zrange 1 (k + 1) x)) in Hxin.
      apply (proj2 (In_Zrange 1 (k + 1) y)) in Hyin.
      destruct (Hleader x ltac:(lia)) as [Hrx Htx].
      destruct (Hleader y ltac:(lia)) as [Hry Hty].
      rewrite Heq in Htx. rewrite Htx in Hty. exact Hty.
    - apply NoDup_Zrange.
  }
  assert (Hrange : Forall (fun x => 0 <= x < Zlength p) inds).
  {
    unfold inds. rewrite Forall_forall. intros x Hx.
    apply in_map_iff in Hx as [t [Htx Ht]]. subst x.
    apply (proj2 (In_Zrange 1 (k + 1) t)) in Ht.
    apply Hleader. lia.
  }
  assert (Hincl : incl inds (Zrange 0 (Zlength p))).
  { intros x Hx. apply (proj1 (In_Zrange 0 (Zlength p) x)).
    rewrite Forall_forall in Hrange. apply Hrange. exact Hx. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hcount.
  unfold inds in Hcount. rewrite length_map in Hcount.
  apply Nat2Z.inj_le in Hcount.
  rewrite <- !Zlength_correct in Hcount.
  rewrite !Zlength_Zrange__terminal_correctness in Hcount by lia. lia.
Qed.
Lemma basketball_greedy_prefix_cutoff_spec__terminal_correctness :
  forall powers sorted D n done used,
  1 <= n -> Zlength sorted = n -> 1 <= D ->
  (forall j, 0 <= j < n -> 1 <= Znth j sorted 0) ->
  Permutation powers sorted -> mono_noninc sorted ->
  0 <= done < n -> BasketballGreedyPrefix sorted D done used ->
  used <= n -> used + TeamNeed D (Znth done sorted 0) > n ->
  Spec D powers done.
Proof.
  intros powers sorted D n done used Hn Hlen HD Hpositive Hperm Hmono
    Hdone Hprefix Hused Hcut.
  unfold BasketballGreedyPrefix in Hprefix.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists done. split; [|reflexivity]. split.
  - apply (can_win_teams_permutation__terminal_correctness sorted powers D done
      (Permutation_sym Hperm)).
    apply can_win_teams_of_greedy_prefix__terminal_correctness with (n := n);
      try assumption; lia.
  - intros other Hother.
    assert (Hother_sorted : CanWinTeams sorted D other).
    { apply (can_win_teams_permutation__terminal_correctness powers sorted D other
        Hperm Hother). }
    assert (Hother_le_n : other <= n).
    { rewrite <- Hlen. apply can_win_teams_count_le_length__terminal_correctness
        with (D := D). rewrite Hlen. lia. exact Hother_sorted. }
    destruct (Z_le_gt_dec other done) as [Hle | Hgt]; [exact Hle |].
    pose proof (greedy_prefix_lower_bound_for_any_teams__terminal_correctness
      sorted D n other Hn Hlen HD Hpositive Hmono Hother_sorted) as Hlower.
    rewrite basketball_prefix_as_sum__terminal_correctness in Hlower by lia.
    rewrite basketball_prefix_as_sum__terminal_correctness in Hprefix by lia.
    set (need := fun j : Z => TeamNeed D (Znth j sorted 0)).
    assert (Hstep :
      SumLib.Sum.sum (fun j : Z => 0 <= j < done + 1) need =
      used + need done).
    {
      pose proof (sum_Z_range_extend_right 0 done need ltac:(lia)) as Hext.
      unfold need in Hext. rewrite <- Hprefix in Hext. exact Hext.
    }
    assert (Hmonosum :
      SumLib.Sum.sum (fun j : Z => 0 <= j < done + 1) need <=
      SumLib.Sum.sum (fun j : Z => 0 <= j < other) need).
    {
      pose proof (sum_Z_range_split 0 (done + 1) other need ltac:(lia)) as Hsplit.
      assert (Hrest : 0 <=
        SumLib.Sum.sum (fun j : Z => done + 1 <= j < other) need).
      { replace 0 with ((other - (done + 1)) * 0) by lia.
        apply sum_Z_range_lower_bound; [lia |]. intros j Hj.
        unfold need. pose proof (Hpositive j ltac:(lia)) as Hp.
        pose proof (TeamNeed_positive__terminal_correctness D
          (Znth j sorted 0) ltac:(lia) ltac:(lia)) as Hneedj. lia. }
      lia.
    }
    unfold need in Hstep, Hmonosum. lia.
Qed.
Lemma basketball_greedy_prefix_complete_spec__terminal_correctness :
  forall powers sorted D n used,
  1 <= n -> Zlength sorted = n -> 1 <= D ->
  (forall j, 0 <= j < n -> 1 <= Znth j sorted 0) ->
  Permutation powers sorted -> mono_noninc sorted ->
  BasketballGreedyPrefix sorted D n used -> used <= n ->
  Spec D powers n.
Proof.
  intros powers sorted D n used Hn Hlen HD Hpositive Hperm Hmono Hprefix Hused.
  unfold BasketballGreedyPrefix in Hprefix.
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists n. split; [|reflexivity]. split.
  - apply (can_win_teams_permutation__terminal_correctness sorted powers D n
      (Permutation_sym Hperm)).
    apply can_win_teams_of_greedy_prefix__terminal_correctness with (n := n);
      try assumption; lia.
  - intros other Hother.
    assert (Hpowers_len : Zlength powers = n).
    { rewrite !Zlength_correct in Hlen |- *.
      apply Permutation_length in Hperm. lia. }
    rewrite <- Hpowers_len.
    apply can_win_teams_count_le_length__terminal_correctness with (D := D).
    + rewrite Hpowers_len. lia.
    + exact Hother.
Qed.
