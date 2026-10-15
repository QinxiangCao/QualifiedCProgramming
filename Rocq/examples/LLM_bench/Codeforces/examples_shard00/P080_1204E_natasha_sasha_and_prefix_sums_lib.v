Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition MaximalPrefixSum (a : list Z) (value : Z) : Prop :=
  max_value_of_subset Z.le
    (fun i : Z => 0 <= i < Zlength a + 1)
    (fun i => fold_right Z.add 0 (sublist 0 i a)) value.

Definition IsSign (x : Z) : Prop := -1 <= x < 2 /\ (x = -1 \/ x = 1).

#[local] Instance finite_sign : Finite IsSign :=
  Finite_subset (fun x : Z => -1 <= x < 2) (fun x => x = -1 \/ x = 1).

#[local] Instance finite_sign_array (size : Z) :
    Finite (fun a : list Z =>
      Zlength a = size /\ Forall IsSign a) :=
  Finite_bounded_lists size IsSign.

#[local] Instance finite_array_and_maximum (n m : Z) :
    Finite (fun candidate : list Z * Z =>
      (Zlength (fst candidate) = n + m /\
       Forall IsSign (fst candidate)) /\
      0 <= snd candidate < n + 1) :=
  Finite_prod
    (fun a : list Z =>
      Zlength a = n + m /\ Forall IsSign a)
    (fun maximum : Z => 0 <= maximum < n + 1).

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition IsArrayMaximumCandidate (n m : Z) (candidate : list Z * Z) : Prop :=
  Permutation (fst candidate)
    (Zmap_range (fun _ => 1) n ++ Zmap_range (fun _ => -1) m) /\
  MaximalPrefixSum (fst candidate) (snd candidate).

Definition Pre (n m : Z) : Prop := 0 <= n <= 2000 /\ 0 <= m <= 2000.

Definition Spec (n m out : Z) : Prop :=
  out = sum
    (fun candidate : list Z * Z =>
      ((Zlength (fst candidate) = n + m /\
        Forall IsSign (fst candidate)) /\
       0 <= snd candidate < n + 1) /\
      IsArrayMaximumCandidate n m candidate)
    snd mod 998244853.

Require Import Coq.Arith.Factorial.
Definition P080Factorial (n : Z) : Z := Z.of_nat (fact (Z.to_nat n)).

Definition P080Factorials (fl : list Z) (hi : Z) : Prop :=
  forall j, 0 <= j < hi -> Znth j fl 0 = P080Factorial j mod 998244853.

Definition P080InverseFactorials (il : list Z) (lo hi : Z) : Prop :=
  forall j, lo <= j < hi ->
    Znth (j - lo) il 0 = Z.pow (P080Factorial j) 998244851 mod 998244853.

Definition P080ZeroCount (n m : Z) : Z :=
  sum
    (fun candidate : list Z * Z =>
      ((Zlength (fst candidate) = n + m /\ Forall IsSign (fst candidate)) /\
       0 <= snd candidate < n + 1) /\
      IsArrayMaximumCandidate n m candidate /\ snd candidate = 0)
    (fun _ => 1) mod 998244853.

Definition P080Tables (n m x y : Z) (kl dl : list Z) : Prop :=
  forall r c, 0 <= r <= n -> 0 <= c <= m ->
    (r < x \/ r = x /\ c < y ->
       Znth (r * (m + 1) + c) kl 0 = P080ZeroCount r c /\
       Spec r c (Znth (r * (m + 1) + c) dl 0)) /\
    (x < r \/ r = x /\ y <= c ->
       Znth (r * (m + 1) + c) kl 0 = 0 /\
       Znth (r * (m + 1) + c) dl 0 = 0).

Require Import Coq.micromega.Lia.

Lemma P080Factorial_zero : P080Factorial 0 = 1.
Proof. reflexivity. Qed.

Lemma P080Factorial_succ : forall n,
  0 <= n -> P080Factorial (n + 1) = P080Factorial n * (n + 1).
Proof.
  intros n Hn. unfold P080Factorial.
  replace (n + 1) with (Z.succ n) by lia.
  rewrite Z2Nat.inj_succ by lia.
  change (Z.of_nat (S (Z.to_nat n) * fact (Z.to_nat n)) =
          Z.of_nat (fact (Z.to_nat n)) * Z.succ n).
  rewrite Nat2Z.inj_mul, Nat2Z.inj_succ, Z2Nat.id by lia.
  ring.
Qed.

Lemma P080ZeroCount_range : forall n m, 0 <= P080ZeroCount n m < 998244853.
Proof. intros. unfold P080ZeroCount. apply Z.mod_pos_bound. lia. Qed.

Lemma P080Spec_range : forall n m out,
  Spec n m out -> 0 <= out < 998244853.
Proof.
  intros n m out H. unfold Spec in H. rewrite H.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma P080Tables_exit : forall n m kl dl,
  0 <= n -> 0 <= m -> P080Tables n m (n + 1) 0 kl dl ->
  Spec n m (Znth (n * (m + 1) + m) dl 0).
Proof.
  intros n m kl dl Hn Hm H.
  specialize (H n m ltac:(lia) ltac:(lia)).
  destruct H as [H _]. specialize (H ltac:(left; lia)). tauto.
Qed.

Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.micromega.Psatz.
Lemma P080_map_constant__table_boundaries : forall (v n:Z),
 Zmap_range (fun _ => v) n = repeat v (Z.to_nat n).
Proof.
 intros v n. unfold Zmap_range, Zrange. rewrite Z.sub_0_r.
 generalize 0 as lo. induction (Z.to_nat n); intros; simpl; auto.
 f_equal. apply IHn0.
Qed.
Lemma P080_perm_repeat__table_boundaries : forall (a:list Z) v k,
 Permutation a (repeat v k) -> a = repeat v k.
Proof.
 intros a v k H.
 assert (L : length a = k) by (apply Permutation_length in H; rewrite repeat_length in H; exact H).
 assert (F : Forall (fun z => z = v) a).
 { apply Forall_forall. intros z Hz. apply (Permutation_in z H) in Hz.
   apply repeat_spec in Hz. exact Hz. }
 clear H. subst k. induction F; simpl; auto. subst x. f_equal. exact IHF.
Qed.
Lemma P080_prefix_repeat__table_boundaries : forall v k i,
 0 <= i <= Z.of_nat k ->
 fold_right Z.add 0 (sublist 0 i (repeat v k)) = v * i.
Proof.
 intros v k i H. unfold sublist. simpl.
 assert (F : forall j k, (j <= k)%nat ->
   firstn j (repeat v k) = repeat v j).
 { induction j; intros k' Hjk; simpl; auto.
   destruct k'; [lia|]. simpl. f_equal. apply IHj. lia. }
 rewrite F by lia.
 assert (S : forall j, fold_right Z.add 0 (repeat v j) = v * Z.of_nat j).
 { induction j; [simpl; ring|]. change (v + fold_right Z.add 0 (repeat v j) = v * Z.of_nat (S j)). rewrite IHj, Nat2Z.inj_succ. ring. }
 rewrite S, Z2Nat.id by lia. reflexivity.
Qed.
Lemma P080_max_repeat__table_boundaries : forall k,
 MaximalPrefixSum (repeat (-1) k) 0 /\
 MaximalPrefixSum (repeat 1 k) (Z.of_nat k).
Proof.
 intros k. unfold MaximalPrefixSum, max_value_of_subset, max_object_of_subset.
 rewrite !Zlength_correct, !repeat_length. split.
 - exists 0. split.
   + split; [change (0 <= 0 < Z.of_nat k + 1); lia|].
     intros i Hi. change (0 <= i < Z.of_nat k + 1) in Hi.
     rewrite !P080_prefix_repeat__table_boundaries by lia. lia.
   + rewrite P080_prefix_repeat__table_boundaries by lia. ring.
 - exists (Z.of_nat k). split.
   + split; [change (0 <= Z.of_nat k < Z.of_nat k + 1); lia|].
     intros i Hi. change (0 <= i < Z.of_nat k + 1) in Hi.
     rewrite !P080_prefix_repeat__table_boundaries by lia. lia.
   + rewrite P080_prefix_repeat__table_boundaries by lia. ring.
Qed.
Lemma P080_max_unique__table_boundaries : forall a u v,
 MaximalPrefixSum a u -> MaximalPrefixSum a v -> u = v.
Proof.
 intros a u v [i [[Hi Hu] Ei]] [j [[Hj Hv] Ej]].
 specialize (Hu j Hj). specialize (Hv i Hi). lia.
Qed.
Lemma P080_sign_constant_candidate__table_boundaries : forall n a v,
 0 <= n ->
 (IsArrayMaximumCandidate 0 n (a,v) <-> a = repeat (-1) (Z.to_nat n) /\ v = 0) /\
 (IsArrayMaximumCandidate n 0 (a,v) <-> a = repeat 1 (Z.to_nat n) /\ v = n).
Proof.
 intros n a v Hn. unfold IsArrayMaximumCandidate. simpl.
 rewrite !P080_map_constant__table_boundaries. simpl. rewrite app_nil_r.
 split; split.
 - intros [Hp Hm]. apply P080_perm_repeat__table_boundaries in Hp. subst a.
   split; [reflexivity|]. eapply P080_max_unique__table_boundaries; [exact Hm|].
   apply P080_max_repeat__table_boundaries.
 - intros [-> ->]. split; [apply Permutation_refl|apply P080_max_repeat__table_boundaries].
 - intros [Hp Hm]. apply P080_perm_repeat__table_boundaries in Hp. subst a.
   split; [reflexivity|]. rewrite <- (Z2Nat.id n Hn).
   eapply P080_max_unique__table_boundaries; [exact Hm|]. apply P080_max_repeat__table_boundaries.
 - intros [-> ->]. split; [apply Permutation_refl|].
   rewrite <- (Z2Nat.id n Hn) at 2. apply P080_max_repeat__table_boundaries.
Qed.
Lemma P080_sum_single__table_boundaries : forall (A:Type) (P:A->Prop) (F:Finite P) a f,
 (forall z, P z <-> z = a) -> @sum A P F f = f a.
Proof.
 intros A P F a f H. unfold sum.
 assert (E : @enum A P F = (a::nil)).
 { pose proof (@enum_nodup A P F) as D.
   assert (I : In a (@enum A P F)) by (apply enum_ok; apply H; reflexivity).
   assert (U : forall z, In z (@enum A P F) -> z = a).
   { intros z Hz. apply H. apply enum_ok. exact Hz. }
   destruct (@enum A P F) as [|b l]; [contradiction|].
   assert (B:b=a) by (apply U; simpl; auto). subst b.
   inversion D; subst. destruct l as [|c l]; [reflexivity|].
   exfalso. apply H2. assert (c=a) by (apply U; simpl; auto).
   subst c. simpl. auto. }
 rewrite E. simpl. lia.
Qed.
Lemma P080_boundary_valid__table_boundaries : forall n v,
 0 <= n -> (v = -1 \/ v = 1) ->
 Zlength (repeat v (Z.to_nat n)) = n /\ Forall IsSign (repeat v (Z.to_nat n)).
Proof.
 intros n v Hn Hv. split.
 - rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. reflexivity.
 - apply Forall_forall. intros z Hz. apply repeat_spec in Hz. subst z.
   unfold IsSign. destruct Hv; subst; lia.
Qed.
Lemma P080_spec_boundaries__table_boundaries : forall n,
 0 <= n <= 2000 ->
 Spec 0 n 0 /\ P080ZeroCount 0 n = 1 /\ Spec n 0 n /\
 (0 < n -> P080ZeroCount n 0 = 0).
Proof.
 intros n Hn.
 assert (M : forall a v, IsArrayMaximumCandidate 0 n (a,v) <-> a = repeat (-1) (Z.to_nat n) /\ v = 0).
 { intros. apply P080_sign_constant_candidate__table_boundaries. lia. }
 assert (P : forall a v, IsArrayMaximumCandidate n 0 (a,v) <-> a = repeat 1 (Z.to_nat n) /\ v = n).
 { intros. apply P080_sign_constant_candidate__table_boundaries. lia. }
 pose proof (P080_boundary_valid__table_boundaries n (-1) ltac:(lia) ltac:(auto)) as Vminus.
 pose proof (P080_boundary_valid__table_boundaries n 1 ltac:(lia) ltac:(auto)) as Vplus.
 split.
 - unfold Spec. erewrite P080_sum_single__table_boundaries with (a:=(repeat (-1) (Z.to_nat n),0)); [reflexivity|].
   intros [a v]. simpl. rewrite M. split.
   + intros [_ [-> ->]]. reflexivity.
   + intros E. inversion E; subst. simpl in *. repeat split; try tauto; try lia.
 - split.
   + unfold P080ZeroCount. erewrite P080_sum_single__table_boundaries with (a:=(repeat (-1) (Z.to_nat n),0)); [reflexivity|].
     intros [a v]. simpl. rewrite M. split.
     * intros [_ [[-> ->] _]]. reflexivity.
     * intros E. inversion E; subst. simpl in *. repeat split; try tauto; try lia.
   + split.
     * unfold Spec. erewrite P080_sum_single__table_boundaries with (a:=(repeat 1 (Z.to_nat n),n)).
       -- simpl. rewrite Z.mod_small by lia. reflexivity.
       -- intros [a v]. simpl. rewrite P. split.
          ++ intros [_ [-> ->]]. reflexivity.
          ++ intros E. inversion E; subst. simpl in *. repeat split; try tauto; try lia.
     * intros Hpos. unfold P080ZeroCount.
       erewrite sum_ext with (g:=fun _ => 0); [rewrite sum_zero; reflexivity|].
       intros [a v] [_ [C E]]. simpl in *. apply P in C. lia.
Qed.
Lemma P080_flat_index_injective__table_boundaries : forall m r c x d,
 0 <= m -> 0 <= c <= m -> 0 <= d <= m ->
 r*(m+1)+c=x*(m+1)+d -> r=x /\ c=d.
Proof.
 intros m r c x d Hm Hc Hd E.
 destruct (Z.lt_trichotomy r x) as [L|[L|L]]; nia.
Qed.
Lemma P080_flat_bounds__table_boundaries : forall n m r c : Z,
  0 <= r <= n -> 0 <= c <= m ->
  0 <= r*(m+1)+c < (n+1)*(m+1).
Proof.
  intros n m r c Hr Hc.
  assert (W : 0 <= m+1) by lia.
  pose proof (Z.mul_nonneg_nonneg r (m+1) ltac:(lia) W) as L.
  pose proof (Z.mul_le_mono_nonneg_r r n (m+1) W ltac:(lia)) as U.
  replace ((n+1)*(m+1)) with (n*(m+1)+(m+1)) by ring.
  lia.
Qed.
Lemma P080_flat_index_injective__dp_semantics : forall m r c r2 c2,
  0 <= m -> 0 <= c <= m -> 0 <= c2 <= m ->
  r * (m+1) + c = r2 * (m+1) + c2 -> r = r2 /\ c = c2.
Proof.
  intros m r c r2 c2 Hm Hc Hc2 Heq.
  assert (r = r2) by nia. split; nia.
Qed.
Lemma P080_maximum_nonnegative__dp_semantics : forall a M,
  MaximalPrefixSum a M -> 0 <= M.
Proof.
  intros a M [i [[Hi Hmax] Heq]].
  specialize (Hmax 0).
  assert (Hlen : 0 <= Zlength a) by apply Zlength_nonneg.
  specialize (Hmax ltac:(change (0 <= 0 < Zlength a + 1); lia)).
  change (0 <= fold_right Z.add 0 (sublist 0 i a)) in Hmax.
  lia.
Qed.
Lemma P080_maximum_unique__dp_semantics : forall a M M2,
  MaximalPrefixSum a M -> MaximalPrefixSum a M2 -> M = M2.
Proof.
  intros a M M2 [i [[Hi Hmax] Heq]] [j [[Hj Hmax2] Heq2]].
  specialize (Hmax j Hj). specialize (Hmax2 i Hi). lia.
Qed.
Lemma P080_prefix_cons__dp_semantics : forall h a i,
  0 < i -> fold_right Z.add 0 (sublist 0 i (h :: a)) =
  h + fold_right Z.add 0 (sublist 0 (i-1) a).
Proof.
  intros h a i Hi. unfold sublist.
  replace i with (Z.succ (i-1)) at 1 by lia.
  rewrite Z2Nat.inj_succ by lia. reflexivity.
Qed.
Lemma P080_maximum_cons__dp_semantics : forall h a M,
  MaximalPrefixSum a M ->
  MaximalPrefixSum (h :: a) (Z.max 0 (h + M)).
Proof.
  intros h a M [i [[Hi Hmax] Heq]].
  assert (HL : Zlength (h :: a) = Zlength a + 1).
  { rewrite Zlength_cons. lia. }
  unfold MaximalPrefixSum, max_value_of_subset, max_object_of_subset.
  destruct (Z_le_gt_dec 0 (h + M)) as [Hpos|Hneg].
  - exists (i+1). split.
    + split.
      * change (0 <= i < Zlength a + 1) in Hi. change (0 <= i+1 < Zlength (h::a)+1). lia.
      * intros b Hb. change (0 <= b < Zlength (h::a)+1) in Hb.
        destruct (Z.eq_dec b 0) as [->|Hbn].
        -- change (0 <= fold_right Z.add 0 (sublist 0 (i+1) (h::a))).
           rewrite P080_prefix_cons__dp_semantics by (change (0 <= i < Zlength a + 1) in Hi; lia).
           replace (i+1-1) with i by lia. lia.
        -- rewrite !P080_prefix_cons__dp_semantics by (change (0 <= i < Zlength a + 1) in Hi; lia).
           replace (i+1-1) with i by lia.
           specialize (Hmax (b-1) ltac:(change (0 <= b-1 < Zlength a+1); lia)). lia.
    + rewrite P080_prefix_cons__dp_semantics by (change (0 <= i < Zlength a + 1) in Hi; lia).
      replace (i+1-1) with i by lia. rewrite Z.max_r by lia. lia.
  - exists 0. split.
    + split.
      * change (0 <= 0 < Zlength (h::a)+1). pose proof (Zlength_nonneg a). lia.
      * intros b Hb. change (0 <= b < Zlength (h::a)+1) in Hb.
        change (fold_right Z.add 0 (sublist 0 b (h::a)) <= 0).
        destruct (Z.eq_dec b 0) as [->|Hbn]; [reflexivity|].
        rewrite P080_prefix_cons__dp_semantics by lia.
        specialize (Hmax (b-1) ltac:(change (0 <= b-1 < Zlength a+1); lia)). lia.
    + change (0 = Z.max 0 (h+M)). rewrite Z.max_l by lia. reflexivity.
Qed.
Lemma P080_map_const_range_aux__dp_semantics : forall n lo (v : Z),
  map (fun _ : Z => v) (Zrange_aux lo n) = repeat v n.
Proof. induction n; intros; simpl; auto. rewrite IHn. reflexivity. Qed.
Lemma P080_map_const_range__dp_semantics : forall n (v : Z),
  Zmap_range (fun _ => v) n = repeat v (Z.to_nat n).
Proof.
  intros. unfold Zmap_range, Zrange. rewrite Z.sub_0_r.
  apply P080_map_const_range_aux__dp_semantics.
Qed.
Lemma P080_map_const_succ__dp_semantics : forall n (v : Z),
  0 < n -> Zmap_range (fun _ => v) n = v :: Zmap_range (fun _ => v) (n-1).
Proof.
  intros n v Hn. rewrite !P080_map_const_range__dp_semantics.
  replace n with (Z.succ (n-1)) at 1 by lia.
  rewrite Z2Nat.inj_succ by lia. reflexivity.
Qed.
Lemma P080_candidate_sign_decompose__dp_semantics : forall n m h a,
  0 < n -> 0 < m ->
  (Permutation (h :: a)
     (Zmap_range (fun _ => 1) n ++ Zmap_range (fun _ => -1) m) <->
   (h = 1 /\ Permutation a
     (Zmap_range (fun _ => 1) (n-1) ++ Zmap_range (fun _ => -1) m)) \/
   (h = -1 /\ Permutation a
     (Zmap_range (fun _ => 1) n ++ Zmap_range (fun _ => -1) (m-1)))).
Proof.
  intros n m h a Hn Hm. split.
  - intro HP.
    assert (Hin : In h (Zmap_range (fun _ => 1) n ++ Zmap_range (fun _ => -1) m)).
    { eapply Permutation_in; [exact HP|]. left. reflexivity. }
    apply in_app_or in Hin. destruct Hin as [Hin|Hin];
      unfold Zmap_range in Hin; apply in_map_iff in Hin;
      destruct Hin as [k [Hk _]]; subst h.
    + left. split; [reflexivity|].
      rewrite P080_map_const_succ__dp_semantics in HP by lia.
      simpl in HP. apply Permutation_cons_inv in HP. exact HP.
    + right. split; [reflexivity|].
      rewrite (P080_map_const_succ__dp_semantics m (-1)) in HP by lia.
      apply Permutation_cons_app_inv in HP. exact HP.
  - intros [[-> HP]|[-> HP]].
    + rewrite (P080_map_const_succ__dp_semantics n 1) by lia.
      simpl. constructor. exact HP.
    + rewrite (P080_map_const_succ__dp_semantics m (-1)) by lia.
      eapply Permutation_trans; [apply perm_skip; exact HP|].
      apply Permutation_middle.
Qed.
Lemma P080_weighted_permutation__dp_semantics : forall (A:Type) (f:A->Z) l l',
  Permutation l l' ->
  fold_right (fun x s => f x + s) 0 l =
  fold_right (fun x s => f x + s) 0 l'.
Proof. intros A f l l' H. induction H; simpl; try lia. Qed.
Lemma P080_sum_reindex__dp_semantics : forall (A B:Type)
  (P:A->Prop) (Q:B->Prop) (FP:Finite P) (FQ:Finite Q) (k:A->B) (f:B->Z),
  (forall a, P a -> Q (k a)) ->
  (forall b, Q b -> exists a, P a /\ k a = b) ->
  (forall a a', P a -> P a' -> k a = k a' -> a = a') ->
  @Sum.sum B Q FQ f = @Sum.sum A P FP (fun a => f (k a)).
Proof.
  intros A B P Q FP FQ k f Hinto Honto Hinj.
  assert (Hnd : NoDup (map k (@enum A P FP))).
  { assert (Hgen : forall l, NoDup l -> (forall a, In a l -> P a) -> NoDup (map k l)).
    { intros l Hnod. induction Hnod; intros Hmem; simpl; constructor.
      - intro Hin. apply in_map_iff in Hin as [a [Heq Ha]].
        assert (x = a) by (apply Hinj; [apply Hmem; left; reflexivity|apply Hmem; right; exact Ha|symmetry; exact Heq]).
        subst. contradiction.
      - apply IHHnod. intros a Ha. apply Hmem. right. exact Ha. }
    apply Hgen; [apply enum_nodup|]. intros. apply (proj2 (enum_ok a)); assumption. }
  assert (HPerm : Permutation (@enum B Q FQ) (map k (@enum A P FP))).
  { apply NoDup_Permutation; [apply enum_nodup|exact Hnd|].
    intro b. rewrite <- enum_ok. split.
    - intro Hb. destruct (Honto b Hb) as [a [Ha Heq]].
      apply in_map_iff. exists a. split; [exact Heq|]. apply (proj1 (enum_ok a)). exact Ha.
    - intro Hb. apply in_map_iff in Hb as [a [<- Ha]]. apply Hinto.
      apply (proj2 (enum_ok a)). exact Ha. }
  unfold Sum.sum.
  rewrite (P080_weighted_permutation__dp_semantics B f _ _ HPerm).
  clear HPerm Hnd Hinto Honto Hinj. induction (@enum A P FP); simpl; congruence.
Qed.
Lemma P080_sum_partition__dp_semantics : forall (A:Type)
  (P Q R:A->Prop) (FP:Finite P) (FQ:Finite Q) (FR:Finite R) (f:A->Z),
  (forall a, P a <-> Q a \/ R a) -> (forall a, Q a -> R a -> False) ->
  @Sum.sum A P FP f = @Sum.sum A Q FQ f + @Sum.sum A R FR f.
Proof.
  intros A P Q R FP FQ FR f Hcover Hdisjoint.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ ++ @enum A R FR)).
  { apply NoDup_Permutation.
    - apply enum_nodup.
    - apply NoDup_app; try apply enum_nodup.
      intros a Ha Hb. apply (Hdisjoint a); apply (proj2 (enum_ok a)); assumption.
    - intro a. rewrite in_app_iff, <- !enum_ok. apply Hcover. }
  unfold Sum.sum.
  rewrite (P080_weighted_permutation__dp_semantics A f _ _ Hperm).
  clear Hperm Hcover Hdisjoint.
  induction (@enum A Q FQ); simpl; lia.
Qed.
Lemma P080_maximum_exists__dp_semantics : forall a, exists M, MaximalPrefixSum a M.
Proof.
  induction a as [|h a [M HM]].
  - exists 0. unfold MaximalPrefixSum, max_value_of_subset, max_object_of_subset.
    exists 0. split; [split|]; try reflexivity.
    + change (0 <= 0 < 0+1). lia.
    + intros b Hb. change (0 <= b < 0+1) in Hb.
      assert (b=0) by lia. subst. reflexivity.
  - exists (Z.max 0 (h+M)). apply P080_maximum_cons__dp_semantics. exact HM.
Qed.
Lemma P080_repeat_sum__dp_semantics : forall n v,
  fold_right Z.add 0 (repeat v n) = v * Z.of_nat n.
Proof.
  induction n; intros.
  - simpl. ring.
  - change (v + fold_right Z.add 0 (repeat v n) = v * Z.of_nat (S n)).
    rewrite IHn, Nat2Z.inj_succ. ring.
Qed.
Lemma P080_permutation_total__dp_semantics : forall n m a,
  0 <= n -> 0 <= m ->
  Permutation a (Zmap_range (fun _ => 1) n ++ Zmap_range (fun _ => -1) m) ->
  fold_right Z.add 0 a = n-m.
Proof.
  intros n m a Hn Hm HP.
  change (fold_right (fun x s => x+s) 0 a = n-m).
  rewrite (P080_weighted_permutation__dp_semantics Z (fun x=>x) _ _ HP).
  rewrite !P080_map_const_range__dp_semantics.
  change (fold_right Z.add 0 (repeat 1 (Z.to_nat n) ++ repeat (-1) (Z.to_nat m)) = n-m).
  rewrite ListLib.sum_app.
  change (fold_right Z.add 0 (repeat 1 (Z.to_nat n)) + fold_right Z.add 0 (repeat (-1) (Z.to_nat m)) = n-m).
  rewrite !P080_repeat_sum__dp_semantics, !Z2Nat.id by lia. ring.
Qed.
Lemma P080_maximum_ge_total__dp_semantics : forall a M,
  MaximalPrefixSum a M -> fold_right Z.add 0 a <= M.
Proof.
  intros a M [i [[Hi Hmax] Heq]].
  specialize (Hmax (Zlength a) ltac:(change (0 <= Zlength a < Zlength a+1); pose proof (Zlength_nonneg a); lia)).
  change (fold_right Z.add 0 (sublist 0 (Zlength a) a) <= fold_right Z.add 0 (sublist 0 i a)) in Hmax.
  rewrite Zlength_correct in Hmax. unfold sublist in Hmax.
  rewrite Nat2Z.id in Hmax. simpl in Hmax. rewrite firstn_all in Hmax.
  change (fold_right Z.add 0 a <= fold_right Z.add 0 (sublist 0 i a)) in Hmax. lia.
Qed.
Lemma P080_zero_impossible__dp_semantics : forall n m a,
  0 <= n -> 0 <= m -> m < n ->
  ~ IsArrayMaximumCandidate n m (a,0).
Proof.
  intros n m a Hn Hm Hlt [HP HM]. simpl in HP, HM.
  pose proof (P080_permutation_total__dp_semantics n m a Hn Hm HP).
  pose proof (P080_maximum_ge_total__dp_semantics a 0 HM). lia.
Qed.
Lemma P080_zero_count_impossible__dp_semantics : forall n m,
  0 <= n -> 0 <= m -> m < n -> P080ZeroCount n m = 0.
Proof.
  intros n m Hn Hm Hlt. unfold P080ZeroCount.
  erewrite sum_ext with (g:=fun _=>0).
  - rewrite sum_zero. reflexivity.
  - intros [a M] [_ [Hcandidate HM]]. simpl in HM. subst M.
    exfalso. exact (P080_zero_impossible__dp_semantics n m a Hn Hm Hlt Hcandidate).
Qed.
Lemma P080_table_step__dp_semantics : forall n m x y kl dl kv dv,
  0 <= n -> 0 <= m -> 0 <= x <= n -> 0 <= y <= m ->
  Zlength kl = (n+1)*(m+1) -> Zlength dl = (n+1)*(m+1) ->
  P080Tables n m x y kl dl -> kv = P080ZeroCount x y -> Spec x y dv ->
  P080Tables n m x (y+1)
    (replace_Znth (x*(m+1)+y) kv kl)
    (replace_Znth (x*(m+1)+y) dv dl).
Proof.
  intros n m x y kl dl kv dv Hn Hm Hx Hy Hkl Hdl HT HK HD.
  assert (Hik : 0 <= x*(m+1)+y < Zlength kl) by nia.
  assert (Hid : 0 <= x*(m+1)+y < Zlength dl) by nia.
  intros r c Hr Hc.
  assert (Hjk : 0 <= r*(m+1)+c < Zlength kl) by nia.
  assert (Hjd : 0 <= r*(m+1)+c < Zlength dl) by nia.
  destruct (Z.eq_dec (x*(m+1)+y) (r*(m+1)+c)) as [Heq|Hneq].
  - destruct (P080_flat_index_injective__dp_semantics m x y r c Hm Hy Hc Heq) as [-> ->].
    rewrite !Znth_replace_Znth_Same by assumption.
    split; [intros; split; assumption|]. intros [Hbad|[_ Hbad]]; lia.
  - rewrite !Znth_replace_Znth_Diff by assumption.
    specialize (HT r c Hr Hc). destruct HT as [Hdone Hfuture].
    split.
    + intro Hprocessed. apply Hdone.
      destruct Hprocessed as [Hlt|[He Hle]]; [left; exact Hlt|].
      right. split; [exact He|]. assert (c <> y) by (intro; subst; apply Hneq; reflexivity). lia.
    + intro Hfuture'. apply Hfuture. destruct Hfuture' as [Hlt|[He Hle]]; [left; exact Hlt|].
      right. split; [exact He|lia].
Qed.
Lemma P080_maximum_count_bound__dp_semantics : forall a M,
  Forall IsSign a -> MaximalPrefixSum a M ->
  M <= Z.of_nat (count_occ Z.eq_dec a 1).
Proof.
  intros a. induction a as [|h a IH]; intros M HF HM.
  - destruct HM as [i [_ Heq]].
    assert (Hnil : sublist 0 i (@nil Z) = nil).
    { unfold sublist. destruct (Z.to_nat i); reflexivity. }
    rewrite Hnil in Heq. simpl in *. lia.
  - inversion HF as [|? ? Hh Ha]; subst.
    destruct (P080_maximum_exists__dp_semantics a) as [T HT].
    pose proof (P080_maximum_cons__dp_semantics h a T HT) as HC.
    pose proof (P080_maximum_unique__dp_semantics (h::a) M (Z.max 0 (h+T)) HM HC) as ->.
    specialize (IH T Ha HT). destruct Hh as [_ [Hh | Hh]]; subst h.
    + change (Z.max 0 (-1+T) <= Z.of_nat (count_occ Z.eq_dec a 1)).
      apply Z.max_lub; lia.
    + change (Z.max 0 (1+T) <= Z.of_nat (S (count_occ Z.eq_dec a 1))).
      rewrite Nat2Z.inj_succ. apply Z.max_lub; lia.
Qed.
Lemma P080_permutation_shape__dp_semantics : forall n m a,
  0 <= n -> 0 <= m ->
  Permutation a (Zmap_range (fun _ => 1) n ++ Zmap_range (fun _ => -1) m) ->
  Zlength a = n+m /\ Forall IsSign a /\
  Z.of_nat (count_occ Z.eq_dec a 1) = n.
Proof.
  intros n m a Hn Hm HP.
  rewrite !P080_map_const_range__dp_semantics in HP.
  split.
  - rewrite Zlength_correct, (Permutation_length HP), length_app, !repeat_length.
    rewrite Nat2Z.inj_add, !Z2Nat.id by lia. reflexivity.
  - split.
    + apply (@Permutation_Forall Z IsSign _ _ (Permutation_sym HP)).
      apply Forall_app. split; apply Forall_forall; intros z Hz;
        apply repeat_spec in Hz; subst z; unfold IsSign; lia.
    + pose proof (proj1 (Permutation_count_occ Z.eq_dec _ _) HP 1) as HC.
      rewrite HC, count_occ_app, count_occ_repeat_eq by reflexivity.
      rewrite count_occ_repeat_neq by lia. rewrite Nat.add_0_r, Z2Nat.id by lia. reflexivity.
Qed.
Lemma P080_candidate_bound__dp_semantics : forall n m a M,
  0 <= n -> 0 <= m -> IsArrayMaximumCandidate n m (a,M) ->
  (Zlength a = n+m /\ Forall IsSign a) /\ 0 <= M < n+1.
Proof.
  intros n m a M Hn Hm [HP HM]. simpl in HP, HM.
  destruct (P080_permutation_shape__dp_semantics n m a Hn Hm HP) as [HL [HF HC]].
  pose proof (P080_maximum_nonnegative__dp_semantics a M HM).
  pose proof (P080_maximum_count_bound__dp_semantics a M HF HM).
  repeat split; try assumption; lia.
Qed.
Lemma P080_fermat_certificate__dp_semantics :
  forallb (fun j => Z.eqb (Zpow_mod (Z.of_nat j) 998244852 998244853) 1)
    (seq 1 4000) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma P080_fermat_small__dp_semantics : forall j,
  1 <= j <= 4000 -> Z.pow j 998244852 mod 998244853 = 1.
Proof. intros j Hj.
  pose proof P080_fermat_certificate__dp_semantics as HC.
  apply forallb_forall with (x:=Z.to_nat j) in HC.
  - apply Z.eqb_eq in HC.
    rewrite Z2Nat.id in HC by lia.
    rewrite Zpow_mod_correct in HC by lia. exact HC.
  - apply in_seq. lia.
Qed.
Lemma P080_factorial_fermat_nat__dp_semantics : forall k,
  (k <= 4000)%nat -> Z.pow (Z.of_nat (fact k)) 998244852 mod 998244853 = 1.
Proof.
  induction k as [|k IH]; intros Hk.
  - change (Z.pow 1 998244852 mod 998244853 = 1).
    rewrite Z.pow_1_l by lia. reflexivity.
  - assert (HB : 1 <= Z.of_nat (S k) <= 4000) by (clear IH; lia).
    specialize (IH (Nat.le_trans _ _ _ (Nat.le_succ_diag_r k) Hk)).
    change (Z.pow (Z.of_nat ((S k)*fact k)) 998244852 mod 998244853 = 1).
    rewrite Nat2Z.inj_mul, Z.pow_mul_l.
    rewrite Z.mul_mod by discriminate.
    rewrite IH.
    rewrite (P080_fermat_small__dp_semantics _ HB). reflexivity.
Qed.
Lemma P080_factorial_inverse__dp_semantics : forall j,
  0 <= j <= 4000 ->
  (P080Factorial j * Z.pow (P080Factorial j) 998244851) mod 998244853 = 1.
Proof. intros j Hj.
  replace (P080Factorial j * Z.pow (P080Factorial j) 998244851)
    with (Z.pow (P080Factorial j) 998244852).
  - unfold P080Factorial. apply P080_factorial_fermat_nat__dp_semantics. lia.
  - change (Z.pow (P080Factorial j) (Z.succ 998244851) = P080Factorial j * Z.pow (P080Factorial j) 998244851).
    rewrite Z.pow_succ_r by lia. reflexivity.
Qed.
Lemma P080_candidate_cons_plus__dp_semantics : forall n m a M,
  0 < n -> 0 < m ->
  (IsArrayMaximumCandidate n m (1::a,M) <->
   exists T, IsArrayMaximumCandidate (n-1) m (a,T) /\ M=T+1).
Proof. intros n m a M Hn Hm. split.
  - intros [HP HM]. simpl in HP, HM.
    apply P080_candidate_sign_decompose__dp_semantics in HP as [[_ HP]|[Hbad _]]; try lia.
    destruct (P080_maximum_exists__dp_semantics a) as [T HT].
    exists T. split; [split; assumption|].
    pose proof (P080_maximum_cons__dp_semantics 1 a T HT) as HC.
    pose proof (P080_maximum_unique__dp_semantics (1::a) M _ HM HC) as Heq.
    pose proof (P080_maximum_nonnegative__dp_semantics a T HT).
    rewrite Z.max_r in Heq by lia. lia.
  - intros [T [[HP HT] ->]]. simpl in HP, HT. split; simpl.
    + apply P080_candidate_sign_decompose__dp_semantics; try lia.
      left. split; [reflexivity|exact HP].
    + pose proof (P080_maximum_cons__dp_semantics 1 a T HT) as HC.
      pose proof (P080_maximum_nonnegative__dp_semantics a T HT).
      rewrite Z.max_r in HC by lia. replace (T+1) with (1+T) by lia. exact HC.
Qed.
Lemma P080_candidate_cons_minus__dp_semantics : forall n m a M,
  0 < n -> 0 < m ->
  (IsArrayMaximumCandidate n m ((-1)::a,M) <->
   exists T, IsArrayMaximumCandidate n (m-1) (a,T) /\ M=Z.max 0 (T-1)).
Proof. intros n m a M Hn Hm. split.
  - intros [HP HM]. simpl in HP, HM.
    apply P080_candidate_sign_decompose__dp_semantics in HP as [[Hbad _]|[_ HP]]; try lia.
    destruct (P080_maximum_exists__dp_semantics a) as [T HT].
    exists T. split; [split; assumption|].
    pose proof (P080_maximum_cons__dp_semantics (-1) a T HT) as HC.
    pose proof (P080_maximum_unique__dp_semantics ((-1)::a) M _ HM HC) as Heq.
    replace (T-1) with (-1+T) by lia. exact Heq.
  - intros [T [[HP HT] ->]]. simpl in HP, HT. split; simpl.
    + apply P080_candidate_sign_decompose__dp_semantics; try lia.
      right. split; [reflexivity|exact HP].
    + replace (T-1) with (-1+T) by lia.
      apply P080_maximum_cons__dp_semantics. exact HT.
Qed.
Lemma P080_weighted_candidate_recurrence__dp_semantics :
  forall (C:Z->Z->(list Z*Z)->Prop) (FC:forall i j, Finite (C i j)) n m (f:(list Z*Z)->Z),
  (forall i j p, 0 <= i -> 0 <= j -> (C i j p <-> IsArrayMaximumCandidate i j p)) ->
  0 < n -> 0 < m ->
  @Sum.sum _ (C n m) (FC n m) f =
    @Sum.sum _ (C (n-1) m) (FC (n-1) m) (fun p => f (1::fst p,snd p+1)) +
    @Sum.sum _ (C n (m-1)) (FC n (m-1)) (fun p => f ((-1)::fst p,Z.max 0 (snd p-1))).
Proof. intros C FC n m f HC Hn Hm.
  pose (QP := fun p : list Z*Z => C n m p /\ hd 0 (fst p)=1).
  pose (QM := fun p : list Z*Z => C n m p /\ hd 0 (fst p)= -1).
  pose (FQP := @Finite_subset _ (C n m) (fun p=>hd 0 (fst p)=1) (FC n m)).
  pose (FQM := @Finite_subset _ (C n m) (fun p=>hd 0 (fst p)= -1) (FC n m)).
  transitivity (@Sum.sum _ QP FQP f + @Sum.sum _ QM FQM f).
  - apply P080_sum_partition__dp_semantics.
    + intros [a M]. unfold QP, QM. simpl. split; [|tauto].
      intro Ha. pose proof (proj1 (HC n m (a,M) ltac:(lia) ltac:(lia)) Ha) as Hca.
      destruct a as [|h a].
      * destruct (P080_candidate_bound__dp_semantics n m nil M ltac:(lia) ltac:(lia) Hca) as [[HL _] _].
        change (0=n+m) in HL. lia.
      * destruct Hca as [HP _]. simpl in HP.
        apply P080_candidate_sign_decompose__dp_semantics in HP as [[He _]|[He _]]; try lia.
        -- left. split; [exact Ha|exact He].
        -- right. split; [exact Ha|exact He].
    + intros [a M] [_ Hp] [_ Hm']. unfold QP, QM in *. simpl in *. lia.
  - f_equal.
    + eapply (P080_sum_reindex__dp_semantics _ _ (C (n-1) m) QP (FC (n-1) m) FQP
         (fun p => (1::fst p,snd p+1)) f).
      * intros [a M] Ha. split; [|reflexivity].
        apply (proj2 (HC n m _ ltac:(lia) ltac:(lia))).
        apply P080_candidate_cons_plus__dp_semantics; try lia.
        exists M. split; [apply (proj1 (HC (n-1) m _ ltac:(lia) ltac:(lia))); exact Ha|reflexivity].
      * intros [a M] [Ha Hhead]. destruct a as [|h a]; [discriminate Hhead|].
        change (h=1) in Hhead. subst h.
        apply (proj1 (HC n m _ ltac:(lia) ltac:(lia))) in Ha.
        apply P080_candidate_cons_plus__dp_semantics in Ha as [T [HT Heq]]; try lia.
        exists (a,T). split.
        -- apply (proj2 (HC (n-1) m _ ltac:(lia) ltac:(lia))). exact HT.
        -- simpl. f_equal. lia.
      * intros [a M] [a' M'] Ha Ha' Heq. simpl in Heq.
        inversion Heq. subst a'. assert (M=M') by lia. subst. reflexivity.
    + eapply (P080_sum_reindex__dp_semantics _ _ (C n (m-1)) QM (FC n (m-1)) FQM
         (fun p => ((-1)::fst p,Z.max 0 (snd p-1))) f).
      * intros [a M] Ha. split; [|reflexivity].
        apply (proj2 (HC n m _ ltac:(lia) ltac:(lia))).
        apply P080_candidate_cons_minus__dp_semantics; try lia.
        exists M. split; [apply (proj1 (HC n (m-1) _ ltac:(lia) ltac:(lia))); exact Ha|reflexivity].
      * intros [a M] [Ha Hhead]. destruct a as [|h a]; [discriminate Hhead|].
        change (h= -1) in Hhead. subst h.
        apply (proj1 (HC n m _ ltac:(lia) ltac:(lia))) in Ha.
        apply P080_candidate_cons_minus__dp_semantics in Ha as [T [HT Heq]]; try lia.
        exists (a,T). split.
        -- apply (proj2 (HC n (m-1) _ ltac:(lia) ltac:(lia))). exact HT.
        -- simpl. f_equal. exact (eq_sym Heq).
      * intros [a M] [a' M'] Ha Ha' Heq. simpl in Heq.
        inversion Heq. subst a'.
        apply (proj1 (HC n (m-1) _ ltac:(lia) ltac:(lia))) in Ha.
        apply (proj1 (HC n (m-1) _ ltac:(lia) ltac:(lia))) in Ha'.
        destruct Ha as [_ HM], Ha' as [_ HM']. simpl in HM, HM'.
        pose proof (P080_maximum_unique__dp_semantics a M M' HM HM'). subst M'. reflexivity.
Qed.
Lemma P080_sum_singleton__dp_semantics : forall (A:Type) (P:A->Prop) (FP:Finite P) a (f:A->Z),
  (forall x, P x <-> x=a) -> @Sum.sum A P FP f = f a.
Proof.
  intros A P FP a f HE.
  assert (HP : Permutation (@enum A P FP) (a::nil)).
  { apply NoDup_Permutation; [apply enum_nodup|constructor; [tauto|constructor]|].
    intro x. rewrite <- enum_ok. simpl. rewrite HE. intuition congruence. }
  unfold Sum.sum. rewrite (P080_weighted_permutation__dp_semantics A f _ _ HP).
  simpl. lia.
Qed.
Lemma P080_maximum_repeat_plus__dp_semantics : forall k,
  MaximalPrefixSum (repeat 1 k) (Z.of_nat k).
Proof.
  induction k as [|k IH].
  - unfold MaximalPrefixSum, max_value_of_subset, max_object_of_subset.
    exists 0. split; [split|]; try reflexivity.
    + change (0<=0<1). lia.
    + intros b Hb. change (0<=b<1) in Hb. assert (b=0) by lia. subst. reflexivity.
  - change (MaximalPrefixSum (1::repeat 1 k) (Z.of_nat (S k))).
    rewrite Nat2Z.inj_succ.
    pose proof (P080_maximum_cons__dp_semantics 1 (repeat 1 k) (Z.of_nat k) IH) as H.
    rewrite Z.max_r in H by lia. replace (Z.succ (Z.of_nat k)) with (1+Z.of_nat k) by lia. exact H.
Qed.
Lemma P080_maximum_repeat_minus__dp_semantics : forall k,
  MaximalPrefixSum (repeat (-1) k) 0.
Proof.
  induction k as [|k IH].
  - exact (P080_maximum_repeat_plus__dp_semantics 0).
  - change (MaximalPrefixSum ((-1)::repeat (-1) k) 0).
    pose proof (P080_maximum_cons__dp_semantics (-1) (repeat (-1) k) 0 IH) as H.
    change (MaximalPrefixSum ((-1)::repeat (-1) k) 0) in H. exact H.
Qed.
Lemma P080_candidate_axis__dp_semantics : forall n m a M,
  0 <= n -> 0 <= m ->
  (n=0 -> (IsArrayMaximumCandidate n m (a,M) <-> a=repeat (-1) (Z.to_nat m) /\ M=0)) /\
  (m=0 -> (IsArrayMaximumCandidate n m (a,M) <-> a=repeat 1 (Z.to_nat n) /\ M=n)).
Proof.
  intros n m a M Hn Hm. split.
  - intros ->. split.
    + intros [HP HM]. simpl in HP, HM.
      rewrite !P080_map_const_range__dp_semantics in HP. simpl in HP.
      apply Permutation_repeat in HP. subst a. split; [reflexivity|].
      eapply P080_maximum_unique__dp_semantics; [exact HM|apply P080_maximum_repeat_minus__dp_semantics].
    + intros [-> ->]. split; simpl.
      * rewrite !P080_map_const_range__dp_semantics. reflexivity.
      * apply P080_maximum_repeat_minus__dp_semantics.
  - intros ->. split.
    + intros [HP HM]. simpl in HP, HM.
      rewrite !P080_map_const_range__dp_semantics in HP. simpl in HP. rewrite app_nil_r in HP.
      apply Permutation_repeat in HP. subst a. split; [reflexivity|].
      pose proof (P080_maximum_repeat_plus__dp_semantics (Z.to_nat n)) as H.
      rewrite Z2Nat.id in H by lia. eapply P080_maximum_unique__dp_semantics; eassumption.
    + intros [-> ->]. split; simpl.
      * rewrite !P080_map_const_range__dp_semantics. simpl. rewrite app_nil_r. reflexivity.
      * pose proof (P080_maximum_repeat_plus__dp_semantics (Z.to_nat n)) as H.
        rewrite Z2Nat.id in H by lia. exact H.
Qed.
Lemma P080_candidate_cardinal_axis__dp_semantics :
  forall (C:Z->Z->(list Z*Z)->Prop) (FC:forall i j, Finite (C i j)) n m,
  (forall i j p, 0 <= i -> 0 <= j -> (C i j p <-> IsArrayMaximumCandidate i j p)) ->
  0 <= n -> 0 <= m ->
  @Sum.sum _ (C 0 m) (FC 0 m) (fun _=>1)=1 /\
  @Sum.sum _ (C n 0) (FC n 0) (fun _=>1)=1.
Proof.
  intros C FC n m HC Hn Hm. split.
  - apply (P080_sum_singleton__dp_semantics _ (C 0 m) (FC 0 m) (repeat (-1) (Z.to_nat m),0) (fun _=>1)).
    intros [a M]. rewrite HC by lia.
    rewrite (proj1 (P080_candidate_axis__dp_semantics 0 m a M ltac:(lia) Hm) eq_refl).
    split; [intros [-> ->]; reflexivity|intro Heq; inversion Heq; auto].
  - apply (P080_sum_singleton__dp_semantics _ (C n 0) (FC n 0) (repeat 1 (Z.to_nat n),n) (fun _=>1)).
    intros [a M]. rewrite HC by lia.
    rewrite (proj2 (P080_candidate_axis__dp_semantics n 0 a M Hn ltac:(lia)) eq_refl).
    split; [intros [-> ->]; reflexivity|intro Heq; inversion Heq; auto].
Qed.
Lemma P080_candidate_cardinal_factorial_nat__dp_semantics :
  forall (C:Z->Z->(list Z*Z)->Prop) (FC:forall i j, Finite (C i j)),
  (forall i j p, 0 <= i -> 0 <= j -> (C i j p <-> IsArrayMaximumCandidate i j p)) ->
  forall k l,
  @Sum.sum _ (C (Z.of_nat k) (Z.of_nat l)) (FC (Z.of_nat k) (Z.of_nat l)) (fun _=>1) *
    Z.of_nat (fact k) * Z.of_nat (fact l) = Z.of_nat (fact (k+l)).
Proof.
  intros C FC HC k. induction k as [|k IHk]; intro l.
  - change (@Sum.sum _ (C 0 (Z.of_nat l)) (FC 0 (Z.of_nat l)) (fun _=>1) * 1 * Z.of_nat (fact l) = Z.of_nat (fact l)).
    rewrite (proj1 (P080_candidate_cardinal_axis__dp_semantics C FC 0 (Z.of_nat l) HC ltac:(lia) ltac:(lia))). ring.
  - induction l as [|l IHl].
    + rewrite Nat.add_0_r.
      change (@Sum.sum _ (C (Z.of_nat (S k)) 0) (FC (Z.of_nat (S k)) 0) (fun _=>1) * Z.of_nat (fact (S k)) * 1 = Z.of_nat (fact (S k))).
      rewrite (proj2 (P080_candidate_cardinal_axis__dp_semantics C FC (Z.of_nat (S k)) 0 HC ltac:(lia) ltac:(lia))). ring.
    + pose proof (P080_weighted_candidate_recurrence__dp_semantics C FC (Z.of_nat (S k)) (Z.of_nat (S l)) (fun _=>1) HC ltac:(lia) ltac:(lia)) as HR.
      replace (Z.of_nat (S k)-1) with (Z.of_nat k) in HR by lia.
      replace (Z.of_nat (S l)-1) with (Z.of_nat l) in HR by lia.
      rewrite HR.
      assert (HFk : Z.of_nat (fact (S k)) = Z.of_nat (S k) * Z.of_nat (fact k)) by (apply Nat2Z.inj_mul).
      assert (HFl : Z.of_nat (fact (S l)) = Z.of_nat (S l) * Z.of_nat (fact l)) by (apply Nat2Z.inj_mul).
      replace ((@Sum.sum _ (C (Z.of_nat k) (Z.of_nat (S l))) (FC (Z.of_nat k) (Z.of_nat (S l))) (fun _=>1) +
                @Sum.sum _ (C (Z.of_nat (S k)) (Z.of_nat l)) (FC (Z.of_nat (S k)) (Z.of_nat l)) (fun _=>1)) * Z.of_nat (fact (S k)) * Z.of_nat (fact (S l)))
        with ((@Sum.sum _ (C (Z.of_nat k) (Z.of_nat (S l))) (FC (Z.of_nat k) (Z.of_nat (S l))) (fun _=>1) * Z.of_nat (fact k) * Z.of_nat (fact (S l))) * Z.of_nat (S k) +
              (@Sum.sum _ (C (Z.of_nat (S k)) (Z.of_nat l)) (FC (Z.of_nat (S k)) (Z.of_nat l)) (fun _=>1) * Z.of_nat (fact (S k)) * Z.of_nat (fact l)) * Z.of_nat (S l)) by (rewrite HFk, HFl; ring).
      rewrite IHk, IHl.
      replace (k + S l)%nat with (S k+l)%nat by lia.
      replace (S k + S l)%nat with (S (S k+l))%nat by lia.
      change (Z.of_nat (fact (S k+l)) * Z.of_nat (S k) + Z.of_nat (fact (S k+l)) * Z.of_nat (S l) = Z.of_nat (fact (S (S k+l)))).
      change (Z.of_nat (fact (S k+l)) * Z.of_nat (S k) + Z.of_nat (fact (S k+l)) * Z.of_nat (S l) = Z.of_nat (S (S k+l) * fact (S k+l))).
      rewrite (Nat2Z.inj_mul (S (S k+l)) (fact (S k+l))).
      assert (HZ : Z.of_nat (S (S k+l)) = Z.of_nat (S k) + Z.of_nat (S l)) by lia.
      rewrite HZ. ring.
Qed.
Lemma P080_candidate_cardinality__dp_semantics :
  forall (C:Z->Z->(list Z*Z)->Prop) (FC:forall i j, Finite (C i j)) n m,
  (forall i j p, 0 <= i -> 0 <= j -> (C i j p <-> IsArrayMaximumCandidate i j p)) ->
  0 <= n -> 0 <= m ->
  @Sum.sum _ (C n m) (FC n m) (fun _=>1) * P080Factorial n * P080Factorial m = P080Factorial (n+m).
Proof.
  intros C FC n m HC Hn Hm.
  pose proof (P080_candidate_cardinal_factorial_nat__dp_semantics C FC HC (Z.to_nat n) (Z.to_nat m)) as H.
  rewrite !Z2Nat.id in H by lia.
  unfold P080Factorial. rewrite Z2Nat.inj_add by lia. exact H.
Qed.
Lemma P080_modular_cancel_pair__dp_semantics : forall c a b u v,
  (a*u) mod 998244853=1 -> (b*v) mod 998244853=1 ->
  (c*a*b*u*v) mod 998244853 = c mod 998244853.
Proof.
  intros c a b u v Ha Hb.
  replace (c*a*b*u*v) with (c*((a*u)*(b*v))) by ring.
  rewrite Z.mul_mod, (Z.mul_mod (a*u) (b*v)) by discriminate.
  rewrite Ha, Hb. change ((c mod 998244853)*1 mod 998244853=c mod 998244853).
  rewrite Z.mul_1_r, Z.mod_mod by discriminate. reflexivity.
Qed.
Lemma P080_modular_binomial__dp_semantics :
  forall (C:Z->Z->(list Z*Z)->Prop) (FC:forall i j, Finite (C i j)) n m,
  (forall i j p, 0 <= i -> 0 <= j -> (C i j p <-> IsArrayMaximumCandidate i j p)) ->
  0 <= n -> 0 <= m -> n+m<=4000 ->
  (P080Factorial (n+m) * Z.pow (P080Factorial n) 998244851 * Z.pow (P080Factorial m) 998244851) mod 998244853 =
  @Sum.sum _ (C n m) (FC n m) (fun _=>1) mod 998244853.
Proof.
  intros C FC n m HC Hn Hm Hnm.
  rewrite <- (P080_candidate_cardinality__dp_semantics C FC n m HC Hn Hm).
  apply P080_modular_cancel_pair__dp_semantics;
    apply P080_factorial_inverse__dp_semantics; lia.
Qed.
Lemma P080_sum_zero_indicator__dp_semantics : forall (A:Type) (P:A->Prop) (FP:Finite P) (f:A->Z),
  @Sum.sum A P FP (fun a=>if Z.eq_dec (f a) 0 then 1 else 0) =
  @Sum.sum A (fun a=>P a /\ f a=0) (@Finite_subset A P (fun a=>f a=0) FP) (fun _=>1).
Proof.
  intros A P FP f. unfold Sum.sum, Finite_subset. simpl.
  induction (@enum A P FP) as [|a l IH]; simpl; [reflexivity|].
  destruct (Sum.prop_dec (f a=0)) as [Hp|Hp]; destruct (Z.eq_dec (f a) 0) as [Hz|Hz]; try contradiction; simpl; rewrite IH; reflexivity.
Qed.
Lemma P080_sum_max_decrement__dp_semantics : forall (A:Type) (P:A->Prop) (FP:Finite P) (f:A->Z),
  (forall a, P a -> 0 <= f a) ->
  @Sum.sum A P FP (fun a=>Z.max 0 (f a-1)) =
  @Sum.sum A P FP f - @Sum.sum A P FP (fun _=>1) +
  @Sum.sum A (fun a=>P a /\ f a=0) (@Finite_subset A P (fun a=>f a=0) FP) (fun _=>1).
Proof.
  intros A P FP f Hnonneg.
  erewrite sum_ext with (g:=fun a=> f a-1+(if Z.eq_dec (f a) 0 then 1 else 0)).
  - rewrite sum_add, sum_sub, P080_sum_zero_indicator__dp_semantics. reflexivity.
  - intros a Ha. specialize (Hnonneg a Ha).
    destruct (Z.eq_dec (f a) 0) as [->|Hz].
    + reflexivity.
    + rewrite Z.max_r by lia. lia.
Qed.
Lemma P080_mod_five_terms__dp_semantics : forall a b c d e,
  ((a mod 998244853)+(b mod 998244853)+(c mod 998244853)-(d mod 998244853)+(e mod 998244853)) mod 998244853 =
  (a+b+c-d+e) mod 998244853.
Proof.
  intros a b c d e. set (p:=998244853).
  change (((a mod p)+(b mod p)+(c mod p)-(d mod p)+(e mod p)) mod p=(a+b+c-d+e) mod p).
  assert (Hp:p<>0) by (unfold p; discriminate).
  rewrite (Z.add_mod (a mod p+b mod p+c mod p-d mod p) (e mod p) p Hp).
  rewrite (Zminus_mod (a mod p+b mod p+c mod p) (d mod p) p).
  rewrite (Z.add_mod (a mod p+b mod p) (c mod p) p Hp).
  rewrite (Z.add_mod (a mod p) (b mod p) p Hp).
  rewrite (Z.add_mod (a+b+c-d) e p Hp), (Zminus_mod (a+b+c) d p).
  rewrite (Z.add_mod (a+b) c p Hp), (Z.add_mod a b p Hp).
  repeat rewrite Z.mod_mod by exact Hp. reflexivity.
Qed.
Lemma P080_sum_predicate_ext__dp_semantics : forall (A:Type) (P Q:A->Prop) (FP:Finite P) (FQ:Finite Q) (f:A->Z),
  (forall a, P a <-> Q a) -> @Sum.sum A P FP f = @Sum.sum A Q FQ f.
Proof.
  intros A P Q FP FQ f H.
  apply (P080_sum_reindex__dp_semantics A A Q P FQ FP (fun a=>a) f).
  - intros a Ha. apply (proj2 (H a)); exact Ha.
  - intros a Ha. exists a. split; [apply (proj1 (H a)); exact Ha|reflexivity].
  - intros; assumption.
Qed.
Lemma P080_spec_recurrence__dp_semantics : forall n m A B,
  0 < n -> 0 < m -> n+m<=4000 -> Spec (n-1) m A -> Spec n (m-1) B ->
  Spec n m
    (((P080Factorial (n-1+m) * Z.pow (P080Factorial (n-1)) 998244851 * Z.pow (P080Factorial m) 998244851) mod 998244853 + A + B -
      (P080Factorial (n+(m-1)) * Z.pow (P080Factorial n) 998244851 * Z.pow (P080Factorial (m-1)) 998244851) mod 998244853 + P080ZeroCount n (m-1)) mod 998244853).
Proof.
  intros n m A B Hn Hm Hnm HA HB.
  pose (C := fun i j (p:list Z*Z) =>
    ((Zlength (fst p)=i+j /\ Forall IsSign (fst p)) /\ 0<=snd p<i+1) /\ IsArrayMaximumCandidate i j p).
  pose (FC := fun i j => @Finite_subset (list Z*Z)
    (fun p => (Zlength (fst p)=i+j /\ Forall IsSign (fst p)) /\ 0<=snd p<i+1)
    (IsArrayMaximumCandidate i j) (finite_array_and_maximum i j)).
  assert (HC : forall i j p, 0<=i -> 0<=j -> (C i j p <-> IsArrayMaximumCandidate i j p)).
  { intros i j [a M] Hi Hj. unfold C. split; [tauto|].
    intro H. split; [apply P080_candidate_bound__dp_semantics; assumption|exact H]. }
  change (A=@Sum.sum _ (C (n-1) m) (FC (n-1) m) snd mod 998244853) in HA.
  change (B=@Sum.sum _ (C n (m-1)) (FC n (m-1)) snd mod 998244853) in HB.
  assert (HZ : P080ZeroCount n (m-1) =
    @Sum.sum _ (fun p=> C n (m-1) p /\ snd p=0)
      (@Finite_subset _ (C n (m-1)) (fun p=>snd p=0) (FC n (m-1))) (fun _=>1) mod 998244853).
  { unfold P080ZeroCount. f_equal. apply P080_sum_predicate_ext__dp_semantics.
    intros p. unfold C. tauto. }
  pose proof (P080_weighted_candidate_recurrence__dp_semantics C FC n m snd HC Hn Hm) as HR.
  cbn [fst snd] in HR.
  rewrite sum_add in HR.
  rewrite P080_sum_max_decrement__dp_semantics in HR.
  2: { intros [a M] H. apply (proj1 (HC n (m-1) (a,M) ltac:(lia) ltac:(lia))) in H.
       apply P080_maximum_nonnegative__dp_semantics with (a:=a). exact (proj2 H). }
  unfold Spec. fold C FC.
  rewrite HA, HB, HZ.
  rewrite (P080_modular_binomial__dp_semantics C FC (n-1) m HC ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (P080_modular_binomial__dp_semantics C FC n (m-1) HC ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite P080_mod_five_terms__dp_semantics.
  transitivity (@Sum.sum _ (C n m) (FC n m) snd mod 998244853).
  - rewrite HR. f_equal. ring.
  - reflexivity.
Qed.
Lemma P080_maximum_zero_prefixes__dp_semantics : forall a,
  MaximalPrefixSum a 0 <-> forall i, 0<=i<=Zlength a -> fold_right Z.add 0 (sublist 0 i a)<=0.
Proof.
  intro a. split.
  - intros [j [[Hj Hmax] Heq]] i Hi.
    specialize (Hmax i ltac:(change (0<=i<Zlength a+1); lia)). lia.
  - intros H. unfold MaximalPrefixSum, max_value_of_subset, max_object_of_subset.
    exists 0. split; [split|reflexivity].
    + change (0<=0<Zlength a+1). pose proof (Zlength_nonneg a). lia.
    + intros i Hi. change (0<=i<Zlength a+1) in Hi.
      change (fold_right Z.add 0 (sublist 0 i a)<=0). apply H. lia.
Qed.
Lemma P080_maximum_zero_snoc__dp_semantics : forall a h,
  MaximalPrefixSum (a++h::nil) 0 <->
  MaximalPrefixSum a 0 /\ fold_right Z.add 0 a+h<=0.
Proof.
  intros a h. rewrite !P080_maximum_zero_prefixes__dp_semantics.
  assert (HL : Zlength (a++h::nil)=Zlength a+1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (HS : fold_right Z.add 0 (a++h::nil)=fold_right Z.add 0 a+h).
  { change (ListLib.sum (a++h::nil)=ListLib.sum a+h). rewrite ListLib.sum_app. change (ListLib.sum a+(h+0)=ListLib.sum a+h). lia. }
  split.
  - intros H. split.
    + intros i Hi.
      specialize (H i ltac:(lia)). rewrite sublist_split_app_l in H by lia. exact H.
    + specialize (H (Zlength (a++h::nil)) ltac:(pose proof (Zlength_nonneg a); lia)).
      rewrite sublist_self in H by reflexivity. rewrite HS in H. exact H.
  - intros [H Htotal] i Hi. destruct (Z_le_gt_dec i (Zlength a)).
    + rewrite sublist_split_app_l by lia. apply H. lia.
    + assert (Heq:i=Zlength (a++h::nil)) by lia. rewrite Heq, sublist_self, HS by reflexivity. exact Htotal.
Qed.
Lemma P080_zero_candidate_snoc_plus__dp_semantics : forall n m a,
  0<n -> 0<m -> n<=m ->
  (IsArrayMaximumCandidate n m (a++1::nil,0) <-> IsArrayMaximumCandidate (n-1) m (a,0)).
Proof.
  intros n m a Hn Hm Hnm. split.
  - intros [HP HM]. simpl in HP, HM.
    assert (Hcons:Permutation (1::a) (Zmap_range (fun _=>1) n ++ Zmap_range (fun _=> -1) m)).
    { eapply Permutation_trans; [apply Permutation_cons_append|exact HP]. }
    apply P080_candidate_sign_decompose__dp_semantics in Hcons as [[_ Htail]|[Hbad _]]; try lia.
    apply P080_maximum_zero_snoc__dp_semantics in HM. split; [exact Htail|exact (proj1 HM)].
  - intros [HP HM]. simpl in HP, HM. split; simpl.
    + eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|].
      apply P080_candidate_sign_decompose__dp_semantics; try lia. left. split; [reflexivity|exact HP].
    + apply P080_maximum_zero_snoc__dp_semantics. split; [exact HM|].
      rewrite (P080_permutation_total__dp_semantics (n-1) m a ltac:(lia) ltac:(lia) HP). lia.
Qed.
Lemma P080_zero_candidate_snoc_minus__dp_semantics : forall n m a,
  0<n -> 0<m -> n<=m ->
  (IsArrayMaximumCandidate n m (a++(-1)::nil,0) <-> IsArrayMaximumCandidate n (m-1) (a,0)).
Proof.
  intros n m a Hn Hm Hnm. split.
  - intros [HP HM]. simpl in HP, HM.
    assert (Hcons:Permutation ((-1)::a) (Zmap_range (fun _=>1) n ++ Zmap_range (fun _=> -1) m)).
    { eapply Permutation_trans; [apply Permutation_cons_append|exact HP]. }
    apply P080_candidate_sign_decompose__dp_semantics in Hcons as [[Hbad _]|[_ Htail]]; try lia.
    apply P080_maximum_zero_snoc__dp_semantics in HM. split; [exact Htail|exact (proj1 HM)].
  - intros [HP HM]. simpl in HP, HM. split; simpl.
    + eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|].
      apply P080_candidate_sign_decompose__dp_semantics; try lia. right. split; [reflexivity|exact HP].
    + apply P080_maximum_zero_snoc__dp_semantics. split; [exact HM|].
      rewrite (P080_permutation_total__dp_semantics n (m-1) a ltac:(lia) ltac:(lia) HP). lia.
Qed.
Lemma P080_list_last_decompose__dp_semantics : forall (a:list Z),
  a=nil \/ exists b h, a=b++h::nil.
Proof.
  induction a as [|h a IH]; [left; reflexivity|]. right.
  destruct IH as [->|[b [z ->]]].
  - exists nil, h. reflexivity.
  - exists (h::b), z. reflexivity.
Qed.
Lemma P080_raw_zero_recurrence__dp_semantics :
  forall (C:Z->Z->(list Z*Z)->Prop) (FC:forall i j, Finite (C i j)) n m,
  (forall i j p, 0 <= i -> 0 <= j -> (C i j p <-> IsArrayMaximumCandidate i j p /\ snd p=0)) ->
  0<n -> 0<m -> n<=m ->
  @Sum.sum _ (C n m) (FC n m) (fun _=>1) =
  @Sum.sum _ (C (n-1) m) (FC (n-1) m) (fun _=>1) + @Sum.sum _ (C n (m-1)) (FC n (m-1)) (fun _=>1).
Proof.
  intros C FC n m HC Hn Hm Hnm.
  pose (QP := fun p:list Z*Z=> C n m p /\ last (fst p) 0=1).
  pose (QM := fun p:list Z*Z=> C n m p /\ last (fst p) 0= -1).
  pose (FQP := @Finite_subset _ (C n m) (fun p=>last (fst p) 0=1) (FC n m)).
  pose (FQM := @Finite_subset _ (C n m) (fun p=>last (fst p) 0= -1) (FC n m)).
  transitivity (@Sum.sum _ QP FQP (fun _=>1)+@Sum.sum _ QM FQM (fun _=>1)).
  - apply P080_sum_partition__dp_semantics.
    + intros [a M]. unfold QP, QM. simpl. split; [|tauto]. intro Ha.
      pose proof (proj1 (HC n m (a,M) ltac:(lia) ltac:(lia)) Ha) as [Hca HM].
      destruct (P080_list_last_decompose__dp_semantics a) as [->|[b [h ->]]].
      * destruct (P080_candidate_bound__dp_semantics n m nil M ltac:(lia) ltac:(lia) Hca) as [[HL _] _].
        change (0=n+m) in HL. lia.
      * rewrite last_last.
        destruct Hca as [HP _]. simpl in HP.
        assert (Hcons:Permutation (h::b) (Zmap_range (fun _=>1) n ++ Zmap_range (fun _=> -1) m)).
        { eapply Permutation_trans; [apply Permutation_cons_append|exact HP]. }
        apply P080_candidate_sign_decompose__dp_semantics in Hcons as [[He _]|[He _]]; try lia.
        -- left. split; [exact Ha|exact He].
        -- right. split; [exact Ha|exact He].
    + intros [a M] [_ Hp] [_ Hm']. unfold QP, QM in *. simpl in *. lia.
  - f_equal.
    + eapply (P080_sum_reindex__dp_semantics _ _ (C (n-1) m) QP (FC (n-1) m) FQP (fun p=>(fst p++1::nil,0)) (fun _=>1)).
      * intros [a M] Ha. split; [|simpl; apply last_last].
        apply (proj2 (HC n m _ ltac:(lia) ltac:(lia))). split; [|reflexivity].
        apply P080_zero_candidate_snoc_plus__dp_semantics; try lia.
        apply (proj1 (HC (n-1) m _ ltac:(lia) ltac:(lia))) in Ha as [Ha HM]. simpl in HM. subst M. exact Ha.
      * intros [a M] [Ha Hlast].
        pose proof (proj1 (HC n m _ ltac:(lia) ltac:(lia)) Ha) as [Hca HM]. simpl in HM. subst M.
        destruct (P080_list_last_decompose__dp_semantics a) as [->|[b [h ->]]]; [discriminate Hlast|].
        simpl in Hlast. rewrite last_last in Hlast. subst h.
        exists (b,0). split.
        -- apply (proj2 (HC (n-1) m _ ltac:(lia) ltac:(lia))). split; [|reflexivity].
           apply P080_zero_candidate_snoc_plus__dp_semantics with (n:=n) (m:=m); assumption.
        -- reflexivity.
      * intros [a M] [a' M'] Ha Ha' Heq. simpl in Heq.
        apply (proj1 (HC (n-1) m _ ltac:(lia) ltac:(lia))) in Ha as [_ HM].
        apply (proj1 (HC (n-1) m _ ltac:(lia) ltac:(lia))) in Ha' as [_ HM'].
        simpl in HM, HM'. subst M M'. injection Heq as Hlist.
        apply app_inv_tail in Hlist. subst a'. reflexivity.
    + eapply (P080_sum_reindex__dp_semantics _ _ (C n (m-1)) QM (FC n (m-1)) FQM (fun p=>(fst p++(-1)::nil,0)) (fun _=>1)).
      * intros [a M] Ha. split; [|simpl; apply last_last].
        apply (proj2 (HC n m _ ltac:(lia) ltac:(lia))). split; [|reflexivity].
        apply P080_zero_candidate_snoc_minus__dp_semantics; try lia.
        apply (proj1 (HC n (m-1) _ ltac:(lia) ltac:(lia))) in Ha as [Ha HM]. simpl in HM. subst M. exact Ha.
      * intros [a M] [Ha Hlast].
        pose proof (proj1 (HC n m _ ltac:(lia) ltac:(lia)) Ha) as [Hca HM]. simpl in HM. subst M.
        destruct (P080_list_last_decompose__dp_semantics a) as [->|[b [h ->]]]; [discriminate Hlast|].
        simpl in Hlast. rewrite last_last in Hlast. subst h.
        exists (b,0). split.
        -- apply (proj2 (HC n (m-1) _ ltac:(lia) ltac:(lia))). split; [|reflexivity].
           apply P080_zero_candidate_snoc_minus__dp_semantics with (n:=n) (m:=m); assumption.
        -- reflexivity.
      * intros [a M] [a' M'] Ha Ha' Heq. simpl in Heq.
        apply (proj1 (HC n (m-1) _ ltac:(lia) ltac:(lia))) in Ha as [_ HM].
        apply (proj1 (HC n (m-1) _ ltac:(lia) ltac:(lia))) in Ha' as [_ HM'].
        simpl in HM, HM'. subst M M'. injection Heq as Hlist.
        apply app_inv_tail in Hlist. subst a'. reflexivity.
Qed.
Lemma P080_zero_count_recurrence__dp_semantics : forall n m,
  0<n -> 0<m -> n<=m ->
  P080ZeroCount n m = (P080ZeroCount (n-1) m + P080ZeroCount n (m-1)) mod 998244853.
Proof.
  intros n m Hn Hm Hnm.
  pose (C := fun i j (p:list Z*Z) =>
    ((Zlength (fst p)=i+j /\ Forall IsSign (fst p)) /\ 0<=snd p<i+1) /\ IsArrayMaximumCandidate i j p /\ snd p=0).
  pose (FC := fun i j => @Finite_subset (list Z*Z)
    (fun p => (Zlength (fst p)=i+j /\ Forall IsSign (fst p)) /\ 0<=snd p<i+1)
    (fun p=>IsArrayMaximumCandidate i j p /\ snd p=0) (finite_array_and_maximum i j)).
  assert (HC : forall i j p, 0<=i -> 0<=j -> (C i j p <-> IsArrayMaximumCandidate i j p /\ snd p=0)).
  { intros i j [a M] Hi Hj. unfold C. split; [tauto|].
    intros [H HM]. split; [apply P080_candidate_bound__dp_semantics; assumption|tauto]. }
  pose proof (P080_raw_zero_recurrence__dp_semantics C FC n m HC Hn Hm Hnm) as HR.
  change (@Sum.sum _ (C n m) (FC n m) (fun _=>1) mod 998244853 =
    (@Sum.sum _ (C (n-1) m) (FC (n-1) m) (fun _=>1) mod 998244853 +
     @Sum.sum _ (C n (m-1)) (FC n (m-1)) (fun _=>1) mod 998244853) mod 998244853).
  rewrite <- Z.add_mod by discriminate. rewrite HR. reflexivity.
Qed.
Lemma P080_rem_normalize__dp_semantics : forall v,
  Z.rem (Z.rem v 998244853 + 998244853) 998244853 = v mod 998244853.
Proof.
  intro v.
  pose proof (Z.rem_bound_abs v 998244853 ltac:(discriminate)) as HB.
  change (Z.abs (Z.rem v 998244853) < 998244853) in HB.
  apply Z.abs_lt in HB.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by discriminate.
  pose proof (Z.quot_rem v 998244853 ltac:(discriminate)) as HE.
  rewrite HE at 2.
  rewrite Z.add_mod, Z.mul_mod, Z.mod_same by discriminate.
  rewrite Z.mul_0_l, Z.mod_0_l, Z.add_0_l, Z.mod_mod by discriminate. reflexivity.
Qed.
Lemma P080_rem_product__dp_semantics : forall a b c,
  0<=a -> 0<=b -> 0<=c ->
  Z.rem (Z.rem (a*b) 998244853 * c) 998244853 = (a*b*c) mod 998244853.
Proof.
  intros a b c Ha Hb Hc.
  rewrite (Z.rem_mod_nonneg (a*b) 998244853) by nia.
  pose proof (Z.mod_pos_bound (a*b) 998244853 ltac:(lia)).
  rewrite Z.rem_mod_nonneg by nia.
  rewrite Z.mul_mod_idemp_l by discriminate. reflexivity.
Qed.
Lemma P080_mod_product_three__dp_semantics : forall a b c,
  ((a mod 998244853)*(b mod 998244853)*(c mod 998244853)) mod 998244853 = (a*b*c) mod 998244853.
Proof. intros a b c.
  rewrite (Z.mul_mod ((a mod 998244853)*(b mod 998244853)) (c mod 998244853) 998244853) by discriminate.
  rewrite <- (Z.mul_mod a b 998244853) by discriminate.
  rewrite Z.mod_mod by discriminate.
  rewrite <- Z.mul_mod by discriminate. reflexivity.
Qed.
Lemma P080_mul_swap_tail__dp_semantics : forall a b c:Z, a*b*c=a*c*b.
Proof. intros. ring. Qed.
Lemma P080_cell_value__dp_semantics : forall N n m fl il A B K,
  0<n -> 0<m -> n+m<=N -> N<=4000 ->
  P080Factorials fl (N+1) -> P080InverseFactorials il 0 (N+1) ->
  Spec (n-1) m A -> Spec n (m-1) B -> K=P080ZeroCount n (m-1) ->
  Spec n m
    (Z.rem (Z.rem
       (Z.rem (Z.rem (Znth (n+m-1) fl 0 * Znth m il 0) 998244853 * Znth (n-1) il 0) 998244853 + A+B -
        Z.rem (Z.rem (Znth (n+m-1) fl 0 * Znth n il 0) 998244853 * Znth (m-1) il 0) 998244853 + K)
       998244853 + 998244853) 998244853).
Proof. intros N n m fl il A B K Hn Hm HN HNmax HF HI HA HB HK.
  assert (Ht:0<=n+m-1<N+1) by lia.
  assert (Hni:0<=n<N+1) by lia.
  assert (Hmi:0<=m<N+1) by lia.
  assert (Hn1:0<=n-1<N+1) by lia.
  assert (Hm1:0<=m-1<N+1) by lia.
  assert (Hnm:n+m<=4000) by lia.
  assert (Et1:n-1+m=n+m-1) by lia.
  assert (Et2:n+(m-1)=n+m-1) by lia.
  assert (Hp:0<998244853) by lia.
  assert (HFn:forall j, 0<=j<N+1 -> 0<=Znth j fl 0).
  { intros j Hj. rewrite (HF j Hj). exact (proj1 (Z.mod_pos_bound _ _ Hp)). }
  assert (HIn:forall j, 0<=j<N+1 -> 0<=Znth j il 0).
  { intros j Hj. specialize (HI j Hj). rewrite Z.sub_0_r in HI.
    rewrite HI. exact (proj1 (Z.mod_pos_bound _ _ Hp)). }
  rewrite P080_rem_normalize__dp_semantics.
  rewrite !P080_rem_product__dp_semantics by (first [apply HFn|apply HIn]; assumption).
  rewrite (HF _ Ht).
  pose proof (HI _ Hni) as Eni. rewrite Z.sub_0_r in Eni.
  pose proof (HI _ Hmi) as Emi. rewrite Z.sub_0_r in Emi.
  pose proof (HI _ Hn1) as En1. rewrite Z.sub_0_r in En1.
  pose proof (HI _ Hm1) as Em1. rewrite Z.sub_0_r in Em1.
  rewrite Eni, Emi, En1, Em1.
  rewrite !P080_mod_product_three__dp_semantics.
  rewrite (P080_mul_swap_tail__dp_semantics (P080Factorial (n+m-1)) (Z.pow (P080Factorial m) 998244851) (Z.pow (P080Factorial (n-1)) 998244851)).
  rewrite HK.
  pose proof (P080_spec_recurrence__dp_semantics n m A B Hn Hm Hnm HA HB) as HS.
  rewrite Et1, Et2 in HS.
  exact HS.
Qed.
Lemma P080_table_step_D__dp_semantics : forall n m x y kl dl dv,
  0<=n -> 0<=m -> 0<=x<=n -> 0<=y<=m ->
  Zlength kl=(n+1)*(m+1) -> Zlength dl=(n+1)*(m+1) ->
  P080Tables n m x y kl dl -> Znth (x*(m+1)+y) kl 0=P080ZeroCount x y -> Spec x y dv ->
  P080Tables n m x (y+1) kl (replace_Znth (x*(m+1)+y) dv dl).
Proof. intros n m x y kl dl dv Hn Hm Hx Hy Hkl Hdl HT HK HD.
  pose proof (P080_table_step__dp_semantics n m x y kl dl (Znth (x*(m+1)+y) kl 0) dv Hn Hm Hx Hy Hkl Hdl HT HK HD) as H.
  rewrite replace_Znth_Znth in H by nia. exact H.
Qed.
Lemma P080_small_fermat__inverse_factorials : forall i,
  1 <= i <= 4000 -> i ^ 998244852 mod 998244853 = 1.
Proof.
  assert (Hcheck : forallb (fun k => Z.eqb (Zpow_mod (Z.of_nat k) 998244852 998244853) 1) (seq 1 4000) = true).
  { vm_compute. reflexivity. }
  intros i Hi.
  rewrite forallb_forall in Hcheck.
  specialize (Hcheck (Z.to_nat i)).
  assert (Hin : In (Z.to_nat i) (seq 1 4000)).
  { apply in_seq. lia. }
  specialize (Hcheck Hin). apply Z.eqb_eq in Hcheck.
  rewrite Z2Nat.id in Hcheck by lia.
  rewrite Zpow_mod_correct in Hcheck by lia. exact Hcheck.
Qed.
Lemma P080_pow_mod_congruence__inverse_factorials : forall a e p,
  0 <= e -> p <> 0 -> (a mod p)^e mod p = a^e mod p.
Proof.
  intros a e p He Hp.
  replace e with (Z.of_nat (Z.to_nat e)) by (rewrite Z2Nat.id; lia).
  induction (Z.to_nat e) as [|k IH].
  - reflexivity.
  - rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia.
    rewrite (Z.mul_mod (a mod p)), (Z.mul_mod a) by lia.
    rewrite Z.mod_mod by lia. rewrite IH. reflexivity.
Qed.
Lemma P080_inverse_down__inverse_factorials : forall i,
  1 <= i <= 4000 ->
  ((P080Factorial i)^998244851 mod 998244853*i) mod 998244853 =
  (P080Factorial (i-1))^998244851 mod 998244853.
Proof.
  intros i Hi.
  replace i with ((i-1)+1) at 1 by lia.
  rewrite P080Factorial_succ by lia.
  replace (i-1+1) with i by lia.
  rewrite Z.pow_mul_l.
  rewrite Z.mul_mod_idemp_l by lia.
  replace (P080Factorial (i-1)^998244851 * i^998244851 * i)
    with (P080Factorial (i-1)^998244851 * i^998244852).
  2: { pose proof (Z.pow_succ_r i 998244851 ltac:(lia)) as Hpow. change (i^998244852 = i*i^998244851) in Hpow. rewrite Hpow. rewrite (Z.mul_comm i (i^998244851)). rewrite Z.mul_assoc. reflexivity. }
  rewrite Z.mul_mod by lia.
  rewrite P080_small_fermat__inverse_factorials by lia.
  rewrite Z.mul_1_r, Z.mod_mod by lia. reflexivity.
Qed.
Lemma P080_factorial_rem__inverse_factorials : forall j,
  Z.rem (P080Factorial j) 998244853 = P080Factorial j mod 998244853.
Proof. intros. apply Z.rem_mod_nonneg; [unfold P080Factorial; apply Nat2Z.is_nonneg | lia]. Qed.
Lemma P080_pow_rem__inverse_factorials : forall a e,
  0 <= a -> Z.rem (a^e) 998244853 = a^e mod 998244853.
Proof. intros. apply Z.rem_mod_nonneg; [apply Z.pow_nonneg; assumption | lia]. Qed.
Lemma P080_parity_shift__modpow e :
  Z.shiftr e 1 = e / 2 /\ Z.land e 1 = e mod 2.
Proof.
  split.
  - rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - change (Z.land e (Z.ones 1) = e mod (2 ^ 1)).
    apply Z.land_ones; lia.
Qed.
Lemma P080_pow_mod__modpow a e p : 0 <= e -> p <> 0 ->
  Z.rem ((Z.rem a p) ^ e) p = Z.rem (a ^ e) p.
Proof.
  intros He Hp. rewrite <- (Z2Nat.id e He).
  induction (Z.to_nat e) as [|n IH].
  - change (Z.rem 1 p = Z.rem 1 p). reflexivity.
  - rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia.
    rewrite (Z.mul_rem (Z.rem a p) ((Z.rem a p) ^ (Z.of_nat n)) p) by assumption.
    rewrite Z.rem_rem by assumption. rewrite IH.
    symmetry. apply Z.mul_rem. assumption.
Qed.
Lemma P080_pow_square_mod__modpow a h p : 0 <= h -> p <> 0 ->
  Z.rem ((Z.rem (a * a) p) ^ h) p = Z.rem (a ^ (2*h)) p.
Proof.
  intros Hh Hp. rewrite P080_pow_mod__modpow by assumption.
  rewrite Z.pow_mul_r by lia. rewrite Z.pow_2_r. reflexivity.
Qed.
Lemma P080_even_step__modpow r a e p : 0 <= e -> p <> 0 -> Z.land e 1 = 0 ->
  Z.rem (r * (Z.rem (a*a) p) ^ (Z.shiftr e 1)) p = Z.rem (r * a ^ e) p.
Proof.
  intros He Hp Hb.
  destruct (P080_parity_shift__modpow e) as [Hs Hl]. rewrite Hs.
  assert (Hh: 0 <= e/2) by (apply Z.div_pos; lia).
  assert (Heq: e = 2*(e/2)) by (rewrite Hl in Hb; pose proof (Z.div_mod e 2 ltac:(lia)); lia).
  rewrite (Z.mul_rem r ((Z.rem (a*a) p) ^ (e/2)) p) by assumption.
  rewrite P080_pow_square_mod__modpow by assumption.
  rewrite <- Heq. symmetry. apply Z.mul_rem; assumption.
Qed.
Lemma P080_odd_step__modpow r a e p : 0 <= e -> p <> 0 -> Z.land e 1 <> 0 ->
  Z.rem (Z.rem (r*a) p * (Z.rem (a*a) p) ^ (Z.shiftr e 1)) p = Z.rem (r * a ^ e) p.
Proof.
  intros He Hp Hb.
  destruct (P080_parity_shift__modpow e) as [Hs Hl]. rewrite Hs.
  assert (Hh: 0 <= e/2) by (apply Z.div_pos; lia).
  assert (Heq: e = 2*(e/2)+1) by (rewrite Hl in Hb; pose proof (Z.div_mod e 2 ltac:(lia)); pose proof (Z.mod_pos_bound e 2 ltac:(lia)); lia).
  rewrite (Z.mul_rem (Z.rem (r*a) p) ((Z.rem (a*a) p) ^ (e/2)) p) by assumption.
  rewrite Z.rem_rem by assumption.
  rewrite P080_pow_square_mod__modpow by assumption.
  rewrite <- Z.mul_rem by assumption.
  rewrite Heq at 2. rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
  f_equal. ring.
Qed.
