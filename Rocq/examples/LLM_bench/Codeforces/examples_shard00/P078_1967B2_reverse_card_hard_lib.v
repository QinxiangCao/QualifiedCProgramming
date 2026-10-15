Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

#[local] Instance finite_bounded_pair (n m : Z) :
    Finite (fun p : Z * Z => 1 <= fst p < n + 1 /\ 1 <= snd p < m + 1) :=
  Finite_prod (fun i : Z => 1 <= i < n + 1) (fun j : Z => 1 <= j < m + 1).

Definition Pre (n m : Z) : Prop := 1 <= n <= 2000000 /\ 1 <= m <= 2000000.

Definition Spec (n m out : Z) : Prop :=
  out = #(fun p : Z * Z =>
    (1 <= fst p < n + 1 /\ 1 <= snd p < m + 1) /\
    (fst p + snd p | snd p * Z.gcd (fst p) (snd p))).

(* The processed region is a subset of the original mathematical solution set,
   ordered by the primitive ratio of each pair. *)
Definition RCgcd : Z -> Z -> Z := Z.gcd.

Definition RCBefore (p q : Z) (ab : Z * Z) : Prop :=
  let g := Z.gcd (fst ab) (snd ab) in
  fst ab / g < p \/ (fst ab / g = p /\ snd ab / g < q).

Definition RCProgress (n m p q ans : Z) : Prop :=
  ans = #(fun ab : Z * Z =>
    ((1 <= fst ab < n + 1 /\ 1 <= snd ab < m + 1) /\
     (fst ab + snd ab | snd ab * Z.gcd (fst ab) (snd ab))) /\
    RCBefore p q ab).

Require Import Coq.micromega.Lia.

Lemma RCgcd_step a b : b <> 0 -> RCgcd b (a mod b) = RCgcd a b.
Proof. intros Hb. unfold RCgcd. rewrite Z.gcd_comm, Z.gcd_mod, Z.gcd_comm; auto. Qed.

Lemma RCgcd_finish a : 0 <= a -> RCgcd a 0 = a.
Proof. intros Ha. unfold RCgcd. rewrite Z.gcd_0_r, Z.abs_eq; lia. Qed.

(* A primitive ray has exactly one original pair for each positive multiplier.
   These algebraic lemmas expose the bridge without changing Spec. *)
Lemma RC_ray_gcd p q t :
  0 <= t * (p + q) -> Z.gcd p q = 1 ->
  Z.gcd (t * p * (p + q)) (t * q * (p + q)) = t * (p + q).
Proof.
  intros Hpos Hcop.
  replace (t * p * (p + q)) with ((t * (p + q)) * p) by ring.
  replace (t * q * (p + q)) with ((t * (p + q)) * q) by ring.
  rewrite Z.gcd_mul_mono_l, Hcop, Z.mul_1_r, Z.abs_eq; auto.
Qed.

Lemma RC_ray_valid p q t :
  1 <= p -> 1 <= q -> 1 <= t -> Z.gcd p q = 1 ->
  (t * p * (p + q) + t * q * (p + q) |
   (t * q * (p + q)) *
   Z.gcd (t * p * (p + q)) (t * q * (p + q))).
Proof.
  intros Hp Hq Ht Hg.
  rewrite RC_ray_gcd by (try nia; assumption).
  exists (t * q). ring.
Qed.

Lemma RC_ray_square_bounds n m p q t :
  1 <= p -> 1 <= q -> 1 <= t ->
  t * p * (p + q) <= n -> t * q * (p + q) <= m ->
  p * p < n /\ q * q < m.
Proof. intros. split; nia. Qed.

Lemma RC_primitive_decomposition a b :
  1 <= a -> 1 <= b ->
  let g := Z.gcd a b in
  1 <= g /\ 1 <= a / g /\ 1 <= b / g /\
  a = g * (a / g) /\ b = g * (b / g) /\
  Z.gcd (a / g) (b / g) = 1.
Proof.
  intros Ha Hb g.
  assert (Hg0 : 0 <= g) by (unfold g; apply Z.gcd_nonneg).
  assert (Hgne : g <> 0).
  { intro E. pose proof (Z.gcd_divide_l a b) as [k Hk].
    change (a = k * g) in Hk. rewrite E in Hk. lia. }
  assert (Hg : 1 <= g) by lia.
  assert (Ea : a = g * (a / g)).
  { apply Z.div_exact; auto. apply Z.mod_divide; auto.
    unfold g; apply Z.gcd_divide_l. }
  assert (Eb : b = g * (b / g)).
  { apply Z.div_exact; auto. apply Z.mod_divide; auto.
    unfold g; apply Z.gcd_divide_r. }
  repeat split; try nia.
  apply Z.gcd_div_gcd; auto.
Qed.

Lemma RC_valid_ray a b :
  1 <= a -> 1 <= b -> (a + b | b * Z.gcd a b) ->
  exists t, 1 <= t /\
    a = t * (a / Z.gcd a b) * (a / Z.gcd a b + b / Z.gcd a b) /\
    b = t * (b / Z.gcd a b) * (a / Z.gcd a b + b / Z.gcd a b).
Proof.
  intros Ha Hb Hdiv.
  pose proof (RC_primitive_decomposition a b Ha Hb) as Hdec.
  cbn zeta in Hdec.
  set (g := Z.gcd a b) in *.
  set (p := a / g) in *.
  set (q := b / g) in *.
  destruct Hdec as [Hg [Hp [Hq [Ea [Eb Hcop]]]]].
  assert (Hd : (p + q | q * g)).
  { destruct Hdiv as [k Hk]. exists k. nia. }
  assert (Hsumcop : Z.gcd (p + q) q = 1).
  { rewrite Z.gcd_comm, Z.gcd_add_diag_r, Z.gcd_comm. exact Hcop. }
  pose proof (Z.gauss (p + q) q g Hd Hsumcop) as [t Ht].
  exists t. repeat split; nia.
Qed.

Lemma RC_le_div_iff x d k : 0 < d -> (k <= x / d <-> k * d <= x).
Proof.
  intros Hd. split; intros H.
  - pose proof (Z.mul_div_le x d Hd). nia.
  - apply Z.div_le_lower_bound; nia.
Qed.

Lemma RC_multiplier_bound n m p q t :
  1 <= p -> 1 <= q ->
  (t <= Z.min (n / p) (m / q) / (p + q) <->
   t * p * (p + q) <= n /\ t * q * (p + q) <= m).
Proof.
  intros Hp Hq.
  rewrite RC_le_div_iff by lia.
  rewrite Z.min_glb_iff.
  rewrite !RC_le_div_iff by lia.
  split; intros [Hn Hm]; split; nia.
Qed.

Lemma RC_ray_coordinates p q t :
  1 <= p -> 1 <= q -> 1 <= t -> Z.gcd p q = 1 ->
  let a := t * p * (p + q) in
  let b := t * q * (p + q) in
  a / Z.gcd a b = p /\ b / Z.gcd a b = q.
Proof.
  intros Hp Hq Ht Hg. cbn zeta.
  rewrite RC_ray_gcd by (try nia; assumption).
  replace (t * p * (p + q)) with (p * (t * (p + q))) by ring.
  replace (t * q * (p + q)) with (q * (t * (p + q))) by ring.
  rewrite !Z.div_mul by nia. auto.
Qed.

Lemma RC_ray_injective p q t u :
  1 <= p -> 1 <= q ->
  t * p * (p + q) = u * p * (p + q) -> t = u.
Proof. intros Hp Hq E.
  apply Z.mul_reg_r in E; [|lia].
  apply Z.mul_reg_r in E; [exact E|lia].
Qed.

Lemma RC_valid_normalized_bounds n m a b :
  1 <= a <= n -> 1 <= b <= m -> (a + b | b * Z.gcd a b) ->
  1 <= a / Z.gcd a b /\ 1 <= b / Z.gcd a b /\
  (a / Z.gcd a b) * (a / Z.gcd a b) < n /\
  (b / Z.gcd a b) * (b / Z.gcd a b) < m.
Proof.
  intros [Ha Han] [Hb Hbm] Hd.
  pose proof (RC_primitive_decomposition a b Ha Hb) as Hdec.
  cbn zeta in Hdec.
  destruct Hdec as [Hg [Hp [Hq _]]].
  destruct (RC_valid_ray a b Ha Hb Hd) as [t [Ht [Ea Eb]]].
  pose proof (RC_ray_square_bounds n m (a / Z.gcd a b) (b / Z.gcd a b) t
    Hp Hq Ht ltac:(lia) ltac:(lia)) as Hbounds.
  tauto.
Qed.

Definition RCFiber (n m p q : Z) (ab : Z * Z) : Prop :=
  ((1 <= fst ab < n + 1 /\ 1 <= snd ab < m + 1) /\
   (fst ab + snd ab | snd ab * Z.gcd (fst ab) (snd ab))) /\
  fst ab / Z.gcd (fst ab) (snd ab) = p /\
  snd ab / Z.gcd (fst ab) (snd ab) = q.

#[local] Instance RC_fiber_finite n m p q : Finite (RCFiber n m p q) :=
  Finite_subset _ _.

Definition RCRay (p q t : Z) : Z * Z :=
  (t * p * (p + q), t * q * (p + q)).

Lemma RC_fiber_iff n m p q ab :
  1 <= p -> 1 <= q -> Z.gcd p q = 1 ->
  (RCFiber n m p q ab <->
   exists t, 1 <= t <= Z.min (n / p) (m / q) / (p + q) /\
     ab = RCRay p q t).
Proof.
  intros Hp Hq Hcop. destruct ab as [a b].
  unfold RCFiber, RCRay; cbn [fst snd]. split.
  - intros [[[Ha Hb] Hd] [Ep Eq]].
    destruct (RC_valid_ray a b ltac:(lia) ltac:(lia) Hd) as [t [Ht [Ea Eb]]].
    rewrite Ep, Eq in Ea, Eb.
    exists t. split.
    + split; [assumption|]. apply RC_multiplier_bound; try assumption. lia.
    + f_equal; assumption.
  - intros [t [[Ht Hbound] E]]. inversion E; subst a b.
    pose proof (proj1 (RC_multiplier_bound n m p q t Hp Hq) Hbound) as [Hn Hm].
    pose proof (RC_ray_coordinates p q t Hp Hq Ht Hcop) as Hcoords.
    cbn zeta in Hcoords.
    split; [split|exact Hcoords].
    + split; split; nia.
    + apply RC_ray_valid; assumption.
Qed.

Require Import Coq.Sorting.Permutation.

Lemma RC_card_enum {A : Type} (P : A -> Prop) {FP : Finite P} :
  set_card P = Z.of_nat (length (@enum A P FP)).
Proof.
  unfold set_card, Sum.sum.
  induction (@enum A P FP) as [|x xs IH].
  - reflexivity.
  - change (1 + fold_right (fun (_ : A) acc => 1 + acc) 0 xs =
       Z.of_nat (S (length xs))).
    rewrite IH, Nat2Z.inj_succ. lia.
Qed.

Lemma RC_card_bijection {A B : Type} (P : A -> Prop) (Q : B -> Prop)
    {FP : Finite P} {FQ : Finite Q} (f : A -> B) :
  (forall x, P x -> Q (f x)) ->
  (forall y, Q y -> exists x, P x /\ f x = y) ->
  (forall x y, P x -> P y -> f x = f y -> x = y) ->
  set_card P = set_card Q.
Proof.
  intros Hinto Honto Hinj.
  rewrite !RC_card_enum.
  assert (Hp : Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  { apply NoDup_Permutation.
    - apply Injective_map_NoDup_in; [|apply enum_nodup].
      intros x y Hx Hy E. apply Hinj; auto; apply enum_ok; assumption.
    - apply enum_nodup.
    - intros y. rewrite in_map_iff. split.
      + intros [x [E Hx]]. subst y. apply enum_ok. apply Hinto. apply enum_ok. exact Hx.
      + intros Hy. apply enum_ok in Hy.
        destruct (Honto y Hy) as [x [Hx E]]. exists x. split; auto. apply enum_ok; auto. }
  apply Permutation_length in Hp. rewrite length_map in Hp. now rewrite Hp.
Qed.

Lemma RC_fiber_card n m p q :
  1 <= n -> 1 <= m -> 1 <= p -> 1 <= q -> Z.gcd p q = 1 ->
  set_card (RCFiber n m p q) = Z.min (n / p) (m / q) / (p + q).
Proof.
  intros Hn Hm Hp Hq Hcop.
  set (lim := Z.min (n / p) (m / q) / (p + q)).
  assert (Hlim : 0 <= lim).
  { unfold lim. apply Z.div_pos; [apply Z.min_glb; apply Z.div_pos; lia|lia]. }
  assert (E : set_card (fun t : Z => 1 <= t < lim + 1) = set_card (RCFiber n m p q)).
  { apply (RC_card_bijection _ _ (RCRay p q)).
    - intros t Ht. apply RC_fiber_iff; auto. exists t. split; [unfold lim in *; lia|reflexivity].
    - intros ab Hab. apply RC_fiber_iff in Hab; auto.
      destruct Hab as [t [Ht E]]. exists t. split; [unfold lim; lia|symmetry; exact E].
    - intros t u Ht Hu E.
      apply (RC_ray_injective p q t u Hp Hq).
      exact (f_equal (@fst Z Z) E). }
  rewrite <- E. unfold set_card.
  rewrite sum_Z_range_const by lia. lia.
Qed.

Lemma RC_nodup_app__fiber_step {A} (xs ys : list A) :
  NoDup xs -> NoDup ys -> (forall x, In x xs -> In x ys -> False) ->
  NoDup (xs ++ ys).
Proof.
  intros Hx Hy Hd. induction Hx; simpl; auto.
  constructor.
  - rewrite in_app_iff. intros [Hbad|Hbad]; [contradiction|].
    apply (Hd x); simpl; auto.
  - apply IHHx. intros z Hz. apply Hd. simpl; auto.
Qed.
Lemma RC_card_disjoint_union__fiber_step {A : Type} (P Q R : A -> Prop)
    {FP : Finite P} {FQ : Finite Q} {FR : Finite R} :
  (forall x, R x <-> P x \/ Q x) ->
  (forall x, P x -> Q x -> False) ->
  set_card R = set_card P + set_card Q.
Proof.
  intros Hr Hd. rewrite !RC_card_enum.
  assert (E : Permutation (@enum A R FR) (@enum A P FP ++ @enum A Q FQ)).
  { apply NoDup_Permutation.
    - apply enum_nodup.
    - apply RC_nodup_app__fiber_step; try apply enum_nodup.
      intros x Hx Hy. apply (Hd x); apply enum_ok; assumption.
    - intros x. rewrite in_app_iff, <- (@enum_ok A R FR x), <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x). apply Hr. }
  apply Permutation_length in E. rewrite E, length_app, Nat2Z.inj_add. reflexivity.
Qed.
Lemma RC_progress_step__fiber_step n m p q ans :
  1 <= n -> 1 <= m -> 1 <= p -> 1 <= q -> Z.gcd p q = 1 ->
  RCProgress n m p q ans ->
  RCProgress n m p (q+1) (ans + Z.min (n/p) (m/q)/(p+q)).
Proof.
  intros Hn Hm Hp Hq Hg Ha. unfold RCProgress in *.
  rewrite Ha, <- (RC_fiber_card n m p q Hn Hm Hp Hq Hg).
  symmetry. apply RC_card_disjoint_union__fiber_step.
  - intros [a b]. unfold RCBefore, RCFiber. cbn [fst snd].
    destruct (Z_lt_ge_dec (b / Z.gcd a b) q); intuition lia.
  - intros [a b]. unfold RCBefore, RCFiber. cbn [fst snd].
    intuition lia.
Qed.
Lemma RC_quot_bounds__fiber_step x d e :
  0 <= x -> 1 <= d -> 1 <= e ->
  0 <= Z.quot (Z.quot x d) e <= x.
Proof.
  intros Hx Hd He.
  rewrite (Z.quot_div_nonneg x d) by lia.
  assert (Hdiv : 0 <= x/d) by (apply Z.div_pos; lia).
  rewrite Z.quot_div_nonneg by lia.
  split; [apply Z.div_pos; lia|].
  assert (Hupper : x/d <= x) by (apply Z.div_le_upper_bound; nia).
  assert (Hnested : (x/d)/e <= x/d) by (apply Z.div_le_upper_bound; nia).
  lia.
Qed.
Lemma RC_card_ext__prefix_boundaries {A : Type} (P Q : A -> Prop)
    {FP : Finite P} {FQ : Finite Q} :
  (forall x, P x <-> Q x) -> set_card P = set_card Q.
Proof.
  intros H. apply (RC_card_bijection P Q (fun x => x)).
  - intros x Hx. apply H; exact Hx.
  - intros y Hy. exists y. split; [apply H; exact Hy|reflexivity].
  - intros x y Hx Hy E. exact E.
Qed.
Lemma RC_progress_initial__prefix_boundaries n m : RCProgress n m 1 1 0.
Proof.
  unfold RCProgress, set_card. symmetry.
  eapply eq_trans; [apply sum_ext with (g := fun _ => 0)|apply sum_zero].
  intros [a b] [[[Ha Hb] Hd] Hbefore].
  unfold RCBefore in Hbefore; cbn [fst snd] in *.
  pose proof (RC_primitive_decomposition a b ltac:(lia) ltac:(lia)) as Hdec.
  cbn zeta in Hdec. destruct Hdec as [Hg [Hp [Hq _]]].
  exfalso. lia.
Qed.
Lemma RC_progress_row__prefix_boundaries n m p q ans :
  1 <= p -> 1 <= q -> m <= q*q ->
  RCProgress n m p q ans -> RCProgress n m (p+1) 1 ans.
Proof.
  intros Hp Hq Hm Hprogress. unfold RCProgress in *.
  rewrite Hprogress. apply RC_card_ext__prefix_boundaries.
  intros [a b]. unfold RCBefore; cbn [fst snd].
  assert (Hbounds : ((1 <= a < n+1 /\ 1 <= b < m+1) /\
      (a+b | b * Z.gcd a b)) -> 1 <= b / Z.gcd a b /\ b / Z.gcd a b < q).
  { intros [[Ha Hb] Hd].
    pose proof (RC_valid_normalized_bounds n m a b ltac:(lia) ltac:(lia) Hd).
    nia. }
  split; intros [Hvalid Hbefore]; split; try exact Hvalid;
    pose proof (Hbounds Hvalid); lia.
Qed.
Lemma RC_progress_skip__prefix_boundaries n m p q ans :
  Z.gcd p q <> 1 -> RCProgress n m p q ans ->
  RCProgress n m p (q+1) ans.
Proof.
  intros Hcop Hprogress. unfold RCProgress in *.
  rewrite Hprogress. apply RC_card_ext__prefix_boundaries.
  intros [a b]. unfold RCBefore; cbn [fst snd].
  split; intros [Hvalid Hbefore]; split; try exact Hvalid.
  - lia.
  - destruct Hvalid as [[Ha Hb] Hd].
    pose proof (RC_primitive_decomposition a b ltac:(lia) ltac:(lia)) as Hdec.
    cbn zeta in Hdec. destruct Hdec as [Hg [Hp [Hq [Ea [Eb Hprim]]]]].
    assert (Hneq : a / Z.gcd a b <> p \/ b / Z.gcd a b <> q).
    { destruct (Z.eq_dec (a / Z.gcd a b) p) as [E|E]; [right|auto].
      intro F. rewrite E, F in Hprim. contradiction. }
    lia.
Qed.
Lemma RC_progress_finish__prefix_boundaries n m p ans :
  1 <= p -> n <= p*p -> RCProgress n m p 1 ans -> Spec n m ans.
Proof.
  intros Hp Hn Hprogress. unfold RCProgress in Hprogress. unfold Spec.
  rewrite Hprogress. apply RC_card_ext__prefix_boundaries.
  intros [a b]. unfold RCBefore; cbn [fst snd].
  split; [tauto|]. intros Hvalid. split; [exact Hvalid|].
  destruct Hvalid as [[Ha Hb] Hd].
  pose proof (RC_valid_normalized_bounds n m a b ltac:(lia) ltac:(lia) Hd).
  left. nia.
Qed.
