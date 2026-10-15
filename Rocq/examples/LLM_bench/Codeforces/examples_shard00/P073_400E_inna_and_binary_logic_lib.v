Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition AndExerciseSum (a : list Z) : Z :=
  fold_right Z.add 0
    (map (fun p => let '(l,r) := p in
      fold_left Z.land (sublist l (r+1) a) (-1))
      (concat (Zmap_range
        (fun l => map (fun r => (l,r)) (Zrange l (Zlength a)))
        (Zlength a)))).

Definition ApplyPointUpdate (a : list Z) (u : Z * Z) : list Z :=
  replace_Znth (fst u) (snd u) a.

Definition Pre (a : list Z) (updates : list (Z * Z)) : Prop :=
  1 <= Zlength a <= 100000 /\ 1 <= Zlength updates <= 100000 /\
  Forall (fun x => 0 <= x <= 100000) a /\
  Forall (fun u => 0 <= fst u < Zlength a /\ 0 <= snd u <= 100000) updates.

Definition Spec (a : list Z) (updates : list (Z * Z)) (out : list Z) : Prop :=
  exists states,
    Zlength states = Zlength updates + 1 /\ Znth 0 states nil = a /\
    (forall i, 0 <= i < Zlength updates ->
      Znth (i+1) states nil = ApplyPointUpdate (Znth i states nil) (Znth i updates (0,0))) /\
    Zlength out = Zlength updates /\
    forall i, 0 <= i < Zlength out ->
      Znth i out 0 = AndExerciseSum (Znth (i+1) states nil).

(* Auxiliary mathematical summaries; the specification above is unchanged. *)
Definition P073AllOn (b : Z) (xs : list Z) : bool :=
  forallb (fun x => Z.testbit x b) xs.

Definition P073Indicator (p : bool) : Z := if p then 1 else 0.

Definition P073Prefix (b : Z) (xs : list Z) : Z :=
  fold_right Z.add 0
    (map (fun k => P073Indicator (P073AllOn b (sublist 0 k xs)))
      (Zrange 1 (Zlength xs + 1))).

Definition P073Suffix (b : Z) (xs : list Z) : Z :=
  fold_right Z.add 0
    (map (fun k => P073Indicator
      (P073AllOn b (sublist (Zlength xs - k) (Zlength xs) xs)))
      (Zrange 1 (Zlength xs + 1))).

Definition P073Count (b : Z) (xs : list Z) : Z :=
  fold_right Z.add 0
    (map (fun l => fold_right Z.add 0
      (map (fun r => P073Indicator (P073AllOn b (sublist l (r+1) xs)))
        (Zrange l (Zlength xs)))) (Zrange 0 (Zlength xs))).

Definition P073Summary (b : Z) (xs : list Z) (p s c : Z) : Prop :=
  p = P073Prefix b xs /\ s = P073Suffix b xs /\ c = P073Count b xs.

(* A mathematical binary partition, independent of array contents. *)
Inductive P073Desc : Z -> Z -> Z -> Z -> Z -> Z -> Prop :=
| P073Desc_here : forall v l r, P073Desc v l r v l r
| P073Desc_left : forall v l r w lo hi,
    r-l > 1 -> P073Desc (2*v) l ((l+r)/2) w lo hi ->
    P073Desc v l r w lo hi
| P073Desc_right : forall v l r w lo hi,
    r-l > 1 -> P073Desc (2*v+1) ((l+r)/2) r w lo hi ->
    P073Desc v l r w lo hi.

Definition P073Layout (n v l r : Z) : Prop :=
  forall w lo hi, P073Desc v l r w lo hi ->
    0 < w < 4*n /\ 0 <= lo < hi /\ hi <= n.

Definition P073Tree (n v l r : Z) (xs pr su ct ln : list Z) : Prop :=
  forall w lo hi, P073Desc v l r w lo hi ->
    Znth w ln 0 = hi-lo /\
    forall b, 0 <= b < 17 ->
      P073Summary b (sublist lo hi xs)
        (Znth (b*4*n+w) pr 0) (Znth (b*4*n+w) su 0)
        (Znth (b*4*n+w) ct 0).

Definition P073ZeroTree (n v l r : Z) (pr su ct ln : list Z) : Prop :=
  forall w lo hi, P073Desc v l r w lo hi ->
    Znth w ln 0 = 0 /\
    forall b, 0 <= b < 17 ->
      Znth (b*4*n+w) pr 0 = 0 /\ Znth (b*4*n+w) su 0 = 0 /\
      Znth (b*4*n+w) ct 0 = 0.

Definition P073OutsideTree (n v l r : Z)
    (oldpr oldsu oldct oldln pr su ct ln : list Z) : Prop :=
  (forall w, 0 <= w < 4*n ->
    (forall lo hi, ~ P073Desc v l r w lo hi) ->
    Znth w ln 0 = Znth w oldln 0) /\
  (forall w b, 0 <= w < 4*n -> 0 <= b < 17 ->
    (forall lo hi, ~ P073Desc v l r w lo hi) ->
    Znth (b*4*n+w) pr 0 = Znth (b*4*n+w) oldpr 0 /\
    Znth (b*4*n+w) su 0 = Znth (b*4*n+w) oldsu 0 /\
    Znth (b*4*n+w) ct 0 = Znth (b*4*n+w) oldct 0).

Definition P073NodePrefix (n v bits : Z) (xs pr su ct : list Z) : Prop :=
  forall b, 0 <= b < bits ->
    P073Summary b xs (Znth (b*4*n+v) pr 0)
      (Znth (b*4*n+v) su 0) (Znth (b*4*n+v) ct 0).

Definition P073NodeFrame (n v bits : Z)
    (oldpr oldsu oldct pr su ct : list Z) : Prop :=
  forall b w, 0 <= b < 17 -> 0 <= w < 4*n ->
    (w <> v \/ bits <= b) ->
    Znth (b*4*n+w) pr 0 = Znth (b*4*n+w) oldpr 0 /\
    Znth (b*4*n+w) su 0 = Znth (b*4*n+w) oldsu 0 /\
    Znth (b*4*n+w) ct 0 = Znth (b*4*n+w) oldct 0.

Definition P073BufferBounds (n : Z) (pr su ct ln : list Z) : Prop :=
  (forall k, 0 <= k < 68*n ->
    0 <= Znth k pr 0 <= n /\ 0 <= Znth k su 0 <= n /\
    0 <= Znth k ct 0 <= n*(n+1)/2) /\
  (forall k, 0 <= k < 4*n -> 0 <= Znth k ln 0 <= n).

Definition P073Weighted (xs : list Z) (bits : Z) : Z :=
  fold_right Z.add 0
    (map (fun b => P073Count b xs * 2^b) (Zrange 0 bits)).

Definition P073History (initial : list Z) (updates : list (Z*Z))
    (done : Z) (current output : list Z) : Prop :=
  exists states,
    Zlength states = done+1 /\ Znth 0 states nil = initial /\
    Znth done states nil = current /\
    (forall i, 0 <= i < done ->
      Znth (i+1) states nil = ApplyPointUpdate (Znth i states nil)
        (Znth i updates (0,0))) /\
    Zlength output = done /\
    (forall i, 0 <= i < done ->
      Znth i output 0 = AndExerciseSum (Znth (i+1) states nil)).

Lemma P073AllOn_app : forall b xs ys,
  P073AllOn b (xs ++ ys) = andb (P073AllOn b xs) (P073AllOn b ys).
Proof. intros; unfold P073AllOn; apply forallb_app. Qed.

Lemma P073AllOn_fold_and : forall b xs acc,
  Z.testbit (fold_left Z.land xs acc) b =
  andb (Z.testbit acc b) (P073AllOn b xs).
Proof.
  intros b xs; induction xs as [|x xs IH]; intros acc.
  - simpl. unfold P073AllOn; simpl. now rewrite Bool.andb_true_r.
  - simpl. rewrite IH, Z.land_spec. unfold P073AllOn; simpl.
    now rewrite Bool.andb_assoc.
Qed.

Lemma P073History_finish : forall initial updates current output,
  P073History initial updates (Zlength updates) current output ->
  Spec initial updates output.
Proof.
  intros initial updates current output [states [Hlen [Hinitial [Hcurrent [Hsteps [Hout Hanswers]]]]]].
  exists states. repeat split; auto.
  intros i Hi. apply Hanswers. now rewrite <- Hout.
Qed.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Lemma P073Mid_sublist__build_recursive : forall l r,
  0 <= l -> r-l > 1 ->
  l < (l+r)/2 < r /\ Z.quot (l+r) 2 = (l+r)/2.
Proof.
  intros l r Hl Hr.
  pose proof (Z.div_mod (l+r) 2 ltac:(lia)) as He.
  pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)) as Hb.
  split; [lia|apply Z.quot_div_nonneg; lia].
Qed.
Lemma P073Desc_mono__build_recursive : forall v l r w lo hi,
  P073Desc v l r w lo hi -> 0 < v -> v <= w.
Proof.
  intros v l r w lo hi H; induction H; intros Hv.
  - lia.
  - specialize (IHP073Desc ltac:(lia)); lia.
  - specialize (IHP073Desc ltac:(lia)); lia.
Qed.
Lemma P073Desc_cone__build_recursive : forall v l r w lo hi,
  P073Desc v l r w lo hi ->
  exists d, 0 <= d /\ v*2^d <= w < (v+1)*2^d.
Proof.
  intros v l r w lo hi H; induction H.
  - exists 0; cbn; lia.
  - destruct IHP073Desc as [d [Hd Hw]].
    exists (d+1). rewrite Z.pow_add_r by lia.
    change (2^1) with 2. pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) Hd).
    split; [lia|nia].
  - destruct IHP073Desc as [d [Hd Hw]].
    exists (d+1). rewrite Z.pow_add_r by lia.
    change (2^1) with 2. pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) Hd).
    split; [lia|nia].
Qed.
Lemma P073Desc_domains__build_recursive : forall v l r w lo hi lo' hi',
  0 < v ->
  P073Desc (2*v) l ((l+r)/2) w lo hi ->
  P073Desc (2*v+1) ((l+r)/2) r w lo' hi' -> False.
Proof.
  intros v l r w lo hi lo' hi' Hv HL HR.
  destruct (P073Desc_cone__build_recursive _ _ _ _ _ _ HL) as [d [Hd HW]].
  destruct (P073Desc_cone__build_recursive _ _ _ _ _ _ HR) as [e [He HW']].
  pose proof (Z.pow_pos_nonneg 2 d ltac:(lia) Hd).
  pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He).
  destruct (Z.lt_trichotomy d e) as [Hlt|[Heq|Hgt]].
  - pose proof (Z.pow_le_mono_r 2 (d+1) e ltac:(lia) ltac:(lia)) as Hp.
    rewrite Z.pow_add_r in Hp by lia. change (2^1) with 2 in Hp. nia.
  - subst e; nia.
  - pose proof (Z.pow_le_mono_r 2 (e+1) d ltac:(lia) ltac:(lia)) as Hp.
    rewrite Z.pow_add_r in Hp by lia. change (2^1) with 2 in Hp. nia.
Qed.
Lemma P073Children_layout__build_recursive : forall n v l r,
  r-l > 1 -> P073Layout n v l r ->
  P073Layout n (2*v) l ((l+r)/2) /\
  P073Layout n (2*v+1) ((l+r)/2) r.
Proof.
  intros n v l r Hr HL; split; intros w lo hi HD; apply HL;
    [apply P073Desc_left | apply P073Desc_right]; assumption.
Qed.
Lemma P073Children_zero__build_recursive : forall n v l r pr su ct ln,
  0 < v -> r-l > 1 -> Zlength ln = 4*n ->
  P073Layout n v l r -> P073ZeroTree n v l r pr su ct ln ->
  P073ZeroTree n (2*v) l ((l+r)/2) pr su ct (replace_Znth v (r-l) ln) /\
  P073ZeroTree n (2*v+1) ((l+r)/2) r pr su ct (replace_Znth v (r-l) ln).
Proof.
  intros n v l r pr su ct ln Hv Hr Hlen HL HZ.
  pose proof (HL _ _ _ (P073Desc_here v l r)) as HB.
  split; intros w lo hi HD.
  - pose proof (P073Desc_left _ _ _ _ _ _ Hr HD) as DP.
    pose proof (HL _ _ _ DP) as BW.
    pose proof (P073Desc_mono__build_recursive _ _ _ _ _ _ HD ltac:(lia)) as HM.
    specialize (HZ _ _ _ DP). rewrite Znth_replace_Znth_Diff by lia. exact HZ.
  - pose proof (P073Desc_right _ _ _ _ _ _ Hr HD) as DP.
    pose proof (HL _ _ _ DP) as BW.
    pose proof (P073Desc_mono__build_recursive _ _ _ _ _ _ HD ltac:(lia)) as HM.
    specialize (HZ _ _ _ DP). rewrite Znth_replace_Znth_Diff by lia. exact HZ.
Qed.
Lemma P073Right_zero__build_recursive : forall n v l r pr su ct ln pr' su' ct' ln',
  0 < v -> r-l > 1 -> P073Layout n v l r ->
  P073ZeroTree n (2*v+1) ((l+r)/2) r pr su ct ln ->
  P073OutsideTree n (2*v) l ((l+r)/2) pr su ct ln pr' su' ct' ln' ->
  P073ZeroTree n (2*v+1) ((l+r)/2) r pr' su' ct' ln'.
Proof.
  intros n v l r pr su ct ln pr' su' ct' ln' Hv Hr HL HZ [FL FA] w lo hi HD.
  pose proof (HL _ _ _ (P073Desc_right _ _ _ _ _ _ Hr HD)) as BW.
  assert (HO : forall x y, ~ P073Desc (2*v) l ((l+r)/2) w x y).
  { intros x y D. eapply P073Desc_domains__build_recursive; eauto. }
  destruct (HZ _ _ _ HD) as [HZL HZA].
  split.
  - rewrite FL by (try lia; exact HO). exact HZL.
  - intros b Hb. destruct (FA w b ltac:(lia) Hb HO) as [E1 [E2 E3]].
    rewrite E1,E2,E3. apply HZA; assumption.
Qed.
Lemma P073Left_tree__build_recursive : forall n v l r xs pr su ct ln pr' su' ct' ln',
  0 < v -> r-l > 1 -> P073Layout n v l r ->
  P073Tree n (2*v) l ((l+r)/2) xs pr su ct ln ->
  P073OutsideTree n (2*v+1) ((l+r)/2) r pr su ct ln pr' su' ct' ln' ->
  P073Tree n (2*v) l ((l+r)/2) xs pr' su' ct' ln'.
Proof.
  intros n v l r xs pr su ct ln pr' su' ct' ln' Hv Hr HL HT [FL FA] w lo hi HD.
  pose proof (HL _ _ _ (P073Desc_left _ _ _ _ _ _ Hr HD)) as BW.
  assert (HO : forall x y, ~ P073Desc (2*v+1) ((l+r)/2) r w x y).
  { intros x y D. eapply P073Desc_domains__build_recursive; eauto. }
  destruct (HT _ _ _ HD) as [HTL HTA].
  split.
  - rewrite FL by (try lia; exact HO). exact HTL.
  - intros b Hb. destruct (FA w b ltac:(lia) Hb HO) as [E1 [E2 E3]].
    rewrite E1,E2,E3. apply HTA; assumption.
Qed.
Lemma P073Root_length__build_recursive : forall n v l r pr su ct ln pr1 su1 ct1 ln1 pr2 su2 ct2 ln2,
  0 < v -> v < 4*n -> Zlength ln=4*n ->
  P073OutsideTree n (2*v) l ((l+r)/2) pr su ct (replace_Znth v (r-l) ln) pr1 su1 ct1 ln1 ->
  P073OutsideTree n (2*v+1) ((l+r)/2) r pr1 su1 ct1 ln1 pr2 su2 ct2 ln2 ->
  Znth v ln2 0 = r-l.
Proof.
  intros n v l r pr su ct ln pr1 su1 ct1 ln1 pr2 su2 ct2 ln2 Hv HB Hlen [F1 _] [F2 _].
  assert (H1 : forall x y, ~ P073Desc (2*v) l ((l+r)/2) v x y).
  { intros x y D; pose proof (P073Desc_mono__build_recursive _ _ _ _ _ _ D ltac:(lia)); lia. }
  assert (H2 : forall x y, ~ P073Desc (2*v+1) ((l+r)/2) r v x y).
  { intros x y D; pose proof (P073Desc_mono__build_recursive _ _ _ _ _ _ D ltac:(lia)); lia. }
  rewrite F2 by (try lia; exact H2).
  rewrite F1 by (try lia; exact H1).
  apply Znth_replace_Znth_Same; lia.
Qed.
Lemma P073Outside_parent__build_recursive : forall n v l r pr su ct ln pr1 su1 ct1 ln1 pr2 su2 ct2 ln2 pr3 su3 ct3,
  0 < v -> v < 4*n -> r-l > 1 -> Zlength ln=4*n ->
  P073OutsideTree n (2*v) l ((l+r)/2) pr su ct (replace_Znth v (r-l) ln) pr1 su1 ct1 ln1 ->
  P073OutsideTree n (2*v+1) ((l+r)/2) r pr1 su1 ct1 ln1 pr2 su2 ct2 ln2 ->
  P073NodeFrame n v 17 pr2 su2 ct2 pr3 su3 ct3 ->
  P073OutsideTree n v l r pr su ct ln pr3 su3 ct3 ln2.
Proof.
  intros n v l r pr su ct ln pr1 su1 ct1 ln1 pr2 su2 ct2 ln2 pr3 su3 ct3 Hv HB Hr Hlen [FL1 FA1] [FL2 FA2] FN.
  split.
  - intros w Hw HO.
    assert (HL : forall x y, ~ P073Desc (2*v) l ((l+r)/2) w x y).
    { intros x y H; apply (HO x y); apply P073Desc_left; assumption. }
    assert (HR : forall x y, ~ P073Desc (2*v+1) ((l+r)/2) r w x y).
    { intros x y H; apply (HO x y); apply P073Desc_right; assumption. }
    assert (Hneq : v<>w) by (intro E; subst w; apply (HO l r); constructor).
    rewrite FL2 by assumption. rewrite FL1 by assumption.
    apply Znth_replace_Znth_Diff; lia.
  - intros w b Hw Hb HO.
    assert (HL : forall x y, ~ P073Desc (2*v) l ((l+r)/2) w x y).
    { intros x y H; apply (HO x y); apply P073Desc_left; assumption. }
    assert (HR : forall x y, ~ P073Desc (2*v+1) ((l+r)/2) r w x y).
    { intros x y H; apply (HO x y); apply P073Desc_right; assumption. }
    assert (Hneq : w<>v) by (intro E; subst w; apply (HO l r); constructor).
    destruct (FA1 w b Hw Hb HL) as [E1 [E2 E3]].
    destruct (FA2 w b Hw Hb HR) as [E4 [E5 E6]].
    destruct (FN b w Hb Hw (or_introl Hneq)) as [E7 [E8 E9]].
    rewrite E7,E8,E9,E4,E5,E6,E1,E2,E3; auto.
Qed.
Lemma P073Tree_frames__build_recursive : forall n v l r xs pr su ct ln pr1 su1 ct1,
  0 < v -> 0 <= l -> r-l>1 -> r<=Zlength xs ->
  P073Layout n v l r -> Znth v ln 0=r-l ->
  P073Tree n (2*v) l ((l+r)/2) xs pr su ct ln ->
  P073Tree n (2*v+1) ((l+r)/2) r xs pr su ct ln ->
  P073NodePrefix n v 17 (sublist l ((l+r)/2) xs ++ sublist ((l+r)/2) r xs) pr1 su1 ct1 ->
  P073NodeFrame n v 17 pr su ct pr1 su1 ct1 ->
  P073Tree n v l r xs pr1 su1 ct1 ln.
Proof.
  intros n v l r xs pr su ct ln pr1 su1 ct1 Hv Hl Hr Hlen HL Hroot HTL HTR HP HF w lo hi HD.
  pose proof (HL _ _ _ HD) as HW.
  destruct (P073Mid_sublist__build_recursive l r Hl Hr) as [HM HQ].
  inversion HD; subst.
  - split; [exact Hroot|].
    intros b Hb; specialize (HP b Hb).
    rewrite <- sublist_split in HP by lia. exact HP.
  - match goal with D : P073Desc (2*v) _ _ w lo hi |- _ =>
      pose proof (P073Desc_mono__build_recursive _ _ _ _ _ _ D ltac:(lia)) as Hmono;
      destruct (HTL _ _ _ D) as [HLn HS]
    end.
    split; [exact HLn|]. intros b Hb.
    destruct (HF b w Hb ltac:(lia) ltac:(left; lia)) as [E1 [E2 E3]].
    rewrite E1,E2,E3; apply HS; exact Hb.
  - match goal with D : P073Desc (2*v+1) _ _ w lo hi |- _ =>
      pose proof (P073Desc_mono__build_recursive _ _ _ _ _ _ D ltac:(lia)) as Hmono;
      destruct (HTR _ _ _ D) as [HLn HS]
    end.
    split; [exact HLn|]. intros b Hb.
    destruct (HF b w Hb ltac:(lia) ltac:(left; lia)) as [E1 [E2 E3]].
    rewrite E1,E2,E3; apply HS; exact Hb.
Qed.
Lemma P073Packed_injective__pull_merge : forall n b d v w,
  0 < n -> 0 <= v < 4*n -> 0 <= w < 4*n ->
  b*4*n+v = d*4*n+w -> b=d /\ v=w.
Proof.
  intros. assert (b=d) by (destruct (Z.lt_trichotomy b d) as [Hlt|[Heq|Hgt]]; nia).
  split; nia.
Qed.
Lemma P073Packed_replace__pull_merge : forall (xs : list Z) i j x,
  0 <= i -> 0 <= j -> i <> j ->
  Znth j (replace_Znth i x xs) 0 = Znth j xs 0.
Proof.
  intros xs i j x Hi Hj Hne. unfold Znth, replace_Znth.
  assert (Z.to_nat i <> Z.to_nat j) as Hnat by lia.
  generalize dependent (Z.to_nat i). generalize dependent (Z.to_nat j).
  induction xs as [|a xs IH]; intros m k Hkm; destruct m, k; simpl in *;
    try reflexivity; try congruence.
  apply IH. congruence.
Qed.
Lemma P073Range_ext__pull_merge : forall lo hi (f g : Z -> Z),
  (forall k, lo <= k < hi -> f k = g k) ->
  fold_right Z.add 0 (map f (Zrange lo hi)) =
  fold_right Z.add 0 (map g (Zrange lo hi)).
Proof.
  intros. f_equal. apply map_ext_in. intros k Hk.
  apply H. now apply In_Zrange.
Qed.
Lemma P073Fold_map__pull_merge : forall (xs : list Z) (f : Z -> Z),
  fold_right Z.add 0 (map f xs) = fold_right (fun x acc => f x + acc) 0 xs.
Proof. intros xs f. induction xs; simpl; congruence. Qed.
Lemma P073Range_shift__pull_merge : forall lo hi k (f : Z -> Z),
  fold_right Z.add 0 (map f (Zrange (lo+k) (hi+k))) =
  fold_right Z.add 0 (map (fun x => f (x+k)) (Zrange lo hi)).
Proof.
  intros. rewrite !P073Fold_map__pull_merge. unfold Zrange.
  replace (hi+k-(lo+k)) with (hi-lo) by lia.
  apply fold_Zrange_aux_shift_by.
Qed.
Lemma P073Range_cons__pull_merge : forall lo hi (f : Z -> Z), lo < hi ->
  fold_right Z.add 0 (map f (Zrange lo hi)) =
  f lo + fold_right Z.add 0 (map f (Zrange (lo+1) hi)).
Proof.
  intros. unfold Zrange.
  replace (Z.to_nat (hi-lo)) with (S (Z.to_nat (hi-(lo+1)))) by lia.
  reflexivity.
Qed.
Lemma P073Range_split__pull_merge : forall lo mid hi (f : Z -> Z),
  lo <= mid <= hi ->
  fold_right Z.add 0 (map f (Zrange lo hi)) =
  fold_right Z.add 0 (map f (Zrange lo mid)) +
  fold_right Z.add 0 (map f (Zrange mid hi)).
Proof.
  intros. rewrite !P073Fold_map__pull_merge, <- !sum_range_unfold.
  apply sum_Z_range_split; lia.
Qed.
Lemma P073Range_factor__pull_merge : forall lo hi c (f : Z -> Z),
  fold_right Z.add 0 (map (fun x => c*f x) (Zrange lo hi)) =
  c * fold_right Z.add 0 (map f (Zrange lo hi)).
Proof.
  intros. induction (Zrange lo hi); simpl; [ring|rewrite IHl; ring].
Qed.
Lemma P073Indicator_and__pull_merge : forall p q,
  P073Indicator (andb p q) = P073Indicator p * P073Indicator q.
Proof. intros [] []; reflexivity. Qed.
Lemma P073Prefix_cons__pull_merge : forall b x xs,
  P073Prefix b (x::xs) = P073Indicator (Z.testbit x b) * (1+P073Prefix b xs).
Proof.
  intros. unfold P073Prefix. rewrite Zlength_cons.
  replace (Zlength xs+1+1) with ((Zlength xs+1)+1) by lia.
  replace 1 with (0+1) at 1 by lia.
  rewrite P073Range_shift__pull_merge.
  rewrite P073Range_cons__pull_merge by (pose proof (Zlength_nonneg xs); lia).
  replace (0+1) with 1 by lia.
  replace (Z.succ (Zlength xs)) with (Zlength xs+1) by lia.
  assert (Hhead : sublist 0 1 (x::xs) = x::nil) by reflexivity.
  rewrite Hhead. unfold P073AllOn at 1. simpl.
  rewrite Bool.andb_true_r.
  erewrite P073Range_ext__pull_merge with
    (g:=fun k => P073Indicator (Z.testbit x b) * P073Indicator (P073AllOn b (sublist 0 k xs))).
  2:{ intros k Hk. rewrite sublist_cons1 by lia.
      replace (k+1-1) with k by lia. unfold P073AllOn at 1. simpl.
      apply P073Indicator_and__pull_merge. }
  rewrite P073Range_factor__pull_merge.
  change (P073Indicator (Z.testbit x b) + P073Indicator (Z.testbit x b) * P073Prefix b xs =
    P073Indicator (Z.testbit x b) * (1+P073Prefix b xs)). ring.
Qed.
Lemma P073Range_empty__pull_merge : forall lo hi f, hi <= lo ->
  fold_right Z.add 0 (map f (Zrange lo hi)) = 0.
Proof. intros. unfold Zrange. replace (Z.to_nat (hi-lo)) with 0%nat by lia. reflexivity. Qed.
Lemma P073Range_single__pull_merge : forall lo f,
  fold_right Z.add 0 (map f (Zrange lo (lo+1))) = f lo.
Proof. intros. rewrite P073Range_cons__pull_merge by lia.
  rewrite P073Range_empty__pull_merge by lia. lia. Qed.
Lemma P073Suffix_cons__pull_merge : forall b x xs,
  P073Suffix b (x::xs) = P073Suffix b xs + P073Indicator (P073AllOn b (x::xs)).
Proof.
  intros. unfold P073Suffix. rewrite Zlength_cons.
  pose proof (Zlength_nonneg xs) as Hlen.
  rewrite P073Range_split__pull_merge with (mid:=Zlength xs+1) by lia.
  replace (Z.succ (Zlength xs)+1) with (Zlength xs+1+1) by lia.
  rewrite P073Range_single__pull_merge.
  replace (Z.succ (Zlength xs)-(Zlength xs+1)) with 0 by lia.
  replace (Z.succ (Zlength xs)) with (Zlength (x::xs)) by (rewrite Zlength_cons; lia).
  rewrite sublist_self by reflexivity.
  f_equal. apply P073Range_ext__pull_merge. intros k Hk.
  rewrite sublist_cons2 by (rewrite ?Zlength_cons; lia).
  replace (Zlength (x::xs)-k-1) with (Zlength xs-k) by (rewrite Zlength_cons; lia).
  replace (Zlength (x::xs)-1) with (Zlength xs) by (rewrite Zlength_cons; lia).
  reflexivity.
Qed.
Lemma P073Count_cons__pull_merge : forall b x xs,
  P073Count b (x::xs) = P073Count b xs + P073Prefix b (x::xs).
Proof.
  intros. unfold P073Count at 1. rewrite Zlength_cons.
  pose proof (Zlength_nonneg xs) as Hlen.
  rewrite P073Range_cons__pull_merge by lia.
  replace (0+1) with 1 by lia.
  replace (Z.succ (Zlength xs)) with (Zlength xs+1) by lia.
  assert (HP : fold_right Z.add 0
      (map (fun r => P073Indicator (P073AllOn b (sublist 0 (r+1) (x::xs))))
        (Zrange 0 (Zlength xs+1))) = P073Prefix b (x::xs)).
  { unfold P073Prefix. rewrite Zlength_cons.
    replace (Z.succ (Zlength xs)+1) with ((Zlength xs+1)+1) by lia.
    rewrite <- (P073Range_shift__pull_merge 0 (Zlength xs+1) 1
      (fun k => P073Indicator (P073AllOn b (sublist 0 k (x::xs))))).
    reflexivity. }
  rewrite HP.
  replace 1 with (0+1) at 1 by lia.
  rewrite P073Range_shift__pull_merge.
  assert (HC : fold_right Z.add 0
    (map (fun l => fold_right Z.add 0
      (map (fun r => P073Indicator (P073AllOn b (sublist (l+1) (r+1) (x::xs))))
        (Zrange (l+1) (Zlength xs+1)))) (Zrange 0 (Zlength xs))) = P073Count b xs).
  { unfold P073Count. apply P073Range_ext__pull_merge. intros l Hl.
    rewrite P073Range_shift__pull_merge. apply P073Range_ext__pull_merge. intros r Hr.
    rewrite sublist_cons2 by (rewrite ?Zlength_cons; lia).
    replace (l+1-1) with l by lia. replace (r+1+1-1) with (r+1) by lia.
    reflexivity. }
  rewrite HC. lia.
Qed.
Lemma P073Prefix_bounds_full__pull_merge : forall b xs,
  0 <= P073Prefix b xs <= Zlength xs /\
  (P073Prefix b xs = Zlength xs <-> P073AllOn b xs = true).
Proof.
  intros b xs. induction xs as [|x xs [[Hlo Hhi] IH]].
  - change (0<=0<=0 /\ (0=0 <-> true=true)). intuition lia.
  - rewrite P073Prefix_cons__pull_merge, Zlength_cons.
    change (0 <= P073Indicator (Z.testbit x b)*(1+P073Prefix b xs) <= Z.succ (Zlength xs) /\
      (P073Indicator (Z.testbit x b)*(1+P073Prefix b xs)=Z.succ (Zlength xs) <->
       andb (Z.testbit x b) (P073AllOn b xs)=true)).
    pose proof (Zlength_nonneg xs) as Hlength.
    destruct (Z.testbit x b); unfold P073Indicator; simpl andb;
      split; try lia; split; intro H; try discriminate; try lia.
    + apply IH; lia.
    + apply IH in H; lia.
Qed.
Lemma P073Suffix_bounds_full__pull_merge : forall b xs,
  0 <= P073Suffix b xs <= Zlength xs /\
  (P073Suffix b xs = Zlength xs <-> P073AllOn b xs = true).
Proof.
  intros b xs. induction xs as [|x xs [[Hlo Hhi] IH]].
  - change (0<=0<=0 /\ (0=0 <-> true=true)). intuition lia.
  - rewrite P073Suffix_cons__pull_merge, Zlength_cons.
    change (0 <= P073Suffix b xs + P073Indicator (andb (Z.testbit x b) (P073AllOn b xs)) <= Z.succ (Zlength xs) /\
      (P073Suffix b xs + P073Indicator (andb (Z.testbit x b) (P073AllOn b xs)) = Z.succ (Zlength xs) <->
       andb (Z.testbit x b) (P073AllOn b xs)=true)).
    destruct (Z.testbit x b), (P073AllOn b xs); unfold P073Indicator;
      simpl andb in *; split; try lia; split; intro H; try discriminate; try lia.
Qed.
Lemma P073Prefix_concat__pull_merge : forall b xs ys,
  P073Prefix b (xs++ys) = P073Prefix b xs + P073Indicator (P073AllOn b xs)*P073Prefix b ys.
Proof.
  intros b xs ys. induction xs as [|x xs IH].
  - change (P073Prefix b ys=0+1*P073Prefix b ys). ring.
  - change (P073Prefix b (x::(xs++ys)) = P073Prefix b (x::xs)+P073Indicator (P073AllOn b (x::xs))*P073Prefix b ys).
    rewrite !P073Prefix_cons__pull_merge, IH.
    change (P073Indicator (Z.testbit x b)*(1+(P073Prefix b xs+P073Indicator (P073AllOn b xs)*P073Prefix b ys)) =
      P073Indicator (Z.testbit x b)*(1+P073Prefix b xs)+P073Indicator (andb (Z.testbit x b) (P073AllOn b xs))*P073Prefix b ys).
    rewrite P073Indicator_and__pull_merge. ring.
Qed.
Lemma P073Suffix_concat__pull_merge : forall b xs ys,
  P073Suffix b (xs++ys) = P073Suffix b ys + P073Indicator (P073AllOn b ys)*P073Suffix b xs.
Proof.
  intros b xs ys. induction xs as [|x xs IH].
  - change (P073Suffix b ys=P073Suffix b ys+P073Indicator (P073AllOn b ys)*0). ring.
  - change (P073Suffix b (x::(xs++ys)) = P073Suffix b ys+P073Indicator (P073AllOn b ys)*P073Suffix b (x::xs)).
    rewrite !P073Suffix_cons__pull_merge, IH.
    change (P073Suffix b ys+P073Indicator (P073AllOn b ys)*P073Suffix b xs+
      P073Indicator (P073AllOn b ((x::xs)++ys)) =
      P073Suffix b ys+P073Indicator (P073AllOn b ys)*(P073Suffix b xs+P073Indicator (P073AllOn b (x::xs)))).
    rewrite P073AllOn_app, P073Indicator_and__pull_merge. ring.
Qed.
Lemma P073Count_concat__pull_merge : forall b xs ys,
  P073Count b (xs++ys) = P073Count b xs+P073Count b ys+P073Suffix b xs*P073Prefix b ys.
Proof.
  intros b xs ys. induction xs as [|x xs IH].
  - change (P073Count b ys=0+P073Count b ys+0*P073Prefix b ys). ring.
  - change (P073Count b (x::(xs++ys)) = P073Count b (x::xs)+P073Count b ys+P073Suffix b (x::xs)*P073Prefix b ys).
    rewrite !P073Count_cons__pull_merge, IH, P073Suffix_cons__pull_merge.
    change (P073Prefix b (x::(xs++ys))) with (P073Prefix b ((x::xs)++ys)).
    rewrite P073Prefix_concat__pull_merge. ring.
Qed.
Lemma P073Count_bounds__pull_merge : forall b xs,
  0<=P073Count b xs /\ 2*P073Count b xs<=Zlength xs*(Zlength xs+1) /\
  P073Prefix b xs<=P073Count b xs /\ P073Suffix b xs<=P073Count b xs.
Proof.
  intros b xs. induction xs as [|x xs IH].
  - change (0<=0 /\ 2*0<=0*(0+1) /\ 0<=0 /\ 0<=0). lia.
  - pose proof (P073Prefix_bounds_full__pull_merge b (x::xs)) as [HP Hfull].
    pose proof (Zlength_nonneg xs) as Hlen.
    rewrite P073Count_cons__pull_merge.
    rewrite Zlength_cons in HP |- *.
    rewrite P073Suffix_cons__pull_merge.
    destruct (P073AllOn b (x::xs)) eqn:Hbit; unfold P073Indicator;
      repeat split; try nia.
    pose proof (proj2 Hfull eq_refl) as Hpf. rewrite Zlength_cons in Hpf. nia.
Qed.
Lemma P073Summary_concat__pull_merge : forall b xs ys pl sl cl pr sr cr p s,
  P073Summary b xs pl sl cl -> P073Summary b ys pr sr cr ->
  ((pl=Zlength xs /\ p=pl+pr) \/ (pl<>Zlength xs /\ p=pl)) ->
  ((sr=Zlength ys /\ s=sr+sl) \/ (sr<>Zlength ys /\ s=sr)) ->
  P073Summary b (xs++ys) p s (cl+cr+sl*pr).
Proof.
  intros b xs ys pl sl cl pr sr cr p s [Hp [Hs Hc]] [Hpr [Hsr Hcr]] Hpb Hsb.
  subst pl sl cl pr sr cr. unfold P073Summary.
  rewrite P073Prefix_concat__pull_merge, P073Suffix_concat__pull_merge, P073Count_concat__pull_merge.
  pose proof (proj2 (P073Prefix_bounds_full__pull_merge b xs)) as Hpf.
  pose proof (proj2 (P073Suffix_bounds_full__pull_merge b ys)) as Hsf.
  destruct (P073AllOn b xs), (P073AllOn b ys); unfold P073Indicator;
    destruct Hpb as [[Hpl Hp]|[Hpl Hp]], Hsb as [[Hsr Hs]|[Hsr Hs]];
    intuition lia.
Qed.
Lemma P073Summary_nonzero_child__pull_merge : forall b xs ys,
  0 < Zlength xs -> 0 < Zlength ys ->
  (P073Prefix b (xs++ys)<>0 -> P073Prefix b xs<>0) /\
  (P073Suffix b (xs++ys)<>0 -> P073Suffix b ys<>0) /\
  (P073Count b (xs++ys)<>0 -> P073Count b xs<>0 \/ P073Count b ys<>0).
Proof.
  intros b xs ys Hxs Hys.
  pose proof (P073Prefix_bounds_full__pull_merge b xs) as [HP HF].
  pose proof (P073Suffix_bounds_full__pull_merge b ys) as [HS HG].
  pose proof (P073Count_bounds__pull_merge b xs) as HC.
  pose proof (P073Count_bounds__pull_merge b ys) as HD.
  pose proof (proj1 (P073Suffix_bounds_full__pull_merge b xs)) as Hsx.
  pose proof (proj1 (P073Prefix_bounds_full__pull_merge b ys)) as Hpy.
  rewrite P073Prefix_concat__pull_merge, P073Suffix_concat__pull_merge, P073Count_concat__pull_merge.
  split.
  - destruct (P073AllOn b xs); unfold P073Indicator; intuition nia.
  - split.
    + destruct (P073AllOn b ys); unfold P073Indicator; intuition nia.
    + destruct (Z.eq_dec (P073Count b xs) 0), (Z.eq_dec (P073Count b ys) 0); intuition nia.
Qed.
Lemma P073Znth_out__pull_merge : forall (xs:list Z) i,
  Zlength xs <= i -> Znth i xs 0=0.
Proof.
  intros. unfold Znth. apply nth_overflow. rewrite Zlength_correct in H. lia.
Qed.
Lemma P073Znth_nonzero__pull_merge : forall (xs:list Z) i,
  Znth i xs 0<>0 -> i<Zlength xs.
Proof.
  intros. destruct (Z_lt_ge_dec i (Zlength xs)); auto.
  rewrite P073Znth_out__pull_merge in H by lia. contradiction.
Qed.
Lemma P073Replace_observed__pull_merge : forall (xs:list Z) i x,
  0<=i -> (x<>0 -> i<Zlength xs) -> Znth i (replace_Znth i x xs) 0=x.
Proof.
  intros xs i x Hi Hobs. destruct (Z_lt_ge_dec i (Zlength xs)).
  - apply Znth_replace_Znth_Same. lia.
  - rewrite replace_Znth_nothing by lia. rewrite P073Znth_out__pull_merge by lia.
    destruct (Z.eq_dec x 0); intuition lia.
Qed.
Lemma P073Replace_bound__pull_merge : forall (xs:list Z) i k x m,
  0<=i -> 0<=k -> 0<=x<=m -> 0<=Znth k xs 0<=m ->
  0<=Znth k (replace_Znth i x xs) 0<=m.
Proof.
  intros. destruct (Z.eq_dec i k); subst.
  - destruct (Z_lt_ge_dec k (Zlength xs)).
    + rewrite Znth_replace_Znth_Same by lia. assumption.
    + rewrite replace_Znth_nothing by lia. assumption.
  - rewrite P073Packed_replace__pull_merge by lia. assumption.
Qed.
Lemma P073Buffer_replace__pull_merge : forall n pr su ct ln i b xs p s c,
  0<=i -> 0<=n -> Zlength xs<=n ->
  P073BufferBounds n pr su ct ln -> P073Summary b xs p s c ->
  P073BufferBounds n (replace_Znth i p pr) (replace_Znth i s su) (replace_Znth i c ct) ln.
Proof.
  intros n pr su ct ln i b xs p s c Hi Hn Hlen [Hbuf Hln] [Hp [Hs Hc]].
  pose proof (proj1 (P073Prefix_bounds_full__pull_merge b xs)) as Hpb.
  pose proof (proj1 (P073Suffix_bounds_full__pull_merge b xs)) as Hsb.
  pose proof (P073Count_bounds__pull_merge b xs) as Hcb.
  pose proof (Zlength_nonneg xs) as Hnon.
  assert (Hbound : 0<=c<=n*(n+1)/2).
  { split; [lia|apply Z.div_le_lower_bound; nia]. }
  split; [|assumption]. intros k Hk. specialize (Hbuf k Hk).
  split; [apply P073Replace_bound__pull_merge; intuition lia|].
  split; apply P073Replace_bound__pull_merge; intuition lia.
Qed.
Lemma P073Node_extend__pull_merge : forall n v b xs ys pr su ct p s c,
  0<n -> 0<v -> 2*v+1<4*n -> 0<=b<17 ->
  0<Zlength xs -> 0<Zlength ys ->
  P073NodePrefix n (2*v) 17 xs pr su ct ->
  P073NodePrefix n (2*v+1) 17 ys pr su ct ->
  P073NodePrefix n v b (xs++ys) pr su ct ->
  P073Summary b (xs++ys) p s c ->
  P073NodePrefix n v (b+1) (xs++ys)
    (replace_Znth (b*4*n+v) p pr)
    (replace_Znth (b*4*n+v) s su)
    (replace_Znth (b*4*n+v) c ct).
Proof.
  intros n v b xs ys pr su ct p s c Hn Hv Hvr Hb Hxs Hys HL HR Hold Hnew.
  intros d Hd. destruct (Z.eq_dec d b) as [Heq|Hne].
  - subst d. destruct Hnew as [Hp [Hs Hc]].
    pose proof (HL b Hb) as [Hpl [Hsl Hcl]].
    pose proof (HR b Hb) as [Hpr [Hsr Hcr]].
    destruct (P073Summary_nonzero_child__pull_merge b xs ys Hxs Hys) as [Hpn [Hsn Hcn]].
    unfold P073Summary.
    assert (Hpi : p<>0 -> b*4*n+v < Zlength pr).
    { intros H. rewrite Hp in H. apply Hpn in H.
      rewrite <- Hpl in H. apply P073Znth_nonzero__pull_merge in H. nia. }
    assert (Hsi : s<>0 -> b*4*n+v < Zlength su).
    { intros H. rewrite Hs in H. apply Hsn in H.
      rewrite <- Hsr in H. apply P073Znth_nonzero__pull_merge in H. nia. }
    assert (Hci : c<>0 -> b*4*n+v < Zlength ct).
    { intros H. rewrite Hc in H. apply Hcn in H. destruct H as [H|H].
      - rewrite <- Hcl in H. apply P073Znth_nonzero__pull_merge in H. nia.
      - rewrite <- Hcr in H. apply P073Znth_nonzero__pull_merge in H. nia. }
    rewrite !P073Replace_observed__pull_merge by (try assumption; nia).
    auto.
  - assert (Hidx : b*4*n+v <> d*4*n+v).
    { intro H. apply P073Packed_injective__pull_merge in H; lia. }
    unfold P073Summary. rewrite !P073Packed_replace__pull_merge by nia.
    apply Hold. lia.
Qed.
Lemma P073Singleton_summary__build_leaf : forall b x,
  P073Summary b (x :: nil) (P073Indicator (Z.testbit x b))
    (P073Indicator (Z.testbit x b)) (P073Indicator (Z.testbit x b)).
Proof.
  intros b x.
  unfold P073Summary, P073Prefix, P073Suffix, P073Count, P073AllOn.
  rewrite Zlength_cons, Zlength_nil.
  cbn [Zrange Zrange_aux].
  change (P073Indicator (Z.testbit x b) = P073Indicator (andb (Z.testbit x b) true) + 0 /\
    P073Indicator (Z.testbit x b) = P073Indicator (andb (Z.testbit x b) true) + 0 /\
    P073Indicator (Z.testbit x b) = (P073Indicator (andb (Z.testbit x b) true) + 0) + 0).
  destruct (Z.testbit x b); repeat split; reflexivity.
Qed.
Lemma P073Bit_guard__build_leaf : forall x b,
  Z.land (Z.shiftr x b) 1 = P073Indicator (Z.testbit x b).
Proof.
  intros x b.
  replace 1 with (Z.ones 1) at 1 by reflexivity.
  rewrite Z.land_ones by lia.
  change ((Z.shiftr x b) mod 2 = P073Indicator (Z.testbit x b)).
  rewrite <- Z.bit0_mod, Z.shiftr_spec by lia.
  simpl. destruct (Z.testbit x b); reflexivity.
Qed.
Lemma P073Written_bounds__build_leaf : forall n i pr su ct ln,
  1 <= n -> 0 <= i < 68*n ->
  Zlength pr = 68*n -> Zlength su = 68*n -> Zlength ct = 68*n ->
  P073BufferBounds n pr su ct ln ->
  P073BufferBounds n (replace_Znth i 1 pr) (replace_Znth i 1 su)
    (replace_Znth i 1 ct) ln.
Proof.
  intros n i pr su ct ln Hn Hi Hpr Hsu Hct [Hbits Hln].
  split; [|exact Hln]. intros k Hk.
  destruct (Z.eq_dec k i) as [->|Hne].
  - repeat rewrite Znth_replace_Znth_Same by lia.
    assert (1 <= n*(n+1)/2) by (apply Z.div_le_lower_bound; nia).
    repeat split; lia.
  - repeat rewrite Znth_replace_Znth_Diff by lia. apply Hbits; exact Hk.
Qed.
Lemma P073Leaf_frame__build_leaf : forall n v b oldpr oldsu oldct pr su ct,
  1 <= n -> 0 <= v < 4*n -> 0 <= b < 17 ->
  Zlength pr = 68*n -> Zlength su = 68*n -> Zlength ct = 68*n ->
  P073NodeFrame n v b oldpr oldsu oldct pr su ct ->
  P073NodeFrame n v (b+1) oldpr oldsu oldct
    (replace_Znth (b*4*n+v) 1 pr) (replace_Znth (b*4*n+v) 1 su)
    (replace_Znth (b*4*n+v) 1 ct).
Proof.
  intros n v b oldpr oldsu oldct pr su ct Hn Hv Hb Hp Hs Hc Hframe.
  intros j w Hj Hw Hcond.
  assert (Hdiff: b*4*n+v <> j*4*n+w).
  { destruct (Z.lt_trichotomy b j) as [Hlt|[Heq|Hgt]]; [nia|subst j|nia].
    destruct Hcond; lia. }
  repeat rewrite Znth_replace_Znth_Diff by nia.
  apply Hframe; try assumption.
  destruct Hcond; [left|right]; lia.
Qed.
Lemma P073Written_prefix__build_leaf : forall n v b xs pr su ct,
  1 <= n -> 0 <= v < 4*n -> 0 <= b < 17 ->
  Zlength pr = 68*n -> Zlength su = 68*n -> Zlength ct = 68*n ->
  P073Summary b xs 1 1 1 -> P073NodePrefix n v b xs pr su ct ->
  P073NodePrefix n v (b+1) xs (replace_Znth (b*4*n+v) 1 pr)
    (replace_Znth (b*4*n+v) 1 su) (replace_Znth (b*4*n+v) 1 ct).
Proof.
  intros n v b xs pr su ct Hn Hv Hb Hp Hs Hc Hsummary Hprefix.
  intros j Hj. destruct (Z.eq_dec j b) as [->|Hne].
  - repeat rewrite Znth_replace_Znth_Same by nia. exact Hsummary.
  - repeat rewrite Znth_replace_Znth_Diff by nia. apply Hprefix; lia.
Qed.
Lemma P073Replace_length__update_leaf : forall (xs : list Z) i x,
  Zlength (replace_Znth i x xs) = Zlength xs.
Proof.
  intros xs i x. unfold replace_Znth. generalize (Z.to_nat i).
  induction xs; intros [|k]; simpl; auto; rewrite !Zlength_cons; rewrite IHxs; reflexivity.
Qed.
Lemma P073Singleton_update__update_leaf : forall (xs : list Z) l x,
  0 <= l < Zlength xs ->
  sublist l (l+1) (replace_Znth l x xs) = x :: nil.
Proof.
  intros xs l x Hl.
  rewrite (sublist_single 0); [|rewrite P073Replace_length__update_leaf; exact Hl].
  rewrite Znth_replace_Znth_Same by exact Hl. reflexivity.
Qed.
Lemma P073Singleton_summary__update_leaf : forall b x,
  P073Summary b (x :: nil) (P073Indicator (Z.testbit x b))
    (P073Indicator (Z.testbit x b)) (P073Indicator (Z.testbit x b)).
Proof.
  intros b x.
  unfold P073Summary, P073Prefix, P073Suffix, P073Count,
    P073AllOn, P073Indicator.
  cbn [Zrange Zrange_aux Zlength Z.to_nat Pos.to_nat Pos.iter sublist].
  simpl. destruct (Z.testbit x b); repeat split; reflexivity.
Qed.
Lemma P073Bit_extract__update_leaf : forall x b, 0 <= b ->
  Z.land (Z.shiftr x b) 1 = P073Indicator (Z.testbit x b).
Proof.
  intros x b Hb. change 1 with (Z.ones 1) at 1.
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  change ((x / 2^b) mod 2 = P073Indicator (Z.testbit x b)).
  rewrite <- Z.testbit_spec' by exact Hb.
  unfold P073Indicator. destruct (Z.testbit x b); reflexivity.
Qed.
Lemma P073Leaf_frame__update_leaf : forall n b w b' w',
  0 < n -> 0 <= w < 4*n -> 0 <= w' < 4*n ->
  b*4*n+w = b'*4*n+w' -> b=b' /\ w=w'.
Proof. intros. assert (b=b') by nia. subst. split; nia. Qed.
Lemma P073Packed_bound__update_leaf : forall n b w,
  0 < n -> 0 <= b < 17 -> 0 <= w < 4*n ->
  0 <= b*4*n+w < 68*n.
Proof. intros; nia. Qed.
Lemma P073Prefix_write__update_leaf : forall n v b x xs pr su ct,
  0 < n -> 0 <= v < 4*n -> 0 <= b < 17 ->
  Zlength pr=68*n -> Zlength su=68*n -> Zlength ct=68*n ->
  P073NodePrefix n v b xs pr su ct ->
  P073Summary b xs x x x ->
  P073NodePrefix n v (b+1) xs
    (replace_Znth (b*4*n+v) x pr)
    (replace_Znth (b*4*n+v) x su)
    (replace_Znth (b*4*n+v) x ct).
Proof.
  intros n v b x xs pr su ct Hn Hv Hb Hp Hs Hc Hprefix Hsummary.
  intros i Hi. destruct (Z.eq_dec i b) as [->|Hne].
  - rewrite !Znth_replace_Znth_Same; try rewrite Hp; try rewrite Hs; try rewrite Hc;
      try (apply P073Packed_bound__update_leaf; lia). exact Hsummary.
  - rewrite !Znth_replace_Znth_Diff; try rewrite Hp; try rewrite Hs; try rewrite Hc;
      try (apply P073Packed_bound__update_leaf; lia); try nia.
    apply Hprefix. lia.
Qed.
Lemma P073Frame_write__update_leaf : forall n v b x opr osu oct pr su ct,
  0 < n -> 0 <= v < 4*n -> 0 <= b < 17 ->
  Zlength pr=68*n -> Zlength su=68*n -> Zlength ct=68*n ->
  P073NodeFrame n v b opr osu oct pr su ct ->
  P073NodeFrame n v (b+1) opr osu oct
    (replace_Znth (b*4*n+v) x pr)
    (replace_Znth (b*4*n+v) x su)
    (replace_Znth (b*4*n+v) x ct).
Proof.
  intros n v b x opr osu oct pr su ct Hn Hv Hb Hp Hs Hc Hframe.
  intros i w Hi Hw Houtside.
  assert (Hne : b*4*n+v <> i*4*n+w).
  { intro E. pose proof (P073Leaf_frame__update_leaf n b v i w Hn Hv Hw E).
    destruct Houtside; lia. }
  rewrite !Znth_replace_Znth_Diff; try rewrite Hp; try rewrite Hs; try rewrite Hc;
    try (apply P073Packed_bound__update_leaf; lia); auto.
  apply Hframe; auto. destruct Houtside; [left|right]; lia.
Qed.
Lemma P073Bounds_write__update_leaf : forall n k x pr su ct ln,
  1 <= n -> 0 <= k < 68*n -> 0 <= x <= 1 ->
  Zlength pr=68*n -> Zlength su=68*n -> Zlength ct=68*n ->
  P073BufferBounds n pr su ct ln ->
  P073BufferBounds n (replace_Znth k x pr) (replace_Znth k x su)
    (replace_Znth k x ct) ln.
Proof.
  intros n k x pr su ct ln Hn Hk Hx Hp Hs Hc [Hbuf Hln].
  split; [|exact Hln]. intros i Hi.
  destruct (Z.eq_dec i k) as [->|Hne].
  - rewrite !Znth_replace_Znth_Same; try rewrite Hp; try rewrite Hs; try rewrite Hc; auto.
    assert (1 <= n*(n+1)/2).
    { apply Z.div_le_lower_bound; nia. }
    repeat split; lia.
  - rewrite !Znth_replace_Znth_Diff; try rewrite Hp; try rewrite Hs; try rewrite Hc;
      auto; try lia.
Qed.
Lemma P073Mid_bounds__update_routing : forall l r,
  0 <= l -> r-l > 1 ->
  Z.quot (l+r) 2 = (l+r)/2 /\ l < (l+r)/2 < r.
Proof.
  intros l r Hl Hlen.
  split.
  - apply Z.quot_div_nonneg; lia.
  - pose proof (Z.div_mod (l+r) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)).
    lia.
Qed.
Lemma P073Replace_length__update_pull_input : forall (xs : list Z) p x,
  Zlength (replace_Znth p x xs) = Zlength xs.
Proof.
  induction xs as [|a xs IH]; intros p x.
  - reflexivity.
  - unfold replace_Znth in *; destruct (Z.to_nat p) as [|k]; simpl.
    + rewrite !Zlength_cons. reflexivity.
    + rewrite !Zlength_cons.
      specialize (IH (Z.of_nat k) x).
      rewrite Nat2Z.id in IH. now rewrite IH.
Qed.
Lemma P073Desc_domains__update_pull_input : forall v l r w lo hi,
  P073Desc v l r w lo hi -> 0 < v -> v <= w.
Proof.
  intros v l r w lo hi H; induction H; intros Hv; lia.
Qed.
Lemma P073Sibling_exclusion__update_pull_input : forall v l m r,
  0 < v ->
  (forall lo hi, ~ P073Desc (2*v) l m (2*v+1) lo hi) /\
  (forall lo hi, ~ P073Desc (2*v+1) m r (2*v) lo hi).
Proof.
  intros v l m r Hv; split; intros lo hi H.
  - inversion H; subst; try lia;
      match goal with
      | HD : P073Desc _ _ _ _ _ _ |- _ =>
          pose proof (P073Desc_domains__update_pull_input _ _ _ _ _ _ HD ltac:(lia)); lia
      end.
  - pose proof (P073Desc_domains__update_pull_input _ _ _ _ _ _ H ltac:(lia)); lia.
Qed.
Lemma P073Sublist_update_outside__update_pull_input : forall (xs : list Z) p x lo hi,
  0 <= p < Zlength xs -> 0 <= lo <= hi -> hi <= Zlength xs ->
  (p < lo \/ hi <= p) ->
  sublist lo hi (replace_Znth p x xs) = sublist lo hi xs.
Proof.
  intros xs p x lo hi Hp Hlo Hhi Hout.
  pose proof (P073Replace_length__update_pull_input xs p x) as Hlen.
  apply (list_eq_ext _ _ 0). split.
  - rewrite !Zlength_sublist by lia. reflexivity.
  - intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite !Znth_sublist by lia.
    apply Znth_replace_Znth_Diff; lia.
Qed.
Lemma P073Midpoint__update_pull_input : forall l r,
  0 <= l -> 1 < r-l -> l < (l+r)/2 < r.
Proof.
  intros l r Hl Hr.
  pose proof (Z.div_mod (l+r) 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)). lia.
Qed.
Lemma P073Desc_domains__update_merge : forall v l r w lo hi,
  P073Desc v l r w lo hi -> 0 < v -> l < r ->
  v <= w /\ l <= lo /\ lo < hi /\ hi <= r.
Proof.
  intros v l r w lo hi HD; induction HD; intros Hv Hlr.
  - repeat split; lia.
  - assert (Hm : l < (l+r)/2 < r).
    { pose proof (Z.div_mod (l+r) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)). lia. }
    specialize (IHHD ltac:(lia) ltac:(lia)). lia.
  - assert (Hm : l < (l+r)/2 < r).
    { pose proof (Z.div_mod (l+r) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)). lia. }
    specialize (IHHD ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma P073Desc_heap_interval__update_merge : forall v l r w lo hi,
  P073Desc v l r w lo hi -> 0 < v ->
  exists k : Z, 0 <= k /\ 2^k*v <= w < 2^k*(v+1).
Proof.
  intros v l r w lo hi HD; induction HD; intros Hv.
  - exists 0; rewrite Z.pow_0_r; lia.
  - destruct (IHHD ltac:(lia)) as [k [Hk Hw]].
    exists (k+1). rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
    split; nia.
  - destruct (IHHD ltac:(lia)) as [k [Hk Hw]].
    exists (k+1). rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
    split; nia.
Qed.
Lemma P073Desc_siblings__update_merge : forall v l m r w lo hi lo' hi',
  0 < v ->
  P073Desc (2*v) l m w lo hi ->
  P073Desc (2*v+1) m r w lo' hi' -> False.
Proof.
  intros v l m r w lo hi lo' hi' Hv HL HR.
  destruct (P073Desc_heap_interval__update_merge _ _ _ _ _ _ HL ltac:(lia))
    as [k [Hk Hkw]].
  destruct (P073Desc_heap_interval__update_merge _ _ _ _ _ _ HR ltac:(lia))
    as [j [Hj Hjw]].
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hkp.
  pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj) as Hjp.
  destruct (Z.lt_trichotomy k j) as [Hlt|[Heq|Hgt]].
  - assert (Hpow : 2^(k+1) <= 2^j) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.pow_add_r, Z.pow_1_r in Hpow by lia. nia.
  - subst j. nia.
  - assert (Hpow : 2^(j+1) <= 2^k) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.pow_add_r, Z.pow_1_r in Hpow by lia. nia.
Qed.
Lemma P073Replace_length__update_merge : forall (xs : list Z) p x,
  Zlength (replace_Znth p x xs) = Zlength xs.
Proof.
  intros xs p x. unfold replace_Znth. rewrite !Zlength_correct. f_equal.
  generalize (Z.to_nat p). induction xs as [|a xs IH]; intros [|k]; simpl;
    try reflexivity; now rewrite IH.
Qed.
Lemma P073Replace_slice_nat__update_merge : forall (xs : list Z) p x lo hi,
  (p < lo \/ hi <= p)%nat ->
  skipn lo (firstn hi (replace_nth p xs x)) = skipn lo (firstn hi xs).
Proof.
  induction xs as [|a xs IH]; intros [|p] x [|lo] [|hi] H;
    simpl in *; try reflexivity; try lia;
    try (f_equal; apply (IH p x 0%nat hi); lia); apply IH; lia.
Qed.
Lemma P073Replace_slice__update_merge : forall (xs : list Z) p x lo hi,
  0 <= p -> 0 <= lo -> 0 <= hi -> (p < lo \/ hi <= p) ->
  sublist lo hi (replace_Znth p x xs) = sublist lo hi xs.
Proof.
  intros. unfold sublist, replace_Znth.
  apply P073Replace_slice_nat__update_merge. lia.
Qed.
Lemma P073Updated_parent__update_merge :
  forall n v l r xs pr su ct ln pr' su' ct',
  0 < v -> l < r -> P073Layout n v l r ->
  Znth v ln 0 = r-l ->
  P073Tree n (2*v) l ((l+r)/2) xs pr su ct ln ->
  P073Tree n (2*v+1) ((l+r)/2) r xs pr su ct ln ->
  P073NodePrefix n v 17 (sublist l r xs) pr' su' ct' ->
  P073NodeFrame n v 17 pr su ct pr' su' ct' ->
  P073Tree n v l r xs pr' su' ct' ln.
Proof.
  intros n v l r xs pr su ct ln pr' su' ct' Hv Hlr HL Hlen Hleft Hright Hroot HF.
  intros w lo hi HD.
  pose proof (HL w lo hi HD) as Hbounds.
  inversion HD; subst.
  - split; auto.
  - assert (Hm : l < (l+r)/2 < r).
    { pose proof (Z.div_mod (l+r) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)). lia. }
    match goal with H : P073Desc (2*v) _ _ _ _ _ |- _ =>
      pose proof (P073Desc_domains__update_merge _ _ _ _ _ _ H ltac:(lia) ltac:(lia)) as Hdomain;
      destruct (Hleft _ _ _ H) as [Hlength Hsummary]
    end.
    split; auto. intros b Hb.
    destruct (HF b w Hb ltac:(lia) ltac:(left; lia)) as [Hp [Hs Hc]].
    rewrite Hp, Hs, Hc. apply Hsummary; auto.
  - assert (Hm : l < (l+r)/2 < r).
    { pose proof (Z.div_mod (l+r) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)). lia. }
    match goal with H : P073Desc (2*v+1) _ _ _ _ _ |- _ =>
      pose proof (P073Desc_domains__update_merge _ _ _ _ _ _ H ltac:(lia) ltac:(lia)) as Hdomain;
      destruct (Hright _ _ _ H) as [Hlength Hsummary]
    end.
    split; auto. intros b Hb.
    destruct (HF b w Hb ltac:(lia) ltac:(left; lia)) as [Hp [Hs Hc]].
    rewrite Hp, Hs, Hc. apply Hsummary; auto.
Qed.
Lemma P073Unchanged_child__update_merge : forall n v l r u a c p x xs pr su ct ln pr' su' ct',
  0 < v -> l < r -> 0 <= p ->
  P073Layout n v l r ->
  (p < l \/ r <= p) ->
  (forall w lo hi lo' hi', P073Desc v l r w lo hi ->
    P073Desc u a c w lo' hi' -> False) ->
  P073Tree n v l r xs pr su ct ln ->
  P073OutsideTree n u a c pr su ct ln pr' su' ct' ln ->
  P073Tree n v l r (replace_Znth p x xs) pr' su' ct' ln.
Proof.
  intros n v l r u a c p x xs pr su ct ln pr' su' ct'
    Hv Hlr Hp HL Houtside Hdisjoint HT [_ HF] w lo hi HD.
  pose proof (HL _ _ _ HD) as Hbounds.
  pose proof (P073Desc_domains__update_merge _ _ _ _ _ _ HD Hv Hlr) as Hdomain.
  destruct (HT _ _ _ HD) as [Hlen Hsum]. split; auto.
  intros b Hb.
  destruct (HF w b ltac:(lia) Hb ltac:(intros lo' hi' HD'; eapply Hdisjoint; eauto))
    as [Hpr [Hsu Hct]].
  rewrite Hpr, Hsu, Hct.
  rewrite P073Replace_slice__update_merge by lia.
  apply Hsum; auto.
Qed.
Lemma P073Outside_parent__update_merge : forall n v l r u a c pr su ct ln pr' su' ct' pr'' su'' ct'',
  (forall w lo hi, P073Desc u a c w lo hi -> P073Desc v l r w lo hi) ->
  P073OutsideTree n u a c pr su ct ln pr' su' ct' ln ->
  P073NodeFrame n v 17 pr' su' ct' pr'' su'' ct'' ->
  P073OutsideTree n v l r pr su ct ln pr'' su'' ct'' ln.
Proof.
  intros n v l r u a c pr su ct ln pr' su' ct' pr'' su'' ct'' Hin [_ HO] HF.
  split; [reflexivity|]. intros w b Hw Hb Houtside.
  assert (Hneq : w <> v) by (intro; subst; apply (Houtside l r); constructor).
  destruct (HF b w Hb Hw (or_introl Hneq)) as [Hpr [Hsu Hct]].
  rewrite Hpr, Hsu, Hct. apply HO; auto.
  intros lo hi HD. apply (Houtside lo hi). apply Hin; auto.
Qed.
Lemma P073Desc_power_bound__solver_layout : forall (k : nat) v l r w lo hi,
  0 < v -> 0 <= l < r -> r-l <= 2^(Z.of_nat k) ->
  P073Desc v l r w lo hi ->
  0 < w < (v+1)*2^(Z.of_nat k) /\ l <= lo < hi /\ hi <= r.
Proof.
  induction k as [|k IH]; intros v l r w lo hi Hv Hlr Hlen Hd.
  - cbn in Hlen |- *.
    inversion Hd; subst; lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hlen |- * by lia.
    assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
    inversion Hd as [|v' l' r' w' lo' hi' Hlong Hchild
                     |v' l' r' w' lo' hi' Hlong Hchild]; subst.
    + repeat split; nia.
    + pose proof (Z.div_mod (l+r) 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)) as Hmod.
      specialize (IH (2*v) l ((l+r)/2) w lo hi ltac:(lia)
        ltac:(lia) ltac:(nia) Hchild).
      destruct IH as [Hw [Hlo Hhi]]. repeat split; nia.
    + pose proof (Z.div_mod (l+r) 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound (l+r) 2 ltac:(lia)) as Hmod.
      specialize (IH (2*v+1) ((l+r)/2) r w lo hi ltac:(lia)
        ltac:(lia) ltac:(nia) Hchild).
      destruct IH as [Hw [Hlo Hhi]]. repeat split; nia.
Qed.
Lemma P073Root_layout__solver_layout : forall n,
  1 <= n -> P073Layout n 1 0 n.
Proof.
  intros n Hn w lo hi Hd.
  pose proof (Z.log2_log2_up_spec n ltac:(lia)) as Hpower.
  pose proof (Z.log2_up_nonneg n) as Hlog.
  assert (Hsmall : 2 ^ Z.log2_up n < 2*n).
  { destruct (Z.eq_dec n 1) as [->|Hne].
    - rewrite Z.log2_up_1. cbn. lia.
    - pose proof (Z.log2_up_spec n ltac:(lia)) as Hspec.
      pose proof (Z.log2_up_pos n ltac:(lia)) as Hpos.
      replace (Z.log2_up n) with (Z.succ (Z.pred (Z.log2_up n))) at 1 by lia.
      rewrite Z.pow_succ_r by lia. nia. }
  pose proof (P073Desc_power_bound__solver_layout (Z.to_nat (Z.log2_up n))
    1 0 n w lo hi ltac:(lia) ltac:(lia)) as Hbound.
  rewrite Z2Nat.id in Hbound by lia.
  specialize (Hbound ltac:(lia) Hd).
  unfold P073Layout. destruct Hbound as [Hw [Hlo Hhi]]. repeat split; lia.
Qed.
Lemma P073Zero_buffers__solver_layout : forall n,
  1 <= n ->
  P073BufferBounds n (repeat 0 (Z.to_nat (68*n)))
    (repeat 0 (Z.to_nat (68*n))) (repeat 0 (Z.to_nat (68*n)))
    (repeat 0 (Z.to_nat (4*n))) /\
  P073ZeroTree n 1 0 n (repeat 0 (Z.to_nat (68*n)))
    (repeat 0 (Z.to_nat (68*n))) (repeat 0 (Z.to_nat (68*n)))
    (repeat 0 (Z.to_nat (4*n))).
Proof.
  intros n Hn. split.
  - unfold P073BufferBounds. split; intros k Hk; rewrite !Znth_repeat.
    + assert (0 <= n*(n+1)/2) by (apply Z.div_pos; nia).
      repeat split; lia.
    + lia.
  - unfold P073ZeroTree. intros w lo hi Hd. rewrite Znth_repeat.
    split; [reflexivity|]. intros b Hb. rewrite !Znth_repeat. auto.
Qed.
Lemma P073Range_snoc__solver_weighted : forall b,
  0 <= b -> Zrange 0 (b+1) = Zrange 0 b ++ (b :: nil).
Proof.
  intros b Hb. unfold Zrange. rewrite !Z.sub_0_r.
  rewrite Z2Nat.inj_add by lia.
  rewrite Zrange_aux_app. rewrite Z2Nat.id by lia.
  simpl. reflexivity.
Qed.
Lemma P073Weighted_step__solver_weighted : forall xs b,
  0 <= b -> P073Weighted xs (b+1) =
  P073Weighted xs b + P073Count b xs * 2^b.
Proof.
  intros xs b Hb. unfold P073Weighted.
  rewrite P073Range_snoc__solver_weighted by lia.
  rewrite map_app, fold_right_app. simpl.
  induction (map (fun b => P073Count b xs * 2^b) (Zrange 0 b)); simpl; lia.
Qed.
Lemma P073Weighted_step_bound__solver_weighted : forall xs b cap,
  0 <= b -> 0 <= cap ->
  (forall k, 0 <= k < b -> 0 <= P073Count k xs <= cap) ->
  0 <= P073Weighted xs b <= (2^b-1)*cap.
Proof.
  intros xs b cap Hb Hcap.
  replace b with (Z.of_nat (Z.to_nat b)) by (rewrite Z2Nat.id; lia).
  generalize (Z.to_nat b). intros nb. induction nb as [|nb IH].
  - intros _. unfold P073Weighted, Zrange. simpl. lia.
  - intros Hcounts. rewrite Nat2Z.inj_succ in *.
    replace (Z.succ (Z.of_nat nb)) with (Z.of_nat nb+1) in * by lia.
    rewrite P073Weighted_step__solver_weighted by lia.
    specialize (IH ltac:(intros j Hj; apply Hcounts; lia)).
    specialize (Hcounts (Z.of_nat nb) ltac:(lia)).
    rewrite Z.pow_add_r by lia. simpl.
    pose proof (Z.pow_nonneg 2 (Z.of_nat nb) ltac:(lia)). nia.
Qed.
Lemma P073Root_count__solver_weighted : forall n xs pr su ct ln b,
  Zlength xs = n -> 0 <= b < 17 ->
  P073Tree n 1 0 n xs pr su ct ln ->
  Znth (b*4*n+1) ct 0 = P073Count b xs.
Proof.
  intros n xs pr su ct ln b Hlen Hb Htree.
  specialize (Htree 1 0 n (P073Desc_here 1 0 n)).
  destruct Htree as [_ Htree]. specialize (Htree b Hb).
  assert (Hsub : sublist 0 n xs = xs) by (apply sublist_self; lia).
  unfold P073Summary in Htree. rewrite Hsub in Htree.
  tauto.
Qed.
Lemma P073TreeWeighted_bound__solver_weighted : forall n xs pr su ct ln b,
  1 <= n <= 100000 -> Zlength xs = n -> 0 <= b <= 17 ->
  P073Tree n 1 0 n xs pr su ct ln -> P073BufferBounds n pr su ct ln ->
  0 <= P073Weighted xs b <= 655361553550000.
Proof.
  intros n xs pr su ct ln b Hn Hlen Hb Htree [Hbounds _].
  assert (Hcap : 0 <= n*(n+1)/2 <= 5000050000).
  { pose proof (Z.div_mod (n*(n+1)) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound (n*(n+1)) 2 ltac:(lia)). nia. }
  pose proof (P073Weighted_step_bound__solver_weighted xs b (n*(n+1)/2)
    ltac:(lia) ltac:(lia)) as Hw.
  specialize (Hw ltac:(intros k Hk;
    rewrite <- (P073Root_count__solver_weighted n xs pr su ct ln k Hlen ltac:(lia) Htree);
    specialize (Hbounds (k*4*n+1) ltac:(nia)); tauto)).
  assert (Hp : 2^b <= 131072).
  { change (2^b <= 2^17). apply Z.pow_le_mono_r; lia. }
  nia.
Qed.
Lemma P073Shift17__solver_weighted : forall b,
  0 <= b <= 16 -> Z.shiftl 1 b = 2^b /\
  0 <= 2^b <= 65536.
Proof.
  intros b Hb. assert (Hp : 0 <= 2^b <= 65536).
  { split. apply Z.pow_nonneg; lia.
    change (2^b <= 2^16). apply Z.pow_le_mono_r; lia. }
  split; [|exact Hp]. rewrite Z.shiftl_mul_pow2 by lia.
  apply Z.mul_1_l.
Qed.
Lemma P073Sum_ext__solver_history {A} (xs : list A) (f g : A -> Z) :
  (forall x, In x xs -> f x = g x) ->
  fold_right Z.add 0 (map f xs) = fold_right Z.add 0 (map g xs).
Proof. intro H; f_equal; apply map_ext_in; exact H. Qed.
Lemma P073Sum_plus__solver_history {A} (xs : list A) (f g : A -> Z) :
  fold_right Z.add 0 (map (fun x => f x + g x) xs) =
  fold_right Z.add 0 (map f xs) + fold_right Z.add 0 (map g xs).
Proof. induction xs; simpl; [reflexivity | rewrite IHxs; ring]. Qed.
Lemma P073Sum_scale__solver_history {A} (xs : list A) (f : A -> Z) c :
  fold_right Z.add 0 (map f xs) * c =
  fold_right Z.add 0 (map (fun x => f x * c) xs).
Proof. induction xs; simpl; [ring | rewrite <- IHxs; ring]. Qed.
Lemma P073Sum_swap__solver_history {A B} (xs : list A) (ys : list B)
    (f : A -> B -> Z) :
  fold_right Z.add 0 (map (fun x => fold_right Z.add 0 (map (f x) ys)) xs) =
  fold_right Z.add 0 (map (fun y => fold_right Z.add 0 (map (fun x => f x y) xs)) ys).
Proof.
  induction xs as [|x xs IH]; simpl.
  - induction ys; simpl; auto.
  - rewrite P073Sum_plus__solver_history, <- IH; reflexivity.
Qed.
Lemma P073Bits_telescoping__solver_history z n : forall k, 0 <= k ->
  fold_right Z.add 0 (map (fun b => P073Indicator (Z.testbit z b) * 2^b)
    (Zrange_aux k n)) =
  z / 2^k * 2^k - z / 2^(k+Z.of_nat n) * 2^(k+Z.of_nat n).
Proof.
  induction n as [|n IH]; intros k Hk.
  - simpl; rewrite Z.add_0_r; ring.
  - cbn [Zrange_aux map fold_right]. rewrite IH by lia.
    assert (Hb : P073Indicator (Z.testbit z k) = (z / 2^k) mod 2).
    { change (Z.b2z (Z.testbit z k) = (z / 2^k) mod 2).
      apply Z.testbit_spec'; lia. }
    rewrite Hb, Nat2Z.inj_succ.
    replace (k + Z.succ (Z.of_nat n)) with (k + 1 + Z.of_nat n) by lia.
    assert (Hp : 2^(k+1) = 2^k * 2).
    { rewrite Z.pow_add_r by lia; rewrite Z.pow_1_r; reflexivity. }
    rewrite Hp.
    rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
    pose proof (Z.div_mod (z / 2^k) 2 ltac:(lia)); nia.
Qed.
Lemma P073Finite_bit_sum__solver_history z : 0 <= z < 2^17 ->
  z = fold_right Z.add 0
    (map (fun b => P073Indicator (Z.testbit z b) * 2^b) (Zrange 0 17)).
Proof.
  intros H. unfold Zrange.
  rewrite P073Bits_telescoping__solver_history by lia.
  change (z = z / 1 * 1 - z / 131072 * 131072).
  rewrite Z.div_1_r, Z.div_small by exact H. ring.
Qed.
Lemma P073Land_bound__solver_history x y : 0 <= x < 2^17 ->
  0 <= Z.land x y < 2^17.
Proof.
  intro Hx.
  assert (Hxmask : Z.land x (Z.ones 17) = x).
  { rewrite Z.land_ones by lia; apply Z.mod_small; exact Hx. }
  assert (Hm : Z.land (Z.land x y) (Z.ones 17) = Z.land x y).
  { rewrite <- Z.land_assoc, (Z.land_comm y (Z.ones 17)), Z.land_assoc, Hxmask.
    reflexivity. }
  rewrite Z.land_ones in Hm by lia.
  rewrite <- Hm. apply Z.mod_pos_bound. compute; reflexivity.
Qed.
Lemma P073Fold_bound__solver_history xs : forall acc,
  0 <= acc < 2^17 -> 0 <= fold_left Z.land xs acc < 2^17.
Proof.
  induction xs; simpl; intros acc H; auto.
  apply IHxs, P073Land_bound__solver_history; exact H.
Qed.
Lemma P073Interval_bound__solver_history xs l r :
  (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0 <= 100000) ->
  0 <= l <= r -> r < Zlength xs ->
  0 <= fold_left Z.land (sublist l (r+1) xs) (-1) < 2^17.
Proof.
  intros Hb Hlr Hr.
  assert (Hlen : Zlength (sublist l (r+1) xs) = r+1-l).
  { rewrite Zlength_sublist; lia. }
  assert (Hfirst : Znth 0 (sublist l (r+1) xs) 0 = Znth l xs 0).
  { rewrite Znth_sublist by lia. f_equal; lia. }
  destruct (sublist l (r+1) xs) as [|x tail] eqn:E.
  - rewrite Zlength_nil in Hlen. lia.
  - change (x = Znth l xs 0) in Hfirst.
    cbn [fold_left]. rewrite Z.land_m1_l.
    apply P073Fold_bound__solver_history. rewrite Hfirst.
    specialize (Hb l ltac:(lia)). change (0 <= Znth l xs 0 < 131072). lia.
Qed.
Lemma P073Flatten_sum__solver_history {A B} (xs : list A) (g : A -> list B) (f : B -> Z) :
  fold_right Z.add 0 (map f (concat (map g xs))) =
  fold_right Z.add 0 (map (fun x => fold_right Z.add 0 (map f (g x))) xs).
Proof.
  induction xs; simpl; auto.
  rewrite map_app, fold_right_app, IHxs.
  generalize (g a); intro ys; induction ys; simpl; [ring | rewrite IHys; ring].
Qed.
Lemma P073Weighted17_spec__solver_history xs :
  (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0 <= 100000) ->
  P073Weighted xs 17 = AndExerciseSum xs.
Proof.
  intro Hb. unfold P073Weighted, P073Count, AndExerciseSum, Zmap_range.
  rewrite P073Flatten_sum__solver_history.
  transitivity (fold_right Z.add 0
    (map (fun b => fold_right Z.add 0
      (map (fun l => fold_right Z.add 0
        (map (fun r => P073Indicator (P073AllOn b (sublist l (r+1) xs)) * 2^b)
          (Zrange l (Zlength xs)))) (Zrange 0 (Zlength xs)))) (Zrange 0 17))).
  - apply P073Sum_ext__solver_history; intros b _.
    rewrite P073Sum_scale__solver_history.
    apply P073Sum_ext__solver_history; intros l _.
    apply P073Sum_scale__solver_history.
  - rewrite P073Sum_swap__solver_history.
    apply P073Sum_ext__solver_history; intros l Hl.
    rewrite P073Sum_swap__solver_history, map_map.
    apply P073Sum_ext__solver_history; intros r Hr; cbn.
    symmetry. rewrite (P073Finite_bit_sum__solver_history
      (fold_left Z.land (sublist l (r+1) xs) (-1))) at 1.
    + apply P073Sum_ext__solver_history; intros b Hbit.
      change (In b (Zrange 0 17)) in Hbit.
      rewrite P073AllOn_fold_and.
      rewrite Z.bits_m1 by (apply In_Zrange in Hbit; lia).
      reflexivity.
    + apply P073Interval_bound__solver_history; auto;
        apply In_Zrange in Hl; apply In_Zrange in Hr; lia.
Qed.
Lemma P073Znth_snoc__solver_history {A} (xs : list A) x d :
  Znth (Zlength xs) (xs ++ x :: nil) d = x.
Proof. rewrite app_Znth2 by lia. rewrite Z.sub_diag. reflexivity. Qed.
Lemma P073History_snoc__solver_history initial updates i current output answer :
  0 <= i -> i < Zlength updates ->
  P073History initial updates i current output ->
  answer = AndExerciseSum (ApplyPointUpdate current (Znth i updates (0,0))) ->
  P073History initial updates (i+1)
    (ApplyPointUpdate current (Znth i updates (0,0))) (output ++ answer :: nil).
Proof.
  intros Hi Hui [states [Hlen [Hinit [Hcur [Hsteps [Hout Hans]]]]]] Ha.
  unfold P073History.
  exists (states ++ ApplyPointUpdate current (Znth i updates (0,0)) :: nil).
  split; [rewrite Zlength_app_cons, Hlen; lia |].
  split; [rewrite app_Znth1 by lia; exact Hinit |].
  split; [rewrite <- Hlen; apply P073Znth_snoc__solver_history |].
  split.
  - intros j Hj. destruct (Z.eq_dec j i) as [-> | Hji].
    + rewrite <- Hlen at 1. rewrite P073Znth_snoc__solver_history.
      rewrite app_Znth1 by lia. rewrite Hcur; reflexivity.
    + rewrite !app_Znth1 by lia. apply Hsteps; lia.
  - split; [rewrite Zlength_app_cons, Hout; reflexivity |].
    intros j Hj. destruct (Z.eq_dec j i) as [-> | Hji].
    + rewrite <- Hout at 1. rewrite P073Znth_snoc__solver_history.
      rewrite <- Hlen, P073Znth_snoc__solver_history. exact Ha.
    + rewrite !app_Znth1 by lia. apply Hans; lia.
Qed.
Lemma P073Replace_length__solver_history {A} (xs : list A) p v :
  Zlength (replace_Znth p v xs) = Zlength xs.
Proof.
  unfold replace_Znth. generalize (Z.to_nat p); clear p.
  induction xs as [|x xs IH]; intros n; destruct n; simpl;
    rewrite ?Zlength_cons; try reflexivity; rewrite IH; reflexivity.
Qed.
Lemma P073Replace_bounds__solver_history xs p v :
  0 <= p < Zlength xs -> 0 <= v <= 100000 ->
  (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0 <= 100000) ->
  forall k, 0 <= k < Zlength (replace_Znth p v xs) ->
    0 <= Znth k (replace_Znth p v xs) 0 <= 100000.
Proof.
  intros Hp Hv Hb k Hk. rewrite P073Replace_length__solver_history in Hk.
  destruct (Z.eq_dec k p) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia. exact Hv.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hb; exact Hk.
Qed.
Lemma P073Pow17__solver_safety : forall b,
  0 <= b <= 16 -> 1 <= 2^b <= 65536.
Proof.
  intros b Hb. split.
  - pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)). lia.
  - change (2^b <= 2^16). apply Z.pow_le_mono_r; lia.
Qed.
Lemma P073Shift17__solver_safety : forall b,
  0 <= b <= 16 ->
  Z.shiftl 1 b = 2^b /\ 1 <= 2^b <= 65536.
Proof.
  intros b Hb. pose proof (P073Pow17__solver_safety b Hb) as Hp.
  split; [|exact Hp].
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_1_l. reflexivity.
Qed.
Lemma P073_count_pair_bound__pull_count_safety :
  forall n pr su ct ln i j,
  1 <= n <= 100000 -> P073BufferBounds n pr su ct ln ->
  0 <= i < 68*n -> 0 <= j < 68*n ->
  0 <= Znth i ct 0 + Znth j ct 0 <= 10000100000.
Proof.
  intros n pr su ct ln i j Hn [HB HL] Hi Hj.
  pose proof (HB i Hi) as [_ [_ HC1]].
  pose proof (HB j Hj) as [_ [_ HC2]].
  assert (Hcap : n*(n+1)/2 <= 5000050000).
  { apply Z.div_le_upper_bound; nia. }
  lia.
Qed.
Lemma Znth_replace_distinct__pull_product_safety :
  forall (l : list Z) i j value,
  0 <= i -> 0 <= j -> i <> j ->
  Znth j (replace_Znth i value l) 0 = Znth j l 0.
Proof.
  intros l i j value Hi Hj Hij.
  unfold Znth, replace_Znth.
  assert (Hne : Z.to_nat i <> Z.to_nat j) by lia.
  generalize dependent (Z.to_nat i).
  generalize dependent (Z.to_nat j).
  induction l as [|x l IH]; intros n m Hne.
  - destruct n; reflexivity.
  - destruct m, n; simpl in *; try reflexivity; try congruence.
    apply IH. congruence.
Qed.
Lemma nth_replace_other__pull_total_safety :
  forall (xs : list Z) (i j : nat) value default,
  i <> j -> nth j (replace_nth i xs value) default = nth j xs default.
Proof.
  induction xs as [|x xs IH]; intros i j value default Hneq.
  - destruct j; reflexivity.
  - destruct i, j; simpl; try reflexivity; try congruence.
    apply IH. congruence.
Qed.
Lemma Znth_replace_other__pull_total_safety :
  forall (xs : list Z) (i j value : Z),
  0 <= i -> 0 <= j -> i <> j ->
  Znth j (replace_Znth i value xs) 0 = Znth j xs 0.
Proof.
  intros xs i j value Hi Hj Hneq.
  unfold Znth, replace_Znth.
  apply nth_replace_other__pull_total_safety. lia.
Qed.
Lemma total_bounds__pull_total_safety :
  forall N pr su ct ln i j,
  1 <= N <= 100000 -> P073BufferBounds N pr su ct ln ->
  0 <= i < 68*N -> 0 <= j < 68*N ->
  0 <= Znth i ct 0 + Znth j ct 0 + Znth i su 0 * Znth j pr 0
    <= 20000100000.
Proof.
  intros N pr su ct ln i j HN [HB HL] Hi Hj.
  specialize (HB i Hi) as HBi.
  specialize (HB j Hj) as HBj.
  destruct HBi as [Hpi [Hsi Hci]].
  destruct HBj as [Hpj [Hsj Hcj]].
  assert (Hcap : N*(N+1)/2 <= 5000050000).
  { apply Z.div_le_upper_bound; nia. }
  assert (Hprod : Znth i su 0 * Znth j pr 0 <= 10000000000) by nia.
  nia.
Qed.
