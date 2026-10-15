Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* One step of the scan: position i either beats the current record holder, who
   then pays their own value and hands the record over, or it does not and the
   position pays nothing. *)
Definition RecordStep (a order leaders add : list Z) (i : Z) : Prop :=
  (Znth (Znth (i - 1) leaders 1 - 1) a 0 < Znth (Znth i order 1 - 1) a 0 /\
   Znth i leaders 0 = Znth i order 1 /\
   Znth i add 0 = Znth (Znth (i - 1) leaders 1 - 1) a 0) \/
  (Znth (Znth (i - 1) leaders 1 - 1) a 0 >= Znth (Znth i order 1 - 1) a 0 /\
   Znth i leaders 0 = Znth (i - 1) leaders 0 /\
   Znth i add 0 = 0).

(* The scan over one permutation: [leaders] holds the record holder after each
   position and [add] what that position contributed. *)
Definition RecordRun (a order leaders add : list Z) : Prop :=
  Zlength leaders = Zlength a /\ Zlength add = Zlength a /\
  Znth 0 leaders 0 = Znth 0 order 1 /\ Znth 0 add 0 = 0 /\
  forall i, 1 <= i < Zlength a -> RecordStep a order leaders add i.

(* The value f of one permutation: everything the scan adds up. *)
Definition HistoryValue (a order : list Z) (v : Z) : Prop :=
  Permutation order (Zrange 1 (Zlength a + 1)) /\
  exists leaders add : list Z,
    RecordRun a order leaders add /\ v = fold_right Z.add 0 add.
Definition AllPermutations (n : Z) (ps : list (list Z)) : Prop :=
  NoDup ps /\ forall p, In p ps <-> (Permutation p (Zrange 1 (n + 1))).
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P083 solver Require, so dropped here:
       1 <= Zlength a <= 1000000 /\
       Forall (fun x => 1 <= x <= 1000000000) a  *)
  True.

Definition Spec (a : list Z) (out : Z) : Prop :=
  exists ps f, AllPermutations (Zlength a) ps /\ (forall p, In p ps -> HistoryValue a p (f p)) /\
  out = (fold_right Z.add 0) (map f ps) mod 1000000007.

(* Modular exponentiation, the mathematical meaning of [power]. *)
Definition ModPower (base exponent result : Z) : Prop :=
  result = (base ^ exponent) mod 1000000007.

(* ---------------------------------------------------------------- *)
(* Internal predicates: the mathematical state of the C loops.       *)
(* ---------------------------------------------------------------- *)

(* Square-and-multiply invariant of [power]. *)
Definition PowerLoopState
    (original_base original_exponent accumulator current_base
     remaining_exponent : Z) : Prop :=
  (accumulator * (current_base ^ remaining_exponent)) mod 1000000007 =
  (original_base ^ original_exponent) mod 1000000007.

(* Factorial as a plain mathematical function. *)
Fixpoint fact_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S k => Z.of_nat (S k) * fact_nat k
  end.

Definition Zfact (n : Z) : Z := fact_nat (Z.to_nat n).

(* The accumulator of the factorial loop holds (i-1)! reduced mod p. *)
Definition FactorialModState (i value : Z) : Prop :=
  value = (Zfact (i - 1)) mod 1000000007.

(* Index [i] starts a maximal run of equal values of [l] (or is an end). *)
Definition GroupBoundary (l : list Z) (i : Z) : Prop :=
  i = 0 \/ i = Zlength l \/
  (0 < i < Zlength l /\ Znth (i - 1) l 0 < Znth i l 0).

(* Size of the >=-class of [v] inside [l]; it is Permutation-invariant. *)
Definition count_ge (l : list Z) (v : Z) : Z :=
  Zlength (filter (fun w => Z.leb v w) l).

(* Closed-form contribution of one element value of [l]:
   [v] is added once per ordering in which it is first among its >=-class,
   which happens in (Zlength l)! / count_ge l v of them, and only when some
   strictly larger element exists at all. *)
Definition contrib (l : list Z) (v : Z) : Z :=
  if existsb (fun w => Z.ltb v w) l
  then v * (Zfact (Zlength l) / count_ge l v)
  else 0.

Definition contrib_list (l : list Z) : list Z := map (contrib l) l.

(* The scan accumulator [total] is the mod-reduced closed-form sum over the
   first [i] entries of [l]. *)
Definition ContribPrefixSum (l : list Z) (i total : Z) : Prop :=
  total = (fold_right Z.add 0 (sublist 0 i (contrib_list l))) mod 1000000007.

(* ---------------------------------------------------------------- *)
(* Executable witnesses for the existentials of [Spec] (proof side). *)
(* ---------------------------------------------------------------- *)

Fixpoint remove_first (x : Z) (l : list Z) : list Z :=
  match l with
  | nil => nil
  | y :: t => if Z.eq_dec x y then t else y :: remove_first x t
  end.

(* All orderings of [l], recursing on the chosen first element. *)
Fixpoint perms_of (fuel : nat) (l : list Z) : list (list Z) :=
  match fuel with
  | O => (nil : list Z) :: nil
  | S k => flat_map (fun x => map (cons x) (perms_of k (remove_first x l))) l
  end.

(* The record scan of [RecordRun], run explicitly.  [lead] is the current
   record holder (a 1-based index into [a]) and [p] the remaining ordering. *)
Fixpoint scan_aux (a : list Z) (p : list Z) (lead : Z) : list Z * list Z :=
  match p with
  | nil => (nil, nil)
  | x :: t =>
      if Z.ltb (Znth (lead - 1) a 0) (Znth (x - 1) a 0)
      then let r := scan_aux a t x in
           (x :: fst r, Znth (lead - 1) a 0 :: snd r)
      else let r := scan_aux a t lead in
           (lead :: fst r, 0 :: snd r)
  end.

Definition scan_run (a p : list Z) : list Z * list Z :=
  match p with
  | nil => (nil, nil)
  | x :: t => let r := scan_aux a t x in (x :: fst r, 0 :: snd r)
  end.

Definition scan_leaders (a p : list Z) : list Z := fst (scan_run a p).
Definition scan_add (a p : list Z) : list Z := snd (scan_run a p).

Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.Zquot.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.Znumtheory.
Lemma rem_eq_mod_nonneg__power_modexp : forall a m : Z,
  0 <= a -> 0 < m -> Z.rem a m = a mod m /\ 0 <= Z.rem a m < m.
Proof.
  intros a m Ha Hm.
  assert (Heq : Z.rem a m = a mod m) by (apply Zrem_Zmod_pos; lia).
  split; [exact Heq | ].
  rewrite Heq.
  apply Z.mod_pos_bound.
  lia.
Qed.
Lemma shiftr_land1_decompose__power_modexp : forall e : Z,
  0 <= e ->
  Z.shiftr e 1 = e / 2 /\
  0 <= Z.shiftr e 1 <= e /\
  e = 2 * Z.shiftr e 1 + Z.land e 1 /\
  (Z.land e 1 = 0 \/ Z.land e 1 = 1).
Proof.
  intros e He.
  assert (Hs : Z.shiftr e 1 = e / 2).
  { rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (Hones : Z.ones 1 = 1) by reflexivity.
  assert (Hl : Z.land e 1 = e mod 2).
  { rewrite <- Hones. rewrite Z.land_ones by lia. reflexivity. }
  assert (Hdm : e = 2 * (e / 2) + e mod 2) by (apply Z.div_mod; lia).
  assert (Hb : 0 <= e mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite Hs, Hl.
  repeat split; lia.
Qed.
Lemma pow_mod_square_step__power_modexp : forall b p k : Z,
  0 < p -> 0 <= k ->
  (((b * b) mod p) ^ k) mod p = (b ^ (2 * k)) mod p.
Proof.
  intros b p k Hp Hk.
  rewrite <- Zpower_mod by lia.
  replace (b * b) with (b ^ 2) by ring.
  rewrite <- Z.pow_mul_r by lia.
  reflexivity.
Qed.
Lemma rem_nonneg_bound__solver_arith_safety : forall a m : Z,
  0 <= a -> 0 < m -> 0 <= Z.rem a m < m.
Proof.
  intros a m Ha Hm.
  apply Z.rem_bound_pos; assumption.
Qed.
Lemma znth_bounds_perm_transfer__solver_loop_setup :
  forall (l l' : list Z) (n lo hi : Z),
    Permutation l l' ->
    Zlength l = n ->
    (forall i, 0 <= i < n -> lo <= Znth i l 0 <= hi) ->
    Zlength l' = n /\ (forall i, 0 <= i < n -> lo <= Znth i l' 0 <= hi).
Proof.
  intros l l' n lo hi Hperm Hlen Hbound.
  assert (Hlen' : Zlength l' = n).
  { rewrite Zlength_correct in *.
    rewrite <- (Permutation_length Hperm). exact Hlen. }
  split; [exact Hlen' | ].
  assert (Hall : Forall (fun x => lo <= x <= hi) l).
  { apply Forall_forall. intros x Hx.
    apply (In_nth l x 0) in Hx. destruct Hx as [k [Hk Hnth]].
    specialize (Hbound (Z.of_nat k)).
    rewrite Zlength_correct in Hlen.
    unfold Znth in Hbound. rewrite Nat2Z.id in Hbound.
    rewrite Hnth in Hbound. apply Hbound. lia. }
  assert (Hall' : Forall (fun x => lo <= x <= hi) l').
  { apply Forall_forall. intros x Hx.
    rewrite Forall_forall in Hall. apply Hall.
    apply (Permutation_in x (Permutation_sym Hperm)). exact Hx. }
  intros i Hi.
  rewrite Forall_forall in Hall'.
  apply Hall'. unfold Znth. apply nth_In.
  rewrite Zlength_correct in Hlen'. lia.
Qed.
Lemma zfact_succ_step__solver_loop_setup :
  forall i : Z, 1 <= i -> Zfact i = i * Zfact (i - 1).
Proof.
  intros i Hi. unfold Zfact.
  remember (Z.to_nat (i - 1)) as k eqn:Hk.
  assert (Hsucc : Z.to_nat i = S k) by lia.
  rewrite Hsucc. cbn [fact_nat].
  replace (Z.of_nat (S k)) with i by lia.
  reflexivity.
Qed.
Lemma rem_eq_mod_nonneg__solver_loop_setup :
  forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = a mod b.
Proof.
  intros a b Ha Hb. apply Z.rem_mod_nonneg; lia.
Qed.
Lemma rem_eq_mod_nonneg__group_contribution_step : forall a m,
  0 <= a -> 0 < m ->
  Z.rem a m = a mod m /\ 0 <= Z.rem a m < m.
Proof.
  intros a m Ha Hm. split.
  - apply Z.rem_mod_nonneg; lia.
  - apply Z.rem_bound_pos; lia.
Qed.
Lemma In_Znth_ex__group_contribution_step : forall (l : list Z) (x : Z),
  In x l -> exists k, 0 <= k < Zlength l /\ Znth k l 0 = x.
Proof.
  intros l x H.
  apply (In_nth l x 0) in H.
  destruct H as [n [Hn Heq]].
  exists (Z.of_nat n). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Heq.
Qed.
Lemma filter_all_true__group_contribution_step : forall (f : Z -> bool) (l : list Z),
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros f l. induction l as [| a l IH]; intros H; simpl.
  - reflexivity.
  - rewrite (H a) by (simpl; auto).
    rewrite IH by (intros x Hx; apply H; simpl; auto).
    reflexivity.
Qed.
Lemma filter_all_false__group_contribution_step : forall (f : Z -> bool) (l : list Z),
  (forall x, In x l -> f x = false) -> filter f l = nil.
Proof.
  intros f l. induction l as [| a l IH]; intros H; simpl.
  - reflexivity.
  - rewrite (H a) by (simpl; auto).
    apply IH. intros x Hx. apply H. simpl; auto.
Qed.
Lemma fold_add_app__group_contribution_step : forall (l1 l2 : list Z),
  fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  intros l1 l2. induction l1 as [| a l1 IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.
Lemma fold_add_const__group_contribution_step : forall (l : list Z) (c : Z),
  (forall x, In x l -> x = c) ->
  fold_right Z.add 0 l = Zlength l * c.
Proof.
  intros l c. induction l as [| a l IH]; intros H.
  - rewrite Zlength_nil. simpl. lia.
  - simpl. rewrite (H a) by (simpl; auto).
    rewrite IH by (intros x Hx; apply H; simpl; auto).
    rewrite Zlength_cons. lia.
Qed.
Lemma sublist_map__group_contribution_step :
  forall (A B : Type) (f : A -> B) (lo hi : Z) (l : list A),
  sublist lo hi (map f l) = map f (sublist lo hi l).
Proof.
  intros A B f lo hi l. unfold sublist.
  rewrite firstn_map, skipn_map. reflexivity.
Qed.
Lemma Zlength_map__group_contribution_step :
  forall (A B : Type) (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma count_ge_sorted_group__group_contribution_step : forall (l : list Z) (i : Z),
  mono_nondec l ->
  GroupBoundary l i ->
  0 <= i < Zlength l ->
  count_ge l (Znth i l 0) = Zlength l - i.
Proof.
  intros l i Hmono Hgb Hi.
  unfold count_ge.
  assert (Hsplit : l = sublist 0 i l ++ sublist i (Zlength l) l).
  { rewrite <- (sublist_split 0 (Zlength l) i l) by lia.
    rewrite (sublist_self l (Zlength l)) by reflexivity. reflexivity. }
  assert (Htrue : filter (fun w => Z.leb (Znth i l 0) w) (sublist i (Zlength l) l)
                = sublist i (Zlength l) l).
  { apply filter_all_true__group_contribution_step.
    intros x Hx.
    apply In_Znth_ex__group_contribution_step in Hx.
    destruct Hx as [k [Hk Hkx]].
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist in Hkx by lia.
    apply Z.leb_le. rewrite <- Hkx. apply Hmono; lia. }
  assert (Hfalse : filter (fun w => Z.leb (Znth i l 0) w) (sublist 0 i l) = nil).
  { apply filter_all_false__group_contribution_step.
    intros x Hx.
    apply In_Znth_ex__group_contribution_step in Hx.
    destruct Hx as [k [Hk Hkx]].
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist in Hkx by lia.
    apply Z.leb_gt. rewrite <- Hkx.
    destruct Hgb as [Hz | [Hz | [Hz Hlt]]]; try lia.
    assert (Znth (k + 0) l 0 <= Znth (i - 1) l 0) by (apply Hmono; lia).
    lia. }
  assert (Hgoal : filter (fun w => Z.leb (Znth i l 0) w) l = sublist i (Zlength l) l).
  { transitivity (filter (fun w => Z.leb (Znth i l 0) w)
                   (sublist 0 i l ++ sublist i (Zlength l) l)).
    - f_equal. exact Hsplit.
    - rewrite filter_app, Hfalse, Htrue. reflexivity. }
  rewrite Hgoal. rewrite Zlength_sublist by lia. reflexivity.
Qed.
Lemma contrib_constant_on_group__group_contribution_step :
  forall (l : list Z) (q i : Z),
  Znth q l 0 = Znth i l 0 ->
  contrib l (Znth q l 0) = contrib l (Znth i l 0).
Proof.
  intros l q i H. rewrite H. reflexivity.
Qed.
Lemma contrib_prefix_extend__group_contribution_step :
  forall (l : list Z) (i j : Z),
  0 <= i <= j -> j <= Zlength l ->
  (forall q, i <= q < j -> Znth q l 0 = Znth i l 0) ->
  fold_right Z.add 0 (sublist 0 j (contrib_list l)) =
  fold_right Z.add 0 (sublist 0 i (contrib_list l)) + (j - i) * contrib l (Znth i l 0).
Proof.
  intros l i j Hij Hj Hconst.
  unfold contrib_list.
  assert (Hlen : Zlength (map (contrib l) l) = Zlength l)
    by (rewrite Zlength_map__group_contribution_step; reflexivity).
  rewrite (sublist_split 0 j i (map (contrib l) l)) by lia.
  rewrite fold_add_app__group_contribution_step.
  f_equal.
  rewrite sublist_map__group_contribution_step.
  rewrite (fold_add_const__group_contribution_step _ (contrib l (Znth i l 0))).
  - rewrite Zlength_map__group_contribution_step, Zlength_sublist by lia. reflexivity.
  - intros x Hx.
    apply in_map_iff in Hx.
    destruct Hx as [y [Hy Hiny]].
    apply In_Znth_ex__group_contribution_step in Hiny.
    destruct Hiny as [k [Hk Hky]].
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist in Hky by lia.
    rewrite <- Hy, <- Hky, (Hconst (k + i)) by lia.
    reflexivity.
Qed.
Lemma contrib_zero_on_max_group__group_contribution_step :
  forall (l : list Z) (i : Z),
  mono_nondec l ->
  0 <= i < Zlength l ->
  (forall q, i <= q < Zlength l -> Znth q l 0 = Znth i l 0) ->
  contrib l (Znth i l 0) = 0.
Proof.
  intros l i Hmono Hi Hconst.
  unfold contrib.
  assert (Hguard : existsb (fun w => Z.ltb (Znth i l 0) w) l = false).
  { destruct (existsb (fun w => Z.ltb (Znth i l 0) w) l) eqn:E; [| reflexivity].
    exfalso.
    apply existsb_exists in E.
    destruct E as [x [Hx Hlt]].
    apply Z.ltb_lt in Hlt.
    apply In_Znth_ex__group_contribution_step in Hx.
    destruct Hx as [k [Hk Hkx]].
    destruct (Z.lt_ge_cases k i) as [Hlo | Hhi].
    - assert (Znth k l 0 <= Znth i l 0) by (apply Hmono; lia). lia.
    - rewrite (Hconst k) in Hkx by lia. lia. }
  rewrite Hguard. reflexivity.
Qed.
Lemma prime_1000000007__group_contribution_step : prime 1000000007.
Proof.
  assert (Hchk : forallb (fun d => negb (Z.eqb (1000000007 mod d) 0))
                         (Zrange 2 31624) = true)
    by (vm_compute; reflexivity).
  assert (Hnd : forall d, 2 <= d < 31624 -> 1000000007 mod d <> 0).
  { intros d Hd.
    rewrite forallb_forall in Hchk.
    specialize (Hchk d (proj1 (In_Zrange 2 31624 d) Hd)).
    apply negb_true_iff in Hchk. apply Z.eqb_neq in Hchk. exact Hchk. }
  apply prime_alt. split; [lia |].
  intros n Hn Hdiv.
  destruct Hn as [Hn1 Hn2].
  destruct (Z.le_gt_cases (n * n) 1000000007) as [Hle | Hgt].
  - assert (n < 31624) by nia.
    apply (Hnd n); [lia |].
    apply Zdivide_mod. exact Hdiv.
  - destruct Hdiv as [k Hk].
    assert (Hkpos : 0 < k) by nia.
    assert (Hk1 : 1 < k).
    { destruct (Z.eq_dec k 1) as [He | Hne]; [subst k; lia | lia]. }
    assert (Hkn : k < n) by nia.
    assert (Hkk : k * k < 1000000007) by nia.
    assert (k < 31624) by nia.
    apply (Hnd k); [lia |].
    apply Zdivide_mod. exists n. rewrite Z.mul_comm. exact Hk.
Qed.
Lemma nodup_map_inj_on__group_contribution_step :
  forall (A B : Type) (f : A -> B) (l : list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (map f l).
Proof.
  intros A B f l. induction l as [| a l IH]; intros Hnd Hinj; simpl.
  - constructor.
  - inversion Hnd as [| a' l' Hnotin Hndl]; subst.
    constructor.
    + intros Hin. apply in_map_iff in Hin.
      destruct Hin as [y [Hfy Hy]].
      assert (a = y) by (apply Hinj; simpl; auto).
      subst y. contradiction.
    + apply IH; auto.
      intros x y Hx Hy. apply Hinj; simpl; auto.
Qed.
Lemma fold_mul_perm__group_contribution_step : forall (l l' : list Z),
  Permutation l l' ->
  fold_right Z.mul 1 l = fold_right Z.mul 1 l'.
Proof.
  intros l l' H. induction H.
  - reflexivity.
  - simpl. rewrite IHPermutation. reflexivity.
  - simpl. ring.
  - congruence.
Qed.
Lemma fold_mul_mod__group_contribution_step : forall (m : Z) (l : list Z),
  0 < m ->
  fold_right Z.mul 1 (map (fun x => x mod m) l) mod m = fold_right Z.mul 1 l mod m.
Proof.
  intros m l Hm. induction l as [| a l IH]; simpl.
  - reflexivity.
  - rewrite Zmult_mod. rewrite IH. rewrite Z.mod_mod by lia.
    rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma fold_mul_scale__group_contribution_step : forall (g : Z) (l : list Z),
  fold_right Z.mul 1 (map (fun x => g * x) l) =
  g ^ (Z.of_nat (length l)) * fold_right Z.mul 1 l.
Proof.
  intros g l. induction l as [| a l IH].
  - simpl. ring.
  - cbn [map fold_right length]. rewrite IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.
Lemma prime_not_div_fold__group_contribution_step : forall (p : Z) (l : list Z),
  prime p ->
  (forall x, In x l -> ~ (p | x)) ->
  ~ (p | fold_right Z.mul 1 l).
Proof.
  intros p l Hp. induction l as [| a l IH]; intros Hall Hdiv; simpl in Hdiv.
  - pose proof (prime_ge_2 p Hp) as Hp2.
    assert (p <= 1) by (apply Z.divide_pos_le; [lia | exact Hdiv]).
    lia.
  - apply prime_mult in Hdiv; [| exact Hp].
    destruct Hdiv as [H1 | H1].
    + apply (Hall a); simpl; auto.
    + apply IH; auto. intros x Hx. apply Hall; simpl; auto.
Qed.
Lemma fermat_little__group_contribution_step : forall (p g : Z),
  prime p -> 0 < g < p -> g ^ (p - 1) mod p = 1.
Proof.
  intros p g Hp Hg.
  assert (Hp2 : 2 <= p) by (apply prime_ge_2; exact Hp).
  set (N := Z.to_nat (p - 1)).
  assert (HN : Z.of_nat N = p - 1) by (unfold N; rewrite Z2Nat.id; lia).
  clearbody N.
  set (L := map Z.of_nat (seq 1 N)).
  assert (HinL : forall x, In x L <-> 1 <= x <= p - 1).
  { intros x. unfold L. rewrite in_map_iff. split.
    - intros [n [Hn Hin]]. apply in_seq in Hin. lia.
    - intros Hx. exists (Z.to_nat x). split.
      + rewrite Z2Nat.id; lia.
      + apply in_seq. lia. }
  assert (HlenL : Z.of_nat (length L) = p - 1).
  { unfold L. rewrite length_map, length_seq. exact HN. }
  assert (HndL : NoDup L).
  { unfold L. apply nodup_map_inj_on__group_contribution_step.
    - apply seq_NoDup.
    - intros x y _ _ H. lia. }
  clearbody L.
  assert (Hgnd : ~ (p | g)).
  { intros Hd. pose proof (Z.divide_pos_le p g ltac:(lia) Hd). lia. }
  assert (Hrel : rel_prime p g) by (apply prime_rel_prime; assumption).
  assert (HPnd : ~ (p | fold_right Z.mul 1 L)).
  { apply prime_not_div_fold__group_contribution_step; [exact Hp |].
    intros x Hx Hdx. apply HinL in Hx.
    pose proof (Z.divide_pos_le p x ltac:(lia) Hdx). lia. }
  assert (HrelP : rel_prime p (fold_right Z.mul 1 L))
    by (apply prime_rel_prime; assumption).
  assert (Himg : forall x, In x L -> In ((g * x) mod p) L).
  { intros x Hx. apply HinL in Hx. apply HinL.
    pose proof (Z.mod_pos_bound (g * x) p ltac:(lia)) as Hb.
    assert (Hne : (g * x) mod p <> 0).
    { intros Hz.
      assert (Hd : (p | g * x)) by (apply Zmod_divide; [lia | exact Hz]).
      apply prime_mult in Hd; [| exact Hp].
      destruct Hd as [H1 | H1]; [contradiction |].
      pose proof (Z.divide_pos_le p x ltac:(lia) H1). lia. }
    lia. }
  assert (Hinj : forall x y, In x L -> In y L ->
                 (g * x) mod p = (g * y) mod p -> x = y).
  { intros x y Hx Hy Heq. apply HinL in Hx. apply HinL in Hy.
    assert (Hd0 : (g * x - g * y) mod p = 0)
      by (rewrite Zminus_mod, Heq, Z.sub_diag; reflexivity).
    assert (Hd : (p | g * x - g * y)) by (apply Zmod_divide; [lia | exact Hd0]).
    assert (Hd2 : (p | g * (x - y)))
      by (replace (g * (x - y)) with (g * x - g * y) by ring; exact Hd).
    apply Gauss in Hd2; [| exact Hrel].
    destruct Hd2 as [k Hk].
    destruct (Z.eq_dec k 0) as [Hk0 | Hk0]; [subst k; lia |].
    exfalso.
    assert (Hcase : k <= -1 \/ 1 <= k) by lia.
    destruct Hcase as [Hc | Hc].
    - assert (k * p <= -1 * p) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    - assert (1 * p <= k * p) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  assert (Hperm : Permutation (map (fun x => (g * x) mod p) L) L).
  { apply NoDup_Permutation_bis.
    - apply nodup_map_inj_on__group_contribution_step; assumption.
    - rewrite length_map. lia.
    - intros x Hx. apply in_map_iff in Hx.
      destruct Hx as [y [Hy Hiny]]. subst x. apply Himg. exact Hiny. }
  assert (HP1 : fold_right Z.mul 1 (map (fun x => (g * x) mod p) L)
              = fold_right Z.mul 1 L)
    by (apply fold_mul_perm__group_contribution_step; exact Hperm).
  assert (HP2 : fold_right Z.mul 1 (map (fun x => (g * x) mod p) L) mod p
              = (g ^ (p - 1) * fold_right Z.mul 1 L) mod p).
  { assert (Hmm : map (fun x => (g * x) mod p) L
                = map (fun y => y mod p) (map (fun x => g * x) L))
      by (rewrite map_map; reflexivity).
    rewrite Hmm.
    rewrite fold_mul_mod__group_contribution_step by lia.
    rewrite fold_mul_scale__group_contribution_step.
    rewrite HlenL. reflexivity. }
  assert (Hkey : (g ^ (p - 1) * fold_right Z.mul 1 L) mod p
               = fold_right Z.mul 1 L mod p)
    by (rewrite <- HP2, HP1; reflexivity).
  assert (Hdvd : (p | g ^ (p - 1) - 1)).
  { assert (Hd0 : (fold_right Z.mul 1 L * (g ^ (p - 1) - 1)) mod p = 0).
    { replace (fold_right Z.mul 1 L * (g ^ (p - 1) - 1))
        with (g ^ (p - 1) * fold_right Z.mul 1 L - fold_right Z.mul 1 L) by ring.
      rewrite Zminus_mod, Hkey, Z.sub_diag. reflexivity. }
    assert (Hd : (p | fold_right Z.mul 1 L * (g ^ (p - 1) - 1)))
      by (apply Zmod_divide; [lia | exact Hd0]).
    apply Gauss in Hd; [exact Hd | exact HrelP]. }
  apply Zdivide_mod_minus; [lia | exact Hdvd].
Qed.
Lemma fermat_inverse_mod_p__group_contribution_step : forall g : Z,
  0 < g < 1000000007 ->
  (g ^ (1000000007 - 2) * g) mod 1000000007 = 1.
Proof.
  intros g Hg.
  assert (Hsplitpow : g ^ (1000000007 - 1) = g ^ (1000000007 - 2) * g).
  { replace (1000000007 - 1) with (1000000007 - 2 + 1) by lia.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. reflexivity. }
  rewrite <- Hsplitpow.
  apply fermat_little__group_contribution_step.
  - exact prime_1000000007__group_contribution_step.
  - exact Hg.
Qed.
Lemma fact_nat_divide__group_contribution_step : forall (m : nat) (g : Z),
  1 <= g <= Z.of_nat m -> (g | fact_nat m).
Proof.
  induction m as [| k IH]; intros g Hg.
  - simpl in Hg. lia.
  - cbn [fact_nat].
    destruct (Z.eq_dec g (Z.of_nat (S k))) as [He | Hne].
    + rewrite He. exists (fact_nat k). ring.
    + assert (Hne' : g <> Z.succ (Z.of_nat k))
        by (rewrite <- Nat2Z.inj_succ; exact Hne).
      rewrite Nat2Z.inj_succ in Hg.
      destruct (IH g ltac:(lia)) as [q Hq].
      exists (Z.of_nat (S k) * q). rewrite Hq. ring.
Qed.
Lemma fact_divide__group_contribution_step : forall (n g : Z),
  1 <= g <= n -> (g | Zfact n).
Proof.
  intros n g Hg. unfold Zfact.
  apply fact_nat_divide__group_contribution_step.
  rewrite Z2Nat.id by lia. exact Hg.
Qed.
Lemma exact_quotient_mod_inverse__group_contribution_step : forall (n g : Z),
  0 < g <= n -> n <= 1000000 ->
  (g | Zfact n) /\
  (Zfact n / g) mod 1000000007
    = ((Zfact n mod 1000000007) * (g ^ (1000000007 - 2) mod 1000000007))
      mod 1000000007.
Proof.
  intros n g Hg Hn.
  assert (Hdvd : (g | Zfact n))
    by (apply fact_divide__group_contribution_step; lia).
  split; [exact Hdvd |].
  destruct Hdvd as [q Hq].
  assert (Hq' : Zfact n / g = q) by (rewrite Hq; apply Z.div_mul; lia).
  assert (Hgpos : 0 < g < 1000000007) by lia.
  assert (Hnz : 1000000007 <> 0) by discriminate.
  rewrite Hq', Hq.
  assert (Hferm : (g ^ (1000000007 - 2) * g) mod 1000000007 = 1)
    by (apply fermat_inverse_mod_p__group_contribution_step; exact Hgpos).
  remember (g ^ (1000000007 - 2)) as E eqn:HE. clear HE.
  transitivity ((q * (E * g)) mod 1000000007).
  - rewrite Zmult_mod, Hferm, Z.mul_1_r, (Z.mod_mod q 1000000007 Hnz).
    reflexivity.
  - rewrite <- Zmult_mod. f_equal. lia.
Qed.
Lemma Znth_In__group_contribution_step : forall (l : list Z) (i : Z),
  0 <= i < Zlength l -> In (Znth i l 0) l.
Proof.
  intros l i Hi. apply Znth_In_Zlength. exact Hi.
Qed.
Lemma sum_perm__spec_final_result : forall (l l' : list Z),
  Permutation l l' ->
  fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof.
  intros l l' H. induction H; simpl; lia.
Qed.
Lemma sum_map_zero__spec_final_result : forall {A : Type} (l : list A),
  fold_right Z.add 0 (map (fun _ : A => 0) l) = 0.
Proof.
  intros A l. induction l; simpl; lia.
Qed.
Lemma sum_map_ext__spec_final_result : forall {A : Type} (f g : A -> Z) (l : list A),
  (forall x, In x l -> f x = g x) ->
  fold_right Z.add 0 (map f l) = fold_right Z.add 0 (map g l).
Proof.
  intros A f g l H. induction l as [| a t IH]; simpl; [ reflexivity | ].
  rewrite H by (left; reflexivity).
  rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.
Lemma sum_map_add__spec_final_result : forall {A : Type} (f g : A -> Z) (l : list A),
  fold_right Z.add 0 (map (fun x => f x + g x) l) =
  fold_right Z.add 0 (map f l) + fold_right Z.add 0 (map g l).
Proof.
  intros A f g l. induction l as [| a t IH]; simpl; lia.
Qed.
Lemma sum_swap__spec_final_result :
  forall {A B : Type} (h : A -> B -> Z) (la : list A) (lb : list B),
  fold_right Z.add 0 (map (fun x => fold_right Z.add 0 (map (fun y => h x y) lb)) la) =
  fold_right Z.add 0 (map (fun y => fold_right Z.add 0 (map (fun x => h x y) la)) lb).
Proof.
  intros A B h la. induction la as [| a ta IH]; intros lb; simpl.
  - rewrite (sum_map_zero__spec_final_result lb). reflexivity.
  - rewrite IH.
    rewrite <- (sum_map_add__spec_final_result (fun y => h a y)
                 (fun y => fold_right Z.add 0 (map (fun x => h x y) ta)) lb).
    reflexivity.
Qed.
Lemma sum_indicator__spec_final_result :
  forall {A : Type} (B : A -> bool) (w : Z) (l : list A),
  fold_right Z.add 0 (map (fun x => if B x then w else 0) l) =
  w * Zlength (filter B l).
Proof.
  intros A B w l. induction l as [| a t IH]; simpl.
  - rewrite Zlength_nil. lia.
  - destruct (B a) eqn:Ha; simpl.
    + rewrite Zlength_cons. rewrite IH. lia.
    + rewrite IH. lia.
Qed.
Lemma perm_filter__spec_final_result : forall {A : Type} (f : A -> bool) (l l' : list A),
  Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros A f l l' H. induction H; simpl.
  - constructor.
  - destruct (f x); [ constructor | ]; assumption.
  - destruct (f x) eqn:Hx; destruct (f y) eqn:Hy; simpl;
      try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.
Lemma nodup_app__spec_final_result : forall {A : Type} (l1 l2 : list A),
  NoDup l1 -> NoDup l2 ->
  (forall x, In x l1 -> In x l2 -> False) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1. induction l1 as [| a t IH]; intros l2 H1 H2 Hd; simpl; [ assumption | ].
  inversion H1; subst. constructor.
  - rewrite in_app_iff. intros [Hi | Hi].
    + contradiction.
    + apply (Hd a); [ left; reflexivity | assumption ].
  - apply IH; try assumption. intros x Hx Hx2. apply (Hd x); [ right; assumption | assumption ].
Qed.
Lemma nodup_map__spec_final_result : forall {A B : Type} (f : A -> B) (l : list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (map f l).
Proof.
  intros A B f l. induction l as [| a t IH]; intros Hn Hinj; simpl; [ constructor | ].
  inversion Hn; subst. constructor.
  - rewrite in_map_iff. intros [y [Hy Hin]].
    assert (a = y) by (apply Hinj; [ left; reflexivity | right; assumption | auto ]).
    subst. contradiction.
  - apply IH; [ assumption | ].
    intros x y Hx Hy Hf. apply Hinj; [ right | right | ]; assumption.
Qed.
Lemma zlength_flat_map__spec_final_result :
  forall {A B : Type} (F : A -> list B) (l : list A),
  Zlength (flat_map F l) = fold_right Z.add 0 (map (fun x => Zlength (F x)) l).
Proof.
  intros A B F l. induction l as [| a t IH]; simpl.
  - apply Zlength_nil.
  - rewrite Zlength_app. rewrite IH. reflexivity.
Qed.
Lemma nodup_flat_map__spec_final_result :
  forall {A B : Type} (F : A -> list B) (l : list A),
  NoDup l ->
  (forall x, In x l -> NoDup (F x)) ->
  (forall x y u, In x l -> In y l -> x <> y -> In u (F x) -> In u (F y) -> False) ->
  NoDup (flat_map F l).
Proof.
  intros A B F l. induction l as [| a t IH]; intros Hn Hf Hd; simpl; [ constructor | ].
  inversion Hn; subst.
  apply nodup_app__spec_final_result.
  - apply Hf. left. reflexivity.
  - apply IH; try assumption.
    + intros x Hx. apply Hf. right. assumption.
    + intros x y u Hx Hy Hxy Hu1 Hu2. apply (Hd x y u);
        [ right; assumption | right; assumption | assumption | assumption | assumption ].
  - intros u Hu1 Hu2. rewrite in_flat_map in Hu2. destruct Hu2 as [y [Hy Hu2]].
    apply (Hd a y u);
      [ left; reflexivity | right; assumption
      | intros Heq; subst; contradiction | assumption | assumption ].
Qed.
Lemma zlength_map__spec_final_result : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l. induction l as [| a t IH]; simpl.
  - reflexivity.
  - rewrite !Zlength_cons. lia.
Qed.
Lemma sum_map_const__spec_final_result : forall {A : Type} (c : Z) (l : list A),
  fold_right Z.add 0 (map (fun _ : A => c) l) = Zlength l * c.
Proof.
  intros A c l. induction l as [| a t IH]; simpl.
  - try rewrite Zlength_nil. lia.
  - rewrite Zlength_cons. rewrite IH. lia.
Qed.

(* ================================================================ *)
(* [remove_first] and the permutation enumeration [perms_of].        *)
(* ================================================================ *)
Lemma remove_first_perm__spec_final_result : forall (x : Z) (l : list Z),
  In x l -> Permutation l (x :: remove_first x l).
Proof.
  intros x l. induction l as [| y t IH]; intros Hin; simpl in *; [ contradiction | ].
  destruct (Z.eq_dec x y) as [Heq | Hne].
  - subst. apply Permutation_refl.
  - destruct Hin as [Hin | Hin]; [ symmetry in Hin; contradiction | ].
    eapply Permutation_trans; [ apply perm_skip; apply IH; assumption | ].
    apply perm_swap.
Qed.
Lemma remove_first_length__spec_final_result : forall (x : Z) (l : list Z),
  In x l -> S (length (remove_first x l)) = length l.
Proof.
  intros x l Hin.
  pose proof (remove_first_perm__spec_final_result x l Hin) as Hp.
  apply Permutation_length in Hp. simpl in Hp. lia.
Qed.
Lemma remove_first_nodup__spec_final_result : forall (x : Z) (l : list Z),
  NoDup l -> In x l -> NoDup (remove_first x l).
Proof.
  intros x l Hn Hin.
  pose proof (remove_first_perm__spec_final_result x l Hin) as Hp.
  apply (Permutation_NoDup Hp) in Hn.
  inversion Hn; assumption.
Qed.
Lemma perms_of_in__spec_final_result : forall (fuel : nat) (l p : list Z),
  length l = fuel -> (In p (perms_of fuel l) <-> Permutation p l).
Proof.
  induction fuel as [| k IH]; intros l p Hlen.
  - destruct l as [| a t]; [ | simpl in Hlen; lia ].
    simpl. split.
    + intros [H | H]; [ subst; apply Permutation_refl | contradiction ].
    + intros H. apply Permutation_sym in H. apply Permutation_nil in H.
      subst. left. reflexivity.
  - simpl. rewrite in_flat_map. split.
    + intros [x [Hx Hu]]. rewrite in_map_iff in Hu. destruct Hu as [q [Hq Hq2]].
      subst p.
      assert (Hrl : length (remove_first x l) = k).
      { pose proof (remove_first_length__spec_final_result x l Hx). lia. }
      apply (IH _ _ Hrl) in Hq2.
      eapply Permutation_trans; [ apply perm_skip; exact Hq2 | ].
      apply Permutation_sym. apply remove_first_perm__spec_final_result. assumption.
    + intros Hperm.
      assert (Hlp : length p = S k) by (apply Permutation_length in Hperm; lia).
      destruct p as [| x q]; [ simpl in Hlp; lia | ].
      assert (Hx : In x l).
      { eapply Permutation_in; [ exact Hperm | left; reflexivity ]. }
      exists x. split; [ assumption | ].
      rewrite in_map_iff. exists q. split; [ reflexivity | ].
      assert (Hrl : length (remove_first x l) = k).
      { pose proof (remove_first_length__spec_final_result x l Hx). lia. }
      apply (IH _ _ Hrl).
      apply Permutation_cons_inv with (a := x).
      eapply Permutation_trans; [ exact Hperm | ].
      apply remove_first_perm__spec_final_result. assumption.
Qed.
Lemma perms_of_nodup__spec_final_result : forall (fuel : nat) (l : list Z),
  NoDup l -> length l = fuel -> NoDup (perms_of fuel l).
Proof.
  induction fuel as [| k IH]; intros l Hn Hlen.
  - simpl. constructor; [ intros H; contradiction | constructor ].
  - simpl. apply nodup_flat_map__spec_final_result; [ assumption | | ].
    + intros x Hx. apply nodup_map__spec_final_result.
      * apply IH.
        -- apply remove_first_nodup__spec_final_result; assumption.
        -- pose proof (remove_first_length__spec_final_result x l Hx). lia.
      * intros u v _ _ Hc. inversion Hc. reflexivity.
    + intros x y u Hx Hy Hxy Hu1 Hu2.
      rewrite in_map_iff in Hu1, Hu2.
      destruct Hu1 as [q1 [Hq1 _]]. destruct Hu2 as [q2 [Hq2 _]].
      subst u. congruence.
Qed.
Lemma perms_of_zlength__spec_final_result : forall (fuel : nat) (l : list Z),
  length l = fuel -> Zlength (perms_of fuel l) = fact_nat fuel.
Proof.
  induction fuel as [| k IH]; intros l Hlen.
  - simpl. rewrite Zlength_cons. rewrite Zlength_nil. reflexivity.
  - simpl. rewrite zlength_flat_map__spec_final_result.
    transitivity (fold_right Z.add 0 (map (fun _ : Z => fact_nat k) l)).
    + apply sum_map_ext__spec_final_result.
      intros x Hx. rewrite zlength_map__spec_final_result.
      apply IH. pose proof (remove_first_length__spec_final_result x l Hx). lia.
    + rewrite sum_map_const__spec_final_result.
      rewrite Zlength_correct. rewrite Hlen. reflexivity.
Qed.

(* ================================================================ *)
(* The index range [1 .. Zlength a] and its values.                  *)
(* ================================================================ *)
Lemma zrange_aux_map_znth__spec_final_result : forall (n : nat) (a : list Z) (k : Z),
  length a = n ->
  map (fun y => Znth (y - k) a 0) (Zrange_aux k n) = a.
Proof.
  induction n as [| m IH]; intros a k Hlen.
  - destruct a as [| x t]; [ reflexivity | simpl in Hlen; lia ].
  - destruct a as [| x t]; [ simpl in Hlen; lia | ].
    simpl in Hlen. injection Hlen as Hlen.
    simpl. replace (k - k) with 0 by lia. rewrite Znth0_cons. f_equal.
    transitivity (map (fun y => Znth (y - (k + 1)) t 0) (Zrange_aux (k + 1) m)).
    + apply map_ext_in. intros y Hy.
      rewrite In_Zrange_aux in Hy.
      rewrite Znth_cons by lia. f_equal. lia.
    + apply IH. exact Hlen.
Qed.
Lemma zrange_map_znth__spec_final_result : forall (a : list Z),
  map (fun y => Znth (y - 1) a 0) (Zrange 1 (Zlength a + 1)) = a.
Proof.
  intros a. unfold Zrange.
  replace (Z.to_nat (Zlength a + 1 - 1)) with (length a)
    by (rewrite Zlength_correct; lia).
  apply zrange_aux_map_znth__spec_final_result. reflexivity.
Qed.
Lemma zlength_zrange__spec_final_result : forall (a : list Z),
  Zlength (Zrange 1 (Zlength a + 1)) = Zlength a.
Proof.
  intros a.
  rewrite <- (zlength_map__spec_final_result (fun y => Znth (y - 1) a 0)).
  rewrite zrange_map_znth__spec_final_result. reflexivity.
Qed.
Lemma filter_map__spec_final_result :
  forall {A B : Type} (f : A -> B) (g : B -> bool) (l : list A),
  filter g (map f l) = map f (filter (fun x => g (f x)) l).
Proof.
  intros A B f g l. induction l as [| a t IH]; simpl; [ reflexivity | ].
  destruct (g (f a)); simpl; [ f_equal | ]; assumption.
Qed.
Lemma existsb_map__spec_final_result :
  forall {A B : Type} (f : A -> B) (g : B -> bool) (l : list A),
  existsb g (map f l) = existsb (fun x => g (f x)) l.
Proof.
  intros A B f g l. induction l as [| a t IH]; simpl; [ reflexivity | ].
  rewrite IH. reflexivity.
Qed.

(* ================================================================ *)
(* The explicit scan realises [RecordRun].                           *)
(* ================================================================ *)
Lemma scan_aux_zlength__spec_final_result : forall (t a : list Z) (lead : Z),
  Zlength (fst (scan_aux a t lead)) = Zlength t /\
  Zlength (snd (scan_aux a t lead)) = Zlength t.
Proof.
  induction t as [| x t' IH]; intros a lead; simpl.
  - split; reflexivity.
  - destruct (Z.ltb (Znth (lead - 1) a 0) (Znth (x - 1) a 0)).
    + destruct (IH a x) as [H1 H2]. simpl. rewrite !Zlength_cons. lia.
    + destruct (IH a lead) as [H1 H2]. simpl. rewrite !Zlength_cons. lia.
Qed.
Lemma scan_aux_step__spec_final_result :
  forall (t a : list Z) (lead i : Z) (L A : list Z),
  scan_aux a t lead = (L, A) ->
  0 <= i < Zlength t ->
  (Znth ((if Z.eqb i 0 then lead else Znth (i - 1) L 0) - 1) a 0 <
     Znth (Znth i t 1 - 1) a 0 /\
   Znth i L 0 = Znth i t 1 /\
   Znth i A 0 = Znth ((if Z.eqb i 0 then lead else Znth (i - 1) L 0) - 1) a 0) \/
  (Znth ((if Z.eqb i 0 then lead else Znth (i - 1) L 0) - 1) a 0 >=
     Znth (Znth i t 1 - 1) a 0 /\
   Znth i L 0 = (if Z.eqb i 0 then lead else Znth (i - 1) L 0) /\
   Znth i A 0 = 0).
Proof.
  induction t as [| x t' IH]; intros a lead i L A Hs Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    simpl in Hs.
    destruct (Z.ltb (Znth (lead - 1) a 0) (Znth (x - 1) a 0)) eqn:Hb.
    + destruct (scan_aux a t' x) as [L' A'] eqn:E. simpl in Hs.
      injection Hs as HL HA. subst L A.
      destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
      * subst i. simpl. rewrite !Znth0_cons. left.
        apply Z.ltb_lt in Hb. repeat split; try reflexivity; try lia.
      * assert (Hi1 : i > 0) by lia.
        replace (Z.eqb i 0) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite (Znth_cons 1 i x t') by lia.
        rewrite (Znth_cons 0 i x L') by lia.
        rewrite (Znth_cons 0 i (Znth (lead - 1) a 0) A') by lia.
        specialize (IH a x (i - 1) L' A' E ltac:(lia)).
        destruct (Z.eq_dec (i - 1) 0) as [He | He].
        -- rewrite He in IH. simpl in IH.
           replace (Znth (i - 1) (x :: L') 0) with x
             by (rewrite He; rewrite Znth0_cons; reflexivity).
           rewrite He. exact IH.
        -- replace (Z.eqb (i - 1) 0) with false in IH
             by (symmetry; apply Z.eqb_neq; lia).
           replace (Znth (i - 1) (x :: L') 0) with (Znth (i - 1 - 1) L' 0)
             by (rewrite (Znth_cons 0 (i - 1) x L') by lia; reflexivity).
           exact IH.
    + destruct (scan_aux a t' lead) as [L' A'] eqn:E. simpl in Hs.
      injection Hs as HL HA. subst L A.
      destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
      * subst i. simpl. rewrite !Znth0_cons. right.
        apply Z.ltb_ge in Hb. repeat split; try reflexivity; try lia.
      * assert (Hi1 : i > 0) by lia.
        replace (Z.eqb i 0) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite (Znth_cons 1 i x t') by lia.
        rewrite (Znth_cons 0 i lead L') by lia.
        rewrite (Znth_cons 0 i 0 A') by lia.
        specialize (IH a lead (i - 1) L' A' E ltac:(lia)).
        destruct (Z.eq_dec (i - 1) 0) as [He | He].
        -- rewrite He in IH. simpl in IH.
           replace (Znth (i - 1) (lead :: L') 0) with lead
             by (rewrite He; rewrite Znth0_cons; reflexivity).
           rewrite He. exact IH.
        -- replace (Z.eqb (i - 1) 0) with false in IH
             by (symmetry; apply Z.eqb_neq; lia).
           replace (Znth (i - 1) (lead :: L') 0) with (Znth (i - 1 - 1) L' 0)
             by (rewrite (Znth_cons 0 (i - 1) lead L') by lia; reflexivity).
           exact IH.
Qed.
Lemma perm_zlength__spec_final_result : forall {A : Type} (l l' : list A),
  Permutation l l' -> Zlength l = Zlength l'.
Proof.
  intros A l l' H. apply Permutation_length in H.
  rewrite !Zlength_correct. rewrite H. reflexivity.
Qed.
Lemma scan_run_is_record_run__spec_final_result : forall (a p : list Z),
  Zlength p = Zlength a -> 0 < Zlength a ->
  RecordRun a p (scan_leaders a p) (scan_add a p).
Proof.
  intros a p Hlen Hpos.
  destruct p as [| x t]; [ rewrite Zlength_nil in Hlen; lia | ].
  unfold scan_leaders, scan_add, scan_run.
  destruct (scan_aux a t x) as [L A] eqn:E.
  simpl fst. simpl snd.
  pose proof (scan_aux_zlength__spec_final_result t a x) as [HL HA].
  rewrite E in HL, HA. simpl in HL, HA.
  rewrite Zlength_cons in Hlen.
  unfold RecordRun.
  split; [ rewrite Zlength_cons; lia | ].
  split; [ rewrite Zlength_cons; lia | ].
  split; [ unfold Znth; simpl; reflexivity | ].
  split; [ unfold Znth; simpl; reflexivity | ].
  intros i Hi.
    assert (Hi1 : 0 <= i - 1 < Zlength t) by lia.
    pose proof (scan_aux_step__spec_final_result t a x (i - 1) L A E Hi1) as Hstep.
    assert (Hprev : Znth (i - 1) (x :: L) 1
                    = (if Z.eqb (i - 1) 0 then x else Znth (i - 1 - 1) L 0)).
    { destruct (Z.eq_dec (i - 1) 0) as [He | He].
      - rewrite He. simpl. rewrite Znth0_cons. reflexivity.
      - replace (Z.eqb (i - 1) 0) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite (Znth_cons 1 (i - 1) x L) by lia.
        apply Znth_indep. lia. }
    assert (Hprev0 : Znth (i - 1) (x :: L) 0
                    = (if Z.eqb (i - 1) 0 then x else Znth (i - 1 - 1) L 0)).
    { destruct (Z.eq_dec (i - 1) 0) as [He | He].
      - rewrite He. simpl. rewrite Znth0_cons. reflexivity.
      - replace (Z.eqb (i - 1) 0) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite (Znth_cons 0 (i - 1) x L) by lia. reflexivity. }
    unfold RecordStep.
    rewrite Hprev, Hprev0.
    rewrite (Znth_cons 0 i x L) by lia.
    rewrite (Znth_cons 1 i x t) by lia.
    rewrite (Znth_cons 0 i 0 A) by lia.
    exact Hstep.
Qed.
Lemma history_value_of_scan__spec_final_result : forall (a p : list Z),
  Permutation p (Zrange 1 (Zlength a + 1)) -> 0 < Zlength a ->
  HistoryValue a p (fold_right Z.add 0 (scan_add a p)).
Proof.
  intros a p Hperm Hpos. unfold HistoryValue. split; [ assumption | ].
  exists (scan_leaders a p), (scan_add a p). split; [ | reflexivity ].
  apply scan_run_is_record_run__spec_final_result; [ | assumption ].
  apply perm_zlength__spec_final_result in Hperm.
  rewrite Hperm. apply zlength_zrange__spec_final_result.
Qed.

(* ================================================================ *)
(* The scan total, rewritten as a per-occurrence indicator sum.      *)
(* ================================================================ *)
Lemma scan_add_occurrence_indicator__spec_final_result :
  forall (t a : list Z) (lead : Z),
  NoDup t ->
  fold_right Z.add 0 (snd (scan_aux a t lead)) =
  (if existsb (fun y => Z.ltb (Znth (lead - 1) a 0) (Znth (y - 1) a 0)) t
   then Znth (lead - 1) a 0 else 0)
  + fold_right Z.add 0
      (map (fun k =>
         if andb (Z.ltb (Znth (lead - 1) a 0) (Znth (k - 1) a 0))
            (andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t)) k)
                  (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t))
         then Znth (k - 1) a 0 else 0) t).
Proof.
  induction t as [| x t' IH]; intros a lead Hnd.
  - cbn [scan_aux snd existsb map fold_right]. lia.
  - inversion Hnd as [| x0 t0 Hnin Hnd' Heq]; subst.
    assert (Hne : forall k, In k t' -> Z.eqb x k = false).
    { intros k Hk. apply Z.eqb_neq. intros He. subst k. contradiction. }
    cbn [scan_aux existsb map fold_right filter hd].
    destruct (Z.ltb (Znth (lead - 1) a 0) (Znth (x - 1) a 0)) eqn:Hb.
    + cbn [snd fold_right].
      rewrite (IH a x Hnd').
      rewrite Z.leb_refl. cbn [hd]. rewrite Z.eqb_refl.
      rewrite Z.ltb_irrefl. cbn [orb andb].
      apply Z.ltb_lt in Hb.
      match goal with
      | |- _ = ?R =>
        match R with
        | context [ map ?g t' ] =>
          assert (Hs :
            fold_right Z.add 0
              (map (fun k =>
                 if andb (Z.ltb (Znth (x - 1) a 0) (Znth (k - 1) a 0))
                    (andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t')) k)
                          (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t'))
                 then Znth (k - 1) a 0 else 0) t')
            = fold_right Z.add 0 (map g t'))
        end
      end.
      * apply sum_map_ext__spec_final_result.
        intros k Hk.
        destruct (Z.leb (Znth (k - 1) a 0) (Znth (x - 1) a 0)) eqn:Hkx.
        -- apply Z.leb_le in Hkx.
           replace (Z.ltb (Znth (x - 1) a 0) (Znth (k - 1) a 0)) with false
             by (symmetry; apply Z.ltb_ge; lia).
           cbn [hd]. rewrite (Hne k Hk).
           destruct (Z.ltb (Znth (lead - 1) a 0) (Znth (k - 1) a 0));
             cbn [andb]; reflexivity.
        -- apply Z.leb_gt in Hkx.
           replace (Z.ltb (Znth (k - 1) a 0) (Znth (x - 1) a 0)) with false
             by (symmetry; apply Z.ltb_ge; lia).
           replace (Z.ltb (Znth (x - 1) a 0) (Znth (k - 1) a 0)) with true
             by (symmetry; apply Z.ltb_lt; lia).
           replace (Z.ltb (Znth (lead - 1) a 0) (Znth (k - 1) a 0)) with true
             by (symmetry; apply Z.ltb_lt; lia).
           cbn [orb andb]. reflexivity.
      * lia.
    + cbn [snd fold_right].
      rewrite (IH a lead Hnd').
      cbn [orb andb].
      apply Z.ltb_ge in Hb.
      match goal with
      | |- _ = ?R =>
        match R with
        | context [ map ?g t' ] =>
          assert (Hs :
            fold_right Z.add 0
              (map (fun k =>
                 if andb (Z.ltb (Znth (lead - 1) a 0) (Znth (k - 1) a 0))
                    (andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t')) k)
                          (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t'))
                 then Znth (k - 1) a 0 else 0) t')
            = fold_right Z.add 0 (map g t'))
        end
      end.
      * apply sum_map_ext__spec_final_result.
        intros k Hk.
        destruct (Z.leb (Znth (k - 1) a 0) (Znth (x - 1) a 0)) eqn:Hkx.
        -- apply Z.leb_le in Hkx.
           replace (Z.ltb (Znth (lead - 1) a 0) (Znth (k - 1) a 0)) with false
             by (symmetry; apply Z.ltb_ge; lia).
           cbn [andb]. reflexivity.
        -- apply Z.leb_gt in Hkx.
           replace (Z.ltb (Znth (k - 1) a 0) (Znth (x - 1) a 0)) with false
             by (symmetry; apply Z.ltb_ge; lia).
           cbn [orb]. reflexivity.
      * lia.
Qed.
Lemma scan_value_indicator__spec_final_result : forall (a p : list Z),
  NoDup p ->
  fold_right Z.add 0 (scan_add a p) =
  fold_right Z.add 0
    (map (fun k =>
       if andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k)
               (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)
       then Znth (k - 1) a 0 else 0) p).
Proof.
  intros a p Hnd. destruct p as [| x t]; [ reflexivity | ].
  inversion Hnd as [| x0 t0 Hnin Hnd' Heq]; subst.
  assert (Hne : forall k, In k t -> Z.eqb x k = false).
  { intros k Hk. apply Z.eqb_neq. intros He. subst k. contradiction. }
  unfold scan_add, scan_run. cbn [snd fold_right].
  rewrite (scan_add_occurrence_indicator__spec_final_result t a x Hnd').
  cbn [map fold_right filter hd existsb].
  rewrite Z.leb_refl. cbn [hd]. rewrite Z.eqb_refl.
  rewrite Z.ltb_irrefl. cbn [orb andb].
  match goal with
  | |- _ = ?R =>
    match R with
    | context [ map ?g t ] =>
      assert (Hs :
        fold_right Z.add 0
          (map (fun k =>
             if andb (Z.ltb (Znth (x - 1) a 0) (Znth (k - 1) a 0))
                (andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t)) k)
                      (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) t))
             then Znth (k - 1) a 0 else 0) t)
        = fold_right Z.add 0 (map g t))
    end
  end.
  - apply sum_map_ext__spec_final_result.
    intros k Hk.
    destruct (Z.leb (Znth (k - 1) a 0) (Znth (x - 1) a 0)) eqn:Hkx.
    + apply Z.leb_le in Hkx.
      replace (Z.ltb (Znth (x - 1) a 0) (Znth (k - 1) a 0)) with false
        by (symmetry; apply Z.ltb_ge; lia).
      cbn [hd]. rewrite (Hne k Hk). cbn [andb]. reflexivity.
    + apply Z.leb_gt in Hkx.
      replace (Z.ltb (Znth (k - 1) a 0) (Znth (x - 1) a 0)) with false
        by (symmetry; apply Z.ltb_ge; lia).
      replace (Z.ltb (Znth (x - 1) a 0) (Znth (k - 1) a 0)) with true
        by (symmetry; apply Z.ltb_lt; lia).
      cbn [orb andb]. reflexivity.
  - lia.
Qed.
Lemma existsb_perm__spec_final_result : forall {A : Type} (f : A -> bool) (l l' : list A),
  Permutation l l' -> existsb f l = existsb f l'.
Proof.
  intros A f l l' H. induction H; simpl.
  - reflexivity.
  - rewrite IHPermutation. reflexivity.
  - destruct (f x); destruct (f y); reflexivity.
  - rewrite IHPermutation1. assumption.
Qed.
Lemma filter_ext__spec_final_result : forall {A : Type} (f g : A -> bool) (l : list A),
  (forall x, f x = g x) -> filter f l = filter g l.
Proof.
  intros A f g l H. induction l as [| a t IH]; simpl; [ reflexivity | ].
  rewrite H. destruct (g a); [ f_equal | ]; assumption.
Qed.
Lemma hd_map__spec_final_result : forall (f : Z -> Z) (l : list Z),
  f 0 = 0 -> hd 0 (map f l) = f (hd 0 l).
Proof.
  intros f l Hf. destruct l as [| x t]; simpl; [ auto | reflexivity ].
Qed.
Lemma sum_eqb_indicator__spec_final_result : forall (C : list Z) (h : Z),
  NoDup C -> In h C ->
  fold_right Z.add 0 (map (fun c => if Z.eqb h c then 1 else 0) C) = 1.
Proof.
  intros C. induction C as [| c t IH]; intros h Hnd Hin; simpl in *; [ contradiction | ].
  inversion Hnd as [| c0 t0 Hnin Hnd' Heq]; subst.
  destruct Hin as [Hin | Hin].
  - subst h. rewrite Z.eqb_refl.
    assert (Hz : fold_right Z.add 0 (map (fun c0 => if Z.eqb c c0 then 1 else 0) t) = 0).
    { rewrite (sum_map_ext__spec_final_result _ (fun _ : Z => 0)).
      - apply sum_map_zero__spec_final_result.
      - intros y Hy. destruct (Z.eqb c y) eqn:He; [ | reflexivity ].
        apply Z.eqb_eq in He. subst y. contradiction. }
    lia.
  - replace (Z.eqb h c) with false.
    + rewrite (IH h Hnd' Hin). lia.
    + symmetry. apply Z.eqb_neq. intros He. subst h. contradiction.
Qed.

(* ================================================================ *)
(* Counting the orderings in which one class member comes first.     *)
(* ================================================================ *)
Lemma swap_count__spec_final_result :
  forall (K : list Z) (ps : list (list Z)) (sigma : Z -> Z) (g : Z -> bool) (c k : Z),
  NoDup K -> NoDup ps ->
  (forall p, In p ps <-> Permutation p K) ->
  (forall z, sigma (sigma z) = z) ->
  (forall z, In z K -> In (sigma z) K) ->
  sigma 0 = 0 ->
  (forall y, g (sigma y) = g y) ->
  sigma k = c ->
  Zlength (filter (fun p => Z.eqb (hd 0 (filter g p)) c) ps)
  = Zlength (filter (fun p => Z.eqb (hd 0 (filter g p)) k) ps).
Proof.
  intros K ps sigma g c k HndK Hndps Hps Hinv HinK Hs0 Hg Hsk.
  assert (Hinj : forall u w : Z, sigma u = sigma w -> u = w).
  { intros u w H. rewrite <- (Hinv u), <- (Hinv w), H. reflexivity. }
  assert (Hd : forall l : list Z, map sigma (map sigma l) = l).
  { induction l as [| z tl IHl]; simpl; [ reflexivity | rewrite Hinv, IHl; reflexivity ]. }
  assert (HinjL : forall u w : list Z, map sigma u = map sigma w -> u = w).
  { intros u w H.
    rewrite <- (Hd u). rewrite H. apply Hd. }
  assert (HpermK : Permutation (map sigma K) K).
  { apply NoDup_Permutation.
    - apply nodup_map__spec_final_result; [ assumption | intros u w _ _ H; apply Hinj; assumption ].
    - assumption.
    - intros z. split.
      + intros Hz. rewrite in_map_iff in Hz. destruct Hz as [w [Hw Hw2]].
        subst z. apply HinK. assumption.
      + intros Hz. rewrite in_map_iff. exists (sigma z). split; [ apply Hinv | ].
        apply HinK. assumption. }
  assert (Hmem : forall q, In q ps -> In (map sigma q) ps).
  { intros q Hq. apply Hps. apply Hps in Hq.
    eapply Permutation_trans; [ apply Permutation_map; exact Hq | exact HpermK ]. }
  assert (Hpermps : Permutation ps (map (map sigma) ps)).
  { apply NoDup_Permutation.
    - assumption.
    - apply nodup_map__spec_final_result; [ assumption | intros u w _ _ H; apply HinjL; assumption ].
    - intros q. split.
      + intros Hq. rewrite in_map_iff. exists (map sigma q). split.
        * apply Hd.
        * apply Hmem. assumption.
      + intros Hq. rewrite in_map_iff in Hq. destruct Hq as [q' [Hq' Hq'2]].
        subst q. apply Hmem. assumption. }
  assert (Hstep : forall p,
    Z.eqb (hd 0 (filter g (map sigma p))) c = Z.eqb (hd 0 (filter g p)) k).
  { intros p.
    rewrite filter_map__spec_final_result.
    rewrite (filter_ext__spec_final_result (fun x => g (sigma x)) g p Hg).
    rewrite hd_map__spec_final_result by assumption.
    destruct (Z.eq_dec (hd 0 (filter g p)) k) as [He | He].
    - rewrite He. rewrite Hsk. rewrite !Z.eqb_refl. reflexivity.
    - replace (Z.eqb (hd 0 (filter g p)) k) with false
        by (symmetry; apply Z.eqb_neq; assumption).
      apply Z.eqb_neq. intros Hc.
      apply He. apply Hinj. rewrite Hc, Hsk. reflexivity. }
  rewrite (perm_zlength__spec_final_result _ _
             (perm_filter__spec_final_result _ _ _ Hpermps)).
  rewrite filter_map__spec_final_result.
  rewrite zlength_map__spec_final_result.
  f_equal. apply filter_ext__spec_final_result. exact Hstep.
Qed.
Lemma partition_count__spec_final_result :
  forall (K : list Z) (ps : list (list Z)) (g : Z -> bool) (k0 : Z),
  (forall p, In p ps <-> Permutation p K) ->
  NoDup (filter g K) ->
  In k0 (filter g K) ->
  fold_right Z.add 0
    (map (fun c => Zlength (filter (fun p => Z.eqb (hd 0 (filter g p)) c) ps))
         (filter g K))
  = Zlength ps.
Proof.
  intros K ps g k0 Hps HndC Hk0.
  rewrite (sum_map_ext__spec_final_result _
    (fun c => fold_right Z.add 0 (map (fun p => if Z.eqb (hd 0 (filter g p)) c then 1 else 0) ps))).
  - rewrite (sum_swap__spec_final_result
      (fun c p => if Z.eqb (hd 0 (filter g p)) c then 1 else 0) (filter g K) ps).
    rewrite (sum_map_ext__spec_final_result _ (fun _ : list Z => 1)).
    + rewrite sum_map_const__spec_final_result. lia.
    + intros p Hp.
      apply filter_In in Hk0. destruct Hk0 as [Hk0K Hk0g].
      assert (HpK : Permutation p K) by (apply Hps; assumption).
      assert (HKp : Permutation K p) by (apply Permutation_sym; assumption).
      assert (Hin0 : In k0 (filter g p)).
      { apply filter_In. split; [ | assumption ].
        eapply Permutation_in; [ exact HKp | assumption ]. }
      destruct (filter g p) as [| h r] eqn:Ef; [ contradiction | ].
      assert (Hh : In h (filter g p)) by (rewrite Ef; left; reflexivity).
      apply filter_In in Hh. destruct Hh as [Hhp Hhg].
      cbn [hd].
      apply sum_eqb_indicator__spec_final_result; [ assumption | ].
      apply filter_In. split; [ | assumption ].
      eapply Permutation_in; [ exact HpK | assumption ].
  - intros c Hc. rewrite sum_indicator__spec_final_result. lia.
Qed.
Lemma nodup_filter__spec_final_result : forall {A : Type} (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof.
  intros A f l. induction l as [| a t IH]; intros Hnd; simpl; [ assumption | ].
  inversion Hnd as [| a0 t0 Hnin Hnd' Heq]; subst.
  destruct (f a); [ | apply IH; assumption ].
  constructor; [ | apply IH; assumption ].
  intros Hin. apply filter_In in Hin. destruct Hin. contradiction.
Qed.
Lemma perms_of_all_permutations__spec_final_result : forall (a : list Z),
  AllPermutations (Zlength a) (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1))).
Proof.
  intros a.
  assert (Hlen : length (Zrange 1 (Zlength a + 1)) = Z.to_nat (Zlength a)).
  { pose proof (zlength_zrange__spec_final_result a) as H.
    rewrite Zlength_correct in H. lia. }
  unfold AllPermutations. split.
  - apply perms_of_nodup__spec_final_result; [ apply NoDup_Zrange | assumption ].
  - intros p. apply perms_of_in__spec_final_result. assumption.
Qed.
Lemma count_orderings_first_in_class__spec_final_result :
  forall (a : list Z) (k : Z),
  In k (Zrange 1 (Zlength a + 1)) ->
  count_ge a (Znth (k - 1) a 0) *
  Zlength (filter (fun p => Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k)
                  (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1))))
  = Zfact (Zlength a).
Proof.
  intros a k HkK.
  pose proof (perms_of_all_permutations__spec_final_result a) as [Hndps Hps].
  assert (Hlen : length (Zrange 1 (Zlength a + 1)) = Z.to_nat (Zlength a)).
  { pose proof (zlength_zrange__spec_final_result a) as H.
    rewrite Zlength_correct in H. lia. }
  assert (Hzps : Zlength (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1)))
                 = Zfact (Zlength a)).
  { unfold Zfact. apply perms_of_zlength__spec_final_result. assumption. }
  assert (HgK : Z.leb (Znth (k - 1) a 0) (Znth (k - 1) a 0) = true) by apply Z.leb_refl.
  assert (HkC : In k (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0))
                             (Zrange 1 (Zlength a + 1)))).
  { apply filter_In. split; assumption. }
  assert (HndC : NoDup (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0))
                               (Zrange 1 (Zlength a + 1)))).
  { apply nodup_filter__spec_final_result. apply NoDup_Zrange. }
  pose proof (partition_count__spec_final_result
                (Zrange 1 (Zlength a + 1))
                (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1)))
                (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) k Hps HndC HkC) as Hpart.
  rewrite (sum_map_ext__spec_final_result _
    (fun _ : Z =>
       Zlength (filter (fun p => Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k)
                       (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1)))))) in Hpart.
  - rewrite sum_map_const__spec_final_result in Hpart.
    rewrite Hzps in Hpart. rewrite <- Hpart.
    f_equal. unfold count_ge.
    rewrite <- (zrange_map_znth__spec_final_result a) at 1.
    rewrite filter_map__spec_final_result.
    rewrite zlength_map__spec_final_result. reflexivity.
  - intros c Hc.
    apply filter_In in Hc. destruct Hc as [HcK Hcg].
    assert (Hc1 : 1 <= c) by (apply In_Zrange in HcK; lia).
    assert (Hk1 : 1 <= k) by (apply In_Zrange in HkK; lia).
    apply (swap_count__spec_final_result
             (Zrange 1 (Zlength a + 1))
             (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1)))
             (fun z => if Z.eqb z c then k else if Z.eqb z k then c else z)
             (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) c k).
    + apply NoDup_Zrange.
    + assumption.
    + assumption.
    + intros z. destruct (Z.eqb z c) eqn:H1; cbv beta iota.
      * destruct (Z.eqb k c) eqn:H2; cbv beta iota.
        -- apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. congruence.
        -- destruct (Z.eqb k k) eqn:H3; cbv beta iota.
           ++ apply Z.eqb_eq in H1. congruence.
           ++ rewrite Z.eqb_refl in H3. discriminate.
      * destruct (Z.eqb z k) eqn:H2; cbv beta iota.
        -- destruct (Z.eqb c c) eqn:H3; cbv beta iota.
           ++ apply Z.eqb_eq in H2. congruence.
           ++ rewrite Z.eqb_refl in H3. discriminate.
        -- rewrite H1, H2. cbv beta iota. reflexivity.
    + intros z Hz. destruct (Z.eqb z c); cbv beta iota; [ assumption | ].
      destruct (Z.eqb z k); cbv beta iota; assumption.
    + replace (Z.eqb 0 c) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb 0 k) with false by (symmetry; apply Z.eqb_neq; lia).
      cbv beta iota. reflexivity.
    + intros y. destruct (Z.eqb y c) eqn:Hyc; cbv beta iota.
      * apply Z.eqb_eq in Hyc. subst y. rewrite Hcg. exact HgK.
      * destruct (Z.eqb y k) eqn:Hyk; cbv beta iota.
        -- apply Z.eqb_eq in Hyk. subst y. rewrite Hcg. symmetry. exact HgK.
        -- reflexivity.
    + destruct (Z.eqb k c) eqn:Hkc; cbv beta iota.
      * apply Z.eqb_eq in Hkc. assumption.
      * rewrite Z.eqb_refl. cbv beta iota. reflexivity.
Qed.
Lemma zlength_pos_of_In__spec_final_result : forall {A : Type} (x : A) (l : list A),
  In x l -> 0 < Zlength l.
Proof.
  intros A x l Hin. destruct l as [| y t]; [ contradiction | ].
  rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia.
Qed.
Lemma existsb_zrange_values__spec_final_result : forall (a : list Z) (v : Z),
  existsb (fun y => Z.ltb v (Znth (y - 1) a 0)) (Zrange 1 (Zlength a + 1))
  = existsb (fun w => Z.ltb v w) a.
Proof.
  intros a v.
  rewrite <- (zrange_map_znth__spec_final_result a) at 2.
  rewrite existsb_map__spec_final_result. reflexivity.
Qed.
Lemma sum_over_perms_is_contrib_sum__spec_final_result : forall (a : list Z),
  fold_right Z.add 0
    (map (fun p => fold_right Z.add 0 (scan_add a p))
         (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1))))
  = fold_right Z.add 0 (contrib_list a).
Proof.
  intros a.
  pose proof (perms_of_all_permutations__spec_final_result a) as [Hndps Hps].
  transitivity (fold_right Z.add 0
    (map (fun p => fold_right Z.add 0
       (map (fun k =>
          if andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k)
                  (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0))
                           (Zrange 1 (Zlength a + 1)))
          then Znth (k - 1) a 0 else 0) (Zrange 1 (Zlength a + 1))))
         (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1))))).
  { apply sum_map_ext__spec_final_result. intros p Hp.
    apply Hps in Hp.
    assert (Hndp : NoDup p).
    { apply (Permutation_NoDup (l := Zrange 1 (Zlength a + 1))).
      - apply Permutation_sym. assumption.
      - apply NoDup_Zrange. }
    rewrite (scan_value_indicator__spec_final_result a p Hndp).
    transitivity (fold_right Z.add 0
      (map (fun k =>
         if andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k)
                 (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0))
                          (Zrange 1 (Zlength a + 1)))
         then Znth (k - 1) a 0 else 0) p)).
    - apply sum_map_ext__spec_final_result. intros k Hk.
      rewrite (existsb_perm__spec_final_result _ p (Zrange 1 (Zlength a + 1)) Hp).
      reflexivity.
    - apply sum_perm__spec_final_result. apply Permutation_map. assumption. }
  rewrite (sum_swap__spec_final_result
    (fun p k =>
       if andb (Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k)
               (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0))
                        (Zrange 1 (Zlength a + 1)))
       then Znth (k - 1) a 0 else 0)
    (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1)))
    (Zrange 1 (Zlength a + 1))).
  transitivity (fold_right Z.add 0
    (map (fun k => contrib a (Znth (k - 1) a 0)) (Zrange 1 (Zlength a + 1)))).
  - apply sum_map_ext__spec_final_result. intros k Hk.
    assert (Hina : In (Znth (k - 1) a 0) a).
    { pose proof (in_map (fun y => Znth (y - 1) a 0)
                    (Zrange 1 (Zlength a + 1)) k Hk) as Hm.
      rewrite zrange_map_znth__spec_final_result in Hm. exact Hm. }
    unfold contrib.
    rewrite <- (existsb_zrange_values__spec_final_result a (Znth (k - 1) a 0)).
    destruct (existsb (fun y => Z.ltb (Znth (k - 1) a 0) (Znth (y - 1) a 0))
                      (Zrange 1 (Zlength a + 1))) eqn:He.
    + rewrite (sum_map_ext__spec_final_result _
        (fun p =>
           if Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k
           then Znth (k - 1) a 0 else 0)).
      * rewrite sum_indicator__spec_final_result.
        pose proof (count_orderings_first_in_class__spec_final_result a k Hk) as Hcnt.
        assert (Hcg : 0 < count_ge a (Znth (k - 1) a 0)).
        { unfold count_ge.
          apply (zlength_pos_of_In__spec_final_result (Znth (k - 1) a 0)).
          apply filter_In. split; [ assumption | apply Z.leb_refl ]. }
        f_equal. symmetry.
        replace (Zfact (Zlength a))
          with (Zlength (filter (fun p =>
                 Z.eqb (hd 0 (filter (fun y => Z.leb (Znth (k - 1) a 0) (Znth (y - 1) a 0)) p)) k)
                 (perms_of (Z.to_nat (Zlength a)) (Zrange 1 (Zlength a + 1))))
                * count_ge a (Znth (k - 1) a 0)) by lia.
        apply Z.div_mul. lia.
      * intros p Hp. rewrite andb_true_r. reflexivity.
    + rewrite (sum_map_ext__spec_final_result _ (fun _ : list Z => 0)).
      * apply sum_map_zero__spec_final_result.
      * intros p Hp. rewrite andb_false_r. reflexivity.
  - unfold contrib_list.
    transitivity (fold_right Z.add 0
      (map (contrib a) (map (fun y => Znth (y - 1) a 0) (Zrange 1 (Zlength a + 1))))).
    + rewrite map_map. reflexivity.
    + rewrite zrange_map_znth__spec_final_result. reflexivity.
Qed.
Lemma contrib_sum_perm_invariant__spec_final_result : forall (l l' : list Z),
  Permutation l l' ->
  fold_right Z.add 0 (contrib_list l) = fold_right Z.add 0 (contrib_list l').
Proof.
  intros l l' Hperm.
  assert (Hcontrib : forall v, contrib l v = contrib l' v).
  { intros v. unfold contrib, count_ge.
    rewrite (existsb_perm__spec_final_result _ l l' Hperm).
    rewrite (perm_zlength__spec_final_result _ _ (perm_filter__spec_final_result _ _ _ Hperm)).
    rewrite (perm_zlength__spec_final_result _ _ Hperm).
    reflexivity. }
  unfold contrib_list.
  transitivity (fold_right Z.add 0 (map (contrib l') l)).
  - apply sum_map_ext__spec_final_result. intros v Hv. apply Hcontrib.
  - apply sum_perm__spec_final_result. apply Permutation_map. assumption.
Qed.
Lemma spec_of_contrib_prefix__spec_final_result :
  forall (values l1 : list Z) (i total : Z),
  0 < Zlength values ->
  Permutation values l1 ->
  i = Zlength l1 ->
  ContribPrefixSum l1 i total ->
  Spec values total.
Proof.
  intros values l1 i total Hpos Hperm Hi Hcp.
  pose proof (perms_of_all_permutations__spec_final_result values) as Hall.
  destruct Hall as [Hnd Hin].
  unfold Spec.
  exists (perms_of (Z.to_nat (Zlength values)) (Zrange 1 (Zlength values + 1))).
  exists (fun p => fold_right Z.add 0 (scan_add values p)).
  split; [ split; assumption | ].
  split.
  - intros p Hp. apply history_value_of_scan__spec_final_result;
      [ apply Hin; assumption | assumption ].
  - unfold ContribPrefixSum in Hcp.
    rewrite sum_over_perms_is_contrib_sum__spec_final_result.
    rewrite (contrib_sum_perm_invariant__spec_final_result values l1 Hperm).
    rewrite Hcp. f_equal.
    replace (sublist 0 i (contrib_list l1)) with (contrib_list l1); [ reflexivity | ].
    symmetry. apply sublist_self.
    unfold contrib_list. rewrite zlength_map__spec_final_result. lia.
Qed.
