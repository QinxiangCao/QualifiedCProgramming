Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition IsPositiveGcd (d : Z) (xs : list Z) : Prop :=
  d > 0 /\ xs <> [] /\ d = fold_right Z.gcd 0 xs.

Definition ExpandedMultiset (vals freq : list Z) (s : list Z) : Prop :=
  Zlength s = (fold_right Z.add 0) freq /\
  Forall (fun x => In x vals) s /\
  forall i, 0 <= i < Zlength vals ->
    (#(fun j : Z => 0 <= j < Zlength s /\ Znth j s 0 = (Znth i vals 0))) = Znth i freq 0.
Definition ValidSubsetPair (s : list Z) (ab : list Z * list Z) (term : Z) : Prop :=
  let ' (A, B) := ab in Zlength A = Zlength s /\ Zlength B = Zlength s /\
  Forall (fun x => x = 0 \/ x = 1) A /\ Forall (fun x => x = 0 \/ x = 1) B /\
  (forall i, 0 <= i < Zlength s -> Znth i B 0 <= Znth i A 0) /\
  (fold_right Z.add 0) B = (fold_right Z.add 0) A - 1 /\
  (exists g, IsPositiveGcd g (map snd (filter (fun q => Z.eqb (fst q) 1) (combine A s))) /\ g = 1) /\
  term = (fold_right Z.add 0) (map snd (filter (fun q => Z.eqb (fst q) 1) (combine A s))) *
          (fold_right Z.add 0) (map snd (filter (fun q => Z.eqb (fst q) 1) (combine B s))).
Definition AllSubsetPairs (s : list Z) (ps : list (list Z * list Z)) : Prop :=
  NoDup ps /\ forall q, In q ps <-> exists term, ValidSubsetPair s q term.
(* The largest value the input mentions; main seeds its running maximum with 1. *)
Definition maximum_value (vals : list Z) : Z :=
  fold_right Z.max 1 vals.

(* How the three per-value tables main hands to the solver represent the input:
   the total frequency of each value and its first and second moments. *)
Definition aggregate_arrays (vals freq cnts sums squares : list Z) (maxv : Z) : Prop :=
  Zlength cnts = maxv + 1 /\ Zlength sums = maxv + 1 /\ Zlength squares = maxv + 1 /\
  (forall i, 0 <= i < Zlength vals ->
     Znth (Znth i vals 0) cnts 0 = Znth i freq 0 /\
     Znth (Znth i vals 0) sums 0 =
       (Znth i vals 0 * Znth i freq 0) mod 998244353 /\
     Znth (Znth i vals 0) squares 0 =
       (Znth i vals 0 * Znth i vals 0 * Znth i freq 0) mod 998244353) /\
  (forall v, 0 <= v <= maxv -> ~ In v vals ->
     Znth v cnts 0 = 0 /\ Znth v sums 0 = 0 /\ Znth v squares 0 = 0).

Definition Pre (vals freq : list Z) : Prop :=
  (* Stated explicitly in the P096 solver Require, so dropped here:
       1 <= Zlength vals <= 100000 /\
       Zlength freq = Zlength vals /\
       Forall (fun x => 1 <= x <= 100000) vals /\
       Forall (fun x => 1 <= x <= 1000000000) freq  *)
  NoDup vals.

Definition Spec (vals freq : list Z) (out : Z) : Prop :=
  exists s ps f, ExpandedMultiset vals freq s /\ AllSubsetPairs s ps /\
   (forall q, In q ps -> ValidSubsetPair s q (f q)) /\ out = (fold_right Z.add 0) (map f ps) mod 998244353.

(* ------------------------------------------------------------------ *)
(* Helper-level mathematics used by the powmod / pool_sum contracts.   *)
(* ------------------------------------------------------------------ *)

(* Modular exponentiation, the value powmod is required to return. *)
Definition pow_mod (b e : Z) : Z := (b ^ e) mod 998244353.

(* Closed form, modulo 998244353, of
     W(P) = sum over all sub-multisets A of P of (|A| - 1) * (sum A)^2
   expressed through k = |P|, S = sum P and S2 = sum of squares of P.
   Only k has to be exact; S and S2 may already be reduced modulo p.
   At k = 2 the cross coefficient degenerates to 2^(k-2): the extra term
   carries the factor (k - 2) = 0, and Z.pow with a negative exponent is 0,
   which is why the C code may guard that term with k >= 3. *)
Definition pool_closed_form (k S S2 : Z) : Z :=
  if k <? 2 then 0
  else (S2 * 2 ^ (k - 2) * (k - 1)
        + (S * S - S2) * (2 ^ (k - 2) + (k - 2) * 2 ^ (k - 3))) mod 998244353.

(* ------------------------------------------------------------------ *)
(* Internal state of the sieve: canonical multiset, sub-multiset       *)
(* weights, exact-gcd weights and the running loop aggregates.         *)
(* ------------------------------------------------------------------ *)

(* The canonical expansion of the input: each value repeated as often as
   its frequency says.  It satisfies ExpandedMultiset, and any other
   witness of ExpandedMultiset is a permutation of it. *)
Fixpoint expand (vals freq : list Z) : list Z :=
  match vals, freq with
  | v :: vs, f :: fs => repeat v (Z.to_nat f) ++ expand vs fs
  | _, _ => nil
  end.

(* Every sub-multiset of a list, keeping multiplicity. *)
Fixpoint sub_multisets (l : list Z) : list (list Z) :=
  match l with
  | nil => nil :: nil
  | x :: t => map (cons x) (sub_multisets t) ++ sub_multisets t
  end.

(* The contribution of one selected sub-multiset A: pairing A with each of
   the |A| ways of dropping one element collapses to (|A| - 1) * (sum A)^2. *)
Definition subset_weight (A : list Z) : Z :=
  (Zlength A - 1) * (fold_right Z.add 0 A) ^ 2.

(* W(P): the total weight of every sub-multiset of a pool P. *)
Definition subset_weight_sum (P : list Z) : Z :=
  fold_right Z.add 0 (map subset_weight (sub_multisets P)).

Definition divisible_pool (s : list Z) (d : Z) : list Z :=
  filter (fun x => Z.eqb (x mod d) 0) s.

(* G(d): the weight of the pool of input elements divisible by d. *)
Definition pool_weight (vals freq : list Z) (d : Z) : Z :=
  subset_weight_sum (divisible_pool (expand vals freq) d).

(* F(d): the weight of the sub-multisets whose gcd is exactly d.  The empty
   sub-multiset has gcd 0, so it is excluded for every d >= 1. *)
Definition exact_gcd_weight (vals freq : list Z) (d : Z) : Z :=
  fold_right Z.add 0
    (map subset_weight
       (filter (fun A => Z.eqb (fold_right Z.gcd 0 A) d)
               (sub_multisets (expand vals freq)))).

(* The table entries at the first u multiples of d. *)
Definition multiple_prefix_sum (l : list Z) (d u : Z) : Z :=
  sum_range 1 u (fun i => Znth (i * d) l 0).

Definition PowmodState (b0 e0 b e r : Z) : Prop :=
  pow_mod b0 e0 = (r * pow_mod b e) mod 998244353.

Definition AnsExactPrefix (vals freq : list Z) (maxv : Z)
                          (anslist : list Z) (d : Z) : Prop :=
  forall w, d < w <= maxv ->
    Znth w anslist 0 = (exact_gcd_weight vals freq w) mod 998244353.

Definition PoolAggregate (cnts sums squares : list Z)
                         (d u k S S2 : Z) : Prop :=
  k = multiple_prefix_sum cnts d u /\
  S = (multiple_prefix_sum sums d u) mod 998244353 /\
  S2 = (multiple_prefix_sum squares d u) mod 998244353.

Definition PeelState (vals freq : list Z) (d u cur : Z) : Prop :=
  cur = (pool_weight vals freq d
         - sum_range 2 u (fun i => exact_gcd_weight vals freq (i * d)))
        mod 998244353.

Require Import Coq.ZArith.Zquot.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Bool.Bool.
Lemma land_one_shiftr_bridge__powmod_modexp : forall e : Z,
  0 <= e ->
  Z.land e 1 = e mod 2 /\ Z.shiftr e 1 = e / 2 /\ 0 <= e / 2 <= e.
Proof.
  intros e He.
  assert (Hl : Z.land e 1 = e mod 2).
  { transitivity (Z.land e (Z.ones 1)).
    - reflexivity.
    - rewrite Z.land_ones by lia. rewrite Z.pow_1_r. reflexivity. }
  assert (Hs : Z.shiftr e 1 = e / 2).
  { rewrite Z.shiftr_div_pow2 by lia. rewrite Z.pow_1_r. reflexivity. }
  split; [ exact Hl | split; [ exact Hs | ] ].
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; lia.
Qed.
Lemma rem_small_pos__powmod_modexp : forall b : Z,
  0 <= b -> b < 998244353 -> Z.rem b 998244353 = b.
Proof. intros b H1 H2. apply Z.rem_small. lia. Qed.
Lemma rem_bound__powmod_modexp : forall a : Z,
  0 <= a -> 0 <= Z.rem a 998244353 < 998244353.
Proof. intros a Ha. apply Z.rem_bound_pos; lia. Qed.
Lemma shiftr_bound__powmod_modexp : forall e : Z,
  0 <= e -> 0 <= Z.shiftr e 1 <= e.
Proof.
  intros e He.
  destruct (land_one_shiftr_bridge__powmod_modexp e He) as [_ [Hs Hd]].
  rewrite Hs. lia.
Qed.
Lemma pow_mod_odd_step__powmod_modexp : forall b e : Z,
  0 <= e -> Z.land e 1 <> 0 ->
  pow_mod b e = (b * pow_mod ((b * b) mod 998244353) (e / 2)) mod 998244353.
Proof.
  intros b e He Hodd.
  destruct (land_one_shiftr_bridge__powmod_modexp e He) as [Hl [Hs Hd]].
  rewrite Hl in Hodd.
  pose proof (Z.mod_pos_bound e 2 ltac:(lia)) as Hb.
  pose proof (Z.div_mod e 2 ltac:(lia)) as Hdm.
  remember (e / 2) as q eqn:Hq.
  assert (Heq : e = 2 * q + 1) by lia.
  assert (Hq0 : 0 <= q) by lia.
  unfold pow_mod.
  rewrite <- (Zpower_mod (b * b) q 998244353) by lia.
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite Heq.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  rewrite Z.pow_mul_r by lia.
  rewrite <- Z.pow_2_r.
  f_equal. ring.
Qed.
Lemma pow_mod_even_step__powmod_modexp : forall b e : Z,
  0 <= e -> Z.land e 1 = 0 ->
  pow_mod b e = pow_mod ((b * b) mod 998244353) (e / 2).
Proof.
  intros b e He Hev.
  destruct (land_one_shiftr_bridge__powmod_modexp e He) as [Hl [Hs Hd]].
  rewrite Hl in Hev.
  pose proof (Z.div_mod e 2 ltac:(lia)) as Hdm.
  remember (e / 2) as q eqn:Hq.
  assert (Heq : e = 2 * q) by lia.
  assert (Hq0 : 0 <= q) by lia.
  unfold pow_mod.
  rewrite <- (Zpower_mod (b * b) q 998244353) by lia.
  rewrite Heq.
  rewrite Z.pow_mul_r by lia.
  rewrite <- Z.pow_2_r.
  reflexivity.
Qed.
Lemma powmod_init_state__powmod_modexp : forall b0 e0 : Z,
  0 <= b0 -> b0 < 998244353 ->
  PowmodState b0 e0 (Z.rem b0 998244353) e0 1.
Proof.
  intros b0 e0 H1 H2.
  unfold PowmodState.
  rewrite (rem_small_pos__powmod_modexp b0 H1 H2).
  rewrite Z.mul_1_l.
  unfold pow_mod.
  rewrite Zmod_mod. reflexivity.
Qed.
Lemma powmod_odd_state__powmod_modexp : forall b0 e0 b e r : Z,
  0 <= b -> 0 <= r -> 0 <= e -> Z.land e 1 <> 0 ->
  PowmodState b0 e0 b e r ->
  PowmodState b0 e0 (Z.rem (b * b) 998244353) (Z.shiftr e 1) (Z.rem (r * b) 998244353).
Proof.
  intros b0 e0 b e r Hb Hr He Hodd HS.
  destruct (land_one_shiftr_bridge__powmod_modexp e He) as [Hl [Hs Hd]].
  unfold PowmodState in HS |- *.
  rewrite Hs.
  rewrite (Z.rem_mod_nonneg (b * b) 998244353) by nia.
  rewrite (Z.rem_mod_nonneg (r * b) 998244353) by nia.
  rewrite HS.
  rewrite (pow_mod_odd_step__powmod_modexp b e He Hodd).
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  f_equal. ring.
Qed.
Lemma powmod_even_state__powmod_modexp : forall b0 e0 b e r : Z,
  0 <= b -> 0 <= e -> Z.land e 1 = 0 ->
  PowmodState b0 e0 b e r ->
  PowmodState b0 e0 (Z.rem (b * b) 998244353) (Z.shiftr e 1) r.
Proof.
  intros b0 e0 b e r Hb He Hev HS.
  destruct (land_one_shiftr_bridge__powmod_modexp e He) as [Hl [Hs Hd]].
  unfold PowmodState in HS |- *.
  rewrite Hs.
  rewrite (Z.rem_mod_nonneg (b * b) 998244353) by nia.
  rewrite HS.
  rewrite (pow_mod_even_step__powmod_modexp b e He Hev).
  reflexivity.
Qed.
Lemma powmod_final_state__powmod_modexp : forall b0 e0 b e r : Z,
  PowmodState b0 e0 b e r -> e <= 0 -> 0 <= e -> 0 <= r -> r < 998244353 ->
  r = pow_mod b0 e0.
Proof.
  intros b0 e0 b e r HS H1 H2 H3 H4.
  assert (He : e = 0) by lia.
  unfold PowmodState, pow_mod in HS.
  rewrite He in HS.
  rewrite Z.pow_0_r in HS.
  rewrite (Z.mod_1_l 998244353) in HS by lia.
  rewrite Z.mul_1_r in HS.
  rewrite (Z.mod_small r 998244353) in HS by lia.
  unfold pow_mod. symmetry. exact HS.
Qed.
Lemma rem_nonneg_is_mod__pool_sum_closed_form :
  forall a m, 0 <= a -> 0 < m -> Z.rem a m = a mod m.
Proof.
  intros a m Ha Hm. apply Z.rem_mod_nonneg; lia.
Qed.
Lemma rem_ge__pool_sum_closed_form :
  forall a m, 0 <= a -> 0 < m -> 0 <= Z.rem a m.
Proof.
  intros a m Ha Hm. apply Z.rem_bound_pos; lia.
Qed.
Lemma rem_lt__pool_sum_closed_form :
  forall a m, 0 <= a -> 0 < m -> Z.rem a m < m.
Proof.
  intros a m Ha Hm. apply Z.rem_bound_pos; lia.
Qed.
Lemma rem_mod_collapse__pool_sum_closed_form :
  forall a m, m <> 0 -> (Z.rem a m) mod m = a mod m.
Proof.
  intros a m Hm.
  rewrite Z.rem_eq by exact Hm.
  replace (a - m * (Z.quot a m)) with (a + (- (Z.quot a m)) * m) by ring.
  apply Z_mod_plus_full.
Qed.
Lemma rem_shift_is_mod__pool_sum_closed_form :
  forall a m, 0 < m -> Z.rem (Z.rem a m + m) m = a mod m.
Proof.
  intros a m Hm.
  pose proof (Z.rem_bound_abs a m ltac:(lia)) as Hb.
  rewrite (Z.abs_eq m ltac:(lia)) in Hb.
  apply Z.abs_lt in Hb.
  rewrite rem_nonneg_is_mod__pool_sum_closed_form by lia.
  replace (Z.rem a m + m) with (Z.rem a m + 1 * m) by ring.
  rewrite Z_mod_plus_full.
  apply rem_mod_collapse__pool_sum_closed_form. lia.
Qed.
Lemma mod_add_congr__pool_sum_closed_form :
  forall a b a' b' m, m <> 0 ->
    a mod m = a' mod m -> b mod m = b' mod m ->
    (a + b) mod m = (a' + b') mod m.
Proof.
  intros a b a' b' m Hm H1 H2.
  rewrite (Z.add_mod a b) by exact Hm.
  rewrite (Z.add_mod a' b') by exact Hm.
  rewrite H1, H2. reflexivity.
Qed.
Lemma mod_mul_congr__pool_sum_closed_form :
  forall a b a' b' m, m <> 0 ->
    a mod m = a' mod m -> b mod m = b' mod m ->
    (a * b) mod m = (a' * b') mod m.
Proof.
  intros a b a' b' m Hm H1 H2.
  rewrite (Z.mul_mod a b) by exact Hm.
  rewrite (Z.mul_mod a' b') by exact Hm.
  rewrite H1, H2. reflexivity.
Qed.
Lemma pool_expr_rem_to_mod__pool_sum_closed_form :
  forall a b c d e f m,
    0 < m -> 0 <= a -> 0 <= b -> 0 <= c -> 0 <= e -> 0 <= f ->
    Z.rem (Z.rem (Z.rem (Z.rem a m * b) m * Z.rem c m) m
           + Z.rem (Z.rem d m + m) m * Z.rem (b + e * Z.rem f m) m) m
    = (((a mod m * b) mod m * (c mod m)) mod m
       + (d mod m) * ((b + e * (f mod m)) mod m)) mod m.
Proof.
  intros a b c d e f m Hm Ha Hb Hc He Hf.
  pose proof (Z.mod_pos_bound a m Hm) as Ha'.
  pose proof (Z.mod_pos_bound c m Hm) as Hc'.
  pose proof (Z.mod_pos_bound f m Hm) as Hf'.
  pose proof (Z.mod_pos_bound d m Hm) as Hd'.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form a m Ha Hm).
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form c m Hc Hm).
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form f m Hf Hm).
  assert (Hx : 0 <= a mod m * b) by nia.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form (a mod m * b) m Hx Hm).
  pose proof (Z.mod_pos_bound (a mod m * b) m Hm) as Hx'.
  assert (Hy : 0 <= (a mod m * b) mod m * (c mod m)) by nia.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form ((a mod m * b) mod m * (c mod m)) m Hy Hm).
  pose proof (Z.mod_pos_bound ((a mod m * b) mod m * (c mod m)) m Hm) as Hy'.
  rewrite (rem_shift_is_mod__pool_sum_closed_form d m Hm).
  assert (Hz : 0 <= b + e * (f mod m)) by nia.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form (b + e * (f mod m)) m Hz Hm).
  pose proof (Z.mod_pos_bound (b + e * (f mod m)) m Hm) as Hz'.
  assert (Hw : 0 <= ((a mod m * b) mod m * (c mod m)) mod m
                   + (d mod m) * ((b + e * (f mod m)) mod m)) by nia.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form _ m Hw Hm).
  reflexivity.
Qed.
Lemma pool_mod_normalize__pool_sum_closed_form :
  forall a b c d e f m, m <> 0 ->
    (((a mod m * (b mod m)) mod m * (c mod m)) mod m
     + (d mod m) * (((b mod m) + (e mod m) * (f mod m)) mod m)) mod m
    = (a * b * c + d * (b + f * e)) mod m.
Proof.
  intros a b c d e f m Hm.
  assert (Hmm : forall x, (x mod m) mod m = x mod m) by (intros; apply Z.mod_mod; exact Hm).
  assert (E0 : (a mod m * (b mod m)) mod m = (a * b) mod m).
  { apply mod_mul_congr__pool_sum_closed_form; auto. }
  assert (E1 : ((a mod m * (b mod m)) mod m * (c mod m)) mod m = (a * b * c) mod m).
  { apply mod_mul_congr__pool_sum_closed_form; auto.
    rewrite Hmm. exact E0. }
  assert (E2 : ((b mod m) + (e mod m) * (f mod m)) mod m = (b + f * e) mod m).
  { apply mod_add_congr__pool_sum_closed_form; auto.
    rewrite (Z.mul_comm f e).
    apply mod_mul_congr__pool_sum_closed_form; auto. }
  assert (E3 : ((d mod m) * (((b mod m) + (e mod m) * (f mod m)) mod m)) mod m
               = (d * (b + f * e)) mod m).
  { apply mod_mul_congr__pool_sum_closed_form; auto.
    rewrite Hmm. exact E2. }
  apply mod_add_congr__pool_sum_closed_form.
  - exact Hm.
  - rewrite Hmm. exact E1.
  - exact E3.
Qed.
Lemma pool_closed_form_from_residues__pool_sum_closed_form :
  forall k S S2 r2 r3,
    k >= 3 -> 0 <= S -> 0 <= S2 ->
    r2 = pow_mod 2 (k - 2) ->
    r3 = pow_mod 2 (k - 3) ->
    Z.rem (Z.rem (Z.rem (Z.rem S2 998244353 * r2) 998244353 * Z.rem (k - 1) 998244353) 998244353
           + Z.rem (Z.rem (S * S - S2) 998244353 + 998244353) 998244353
             * Z.rem (r2 + r3 * Z.rem (k - 2) 998244353) 998244353) 998244353
    = pool_closed_form k S S2.
Proof.
  intros k S S2 r2 r3 Hk HS HS2 Hr2 Hr3.
  assert (Hm : 0 < 998244353) by lia.
  assert (Hm0 : 998244353 <> 0) by lia.
  subst r2 r3. unfold pow_mod.
  pose proof (Z.mod_pos_bound (2 ^ (k - 2)) 998244353 Hm) as H2b.
  pose proof (Z.mod_pos_bound (2 ^ (k - 3)) 998244353 Hm) as H3b.
  rewrite (pool_expr_rem_to_mod__pool_sum_closed_form
             S2 (2 ^ (k - 2) mod 998244353) (k - 1) (S * S - S2)
             (2 ^ (k - 3) mod 998244353) (k - 2) 998244353) by lia.
  rewrite (pool_mod_normalize__pool_sum_closed_form
             S2 (2 ^ (k - 2)) (k - 1) (S * S - S2) (2 ^ (k - 3)) (k - 2) 998244353 Hm0).
  unfold pool_closed_form.
  assert (Hb : (k <? 2) = false) by (apply Z.ltb_ge; lia).
  rewrite Hb. reflexivity.
Qed.
Lemma pool_closed_form_k2__pool_sum_closed_form :
  forall k S S2 r,
    k = 2 -> r = 1 -> 0 <= S -> 0 <= S2 < 998244353 ->
    Z.rem (Z.rem (Z.rem (Z.rem S2 998244353 * r) 998244353 * Z.rem (k - 1) 998244353) 998244353
           + Z.rem (Z.rem (S * S - S2) 998244353 + 998244353) 998244353 * r) 998244353
    = pool_closed_form k S S2.
Proof.
  intros k S S2 r Hk Hr HS HS2. subst k r.
  assert (Hm : 0 < 998244353) by lia.
  assert (Hm0 : 998244353 <> 0) by lia.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form S2 998244353) by lia.
  rewrite (Z.mod_small S2 998244353) by lia.
  replace (S2 * 1) with S2 by ring.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form S2 998244353) by lia.
  rewrite (Z.mod_small S2 998244353) by lia.
  replace (Z.rem (2 - 1) 998244353) with 1 by reflexivity.
  replace (S2 * 1) with S2 by ring.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form S2 998244353) by lia.
  rewrite (Z.mod_small S2 998244353) by lia.
  rewrite (rem_shift_is_mod__pool_sum_closed_form (S * S - S2) 998244353 Hm).
  pose proof (Z.mod_pos_bound (S * S - S2) 998244353 Hm) as Hc.
  replace ((S * S - S2) mod 998244353 * 1) with ((S * S - S2) mod 998244353) by ring.
  assert (Hw : 0 <= S2 + (S * S - S2) mod 998244353) by lia.
  rewrite (rem_nonneg_is_mod__pool_sum_closed_form _ 998244353 Hw Hm).
  unfold pool_closed_form.
  assert (Hb : (2 <? 2) = false) by reflexivity.
  rewrite Hb.
  replace (2 - 2) with 0 by lia.
  replace (2 - 3) with (-1) by lia.
  replace (2 - 1) with 1 by lia.
  rewrite Z.pow_0_r.
  rewrite Z.pow_neg_r by lia.
  replace (S2 * 1 * 1 + (S * S - S2) * (1 + 0 * 0)) with (S2 + (S * S - S2)) by ring.
  rewrite <- (Z.add_mod_idemp_r S2 (S * S - S2) 998244353 Hm0).
  reflexivity.
Qed.
Lemma pool_closed_form_small__pool_sum_closed_form :
  forall k S S2, k < 2 -> 0 = pool_closed_form k S S2.
Proof.
  intros k S S2 Hk. unfold pool_closed_form.
  assert (Hb : (k <? 2) = true) by (apply Z.ltb_lt; lia).
  rewrite Hb. reflexivity.
Qed.
Lemma sum_range_step__solver_loop_plumbing : forall (a b : Z) (f : Z -> Z),
  (b < a -> sum_range a b f = 0) /\
  (a <= b -> sum_range a b f = sum_range a (b - 1) f + f b).
Proof.
  intros a b f. split.
  - intros Hlt. unfold sum_range. apply sum_Z_range_empty. lia.
  - intros Hle. unfold sum_range.
    replace (b - 1 + 1) with b by lia.
    apply sum_Z_range_extend_right. lia.
Qed.
Lemma multiple_prefix_sum_step__solver_loop_plumbing :
  forall (l : list Z) (d u : Z),
  multiple_prefix_sum l d 0 = 0 /\
  (1 <= u -> multiple_prefix_sum l d u
             = multiple_prefix_sum l d (u - 1) + Znth (u * d) l 0).
Proof.
  intros l d u. unfold multiple_prefix_sum. split.
  - apply (proj1 (sum_range_step__solver_loop_plumbing 1 0
                    (fun i => Znth (i * d) l 0))). lia.
  - intros Hu.
    apply (proj2 (sum_range_step__solver_loop_plumbing 1 u
                    (fun i => Znth (i * d) l 0))). lia.
Qed.
Lemma maximum_value_bounds_Forall__solver_loop_plumbing :
  forall (vals : list Z),
  Forall (fun x => 1 <= x <= 100000) vals ->
  1 <= maximum_value vals <= 100000.
Proof.
  intros vals HF. unfold maximum_value.
  induction HF as [| x xs Hx Hxs IH]; simpl; lia.
Qed.
Lemma maximum_value_bounds__solver_loop_plumbing : forall (vals : list Z),
  (forall i, 0 <= i < Zlength vals -> 1 <= Znth i vals 0 <= 100000) ->
  1 <= maximum_value vals <= 100000.
Proof.
  intros vals Hi.
  apply maximum_value_bounds_Forall__solver_loop_plumbing.
  apply (proj2 (Forall_Znth (fun x => 1 <= x <= 100000) 0 vals)).
  exact Hi.
Qed.
Lemma In_Znth_ex__solver_loop_plumbing : forall (l : list Z) (d x : Z),
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros l d x Hin.
  apply (In_nth l x d) in Hin.
  destruct Hin as [n [Hn Hnth]].
  exists (Z.of_nat n).
  unfold Znth. rewrite Nat2Z.id.
  split; [| exact Hnth].
  rewrite Zlength_correct. lia.
Qed.
Lemma rem_eq_mod_nonneg__solver_loop_plumbing : forall (a b : Z),
  0 <= a -> 0 < b -> Z.rem a b = a mod b.
Proof.
  intros a b Ha Hb.
  rewrite Zquot.Zrem_Zmod_pos; auto; lia.
Qed.
Lemma aggregate_entry_bounds__solver_loop_plumbing :
  forall (vals freq cnts sums squares : list Z) (maxv w : Z),
  Zlength freq = Zlength vals ->
  (forall i, 0 <= i < Zlength freq -> 1 <= Znth i freq 0 <= 1000000000) ->
  aggregate_arrays vals freq cnts sums squares maxv ->
  0 <= w <= maxv ->
  0 <= Znth w cnts 0 <= 1000000000 /\
  0 <= Znth w sums 0 < 998244353 /\
  0 <= Znth w squares 0 < 998244353.
Proof.
  intros vals freq cnts sums squares maxv w Hlen Hfreq Hagg Hw.
  destruct Hagg as [_ [_ [_ [Hin Hnotin]]]].
  destruct (In_dec Z.eq_dec w vals) as [HI | HN].
  - apply (In_Znth_ex__solver_loop_plumbing vals 0 w) in HI.
    destruct HI as [i [Hi Hnth]].
    specialize (Hin i Hi). rewrite Hnth in Hin.
    destruct Hin as [Hc [Hs Hq]].
    specialize (Hfreq i ltac:(lia)).
    rewrite Hc, Hs, Hq.
    pose proof (Z.mod_pos_bound (w * Znth i freq 0) 998244353 ltac:(lia)).
    pose proof (Z.mod_pos_bound (w * w * Znth i freq 0) 998244353 ltac:(lia)).
    lia.
  - specialize (Hnotin w Hw HN).
    destruct Hnotin as [Hc [Hs Hq]].
    rewrite Hc, Hs, Hq. lia.
Qed.
Lemma sub_mod_canonical__solver_loop_plumbing : forall (a b p : Z),
  0 < p -> ((a mod p - b mod p) + p) mod p = (a - b) mod p.
Proof.
  intros a b p Hp.
  replace (a mod p - b mod p + p) with ((a mod p - b mod p) + 1 * p) by lia.
  rewrite Z_mod_plus_full.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.
Lemma peel_state_step__solver_loop_plumbing :
  forall (vals freq : list Z) (d u w cur : Z),
  2 <= u -> w = u * d ->
  PeelState vals freq d (u - 1) cur ->
  PeelState vals freq d u
    ((cur - (exact_gcd_weight vals freq w) mod 998244353 + 998244353)
     mod 998244353).
Proof.
  intros vals freq d u w cur Hu Hw H.
  unfold PeelState in *.
  destruct (sum_range_step__solver_loop_plumbing 2 u
              (fun i => exact_gcd_weight vals freq (i * d))) as [_ Hstep].
  specialize (Hstep ltac:(lia)).
  rewrite Hstep. subst w. rewrite H.
  replace (pool_weight vals freq d -
           (sum_range 2 (u - 1)
              (fun i => exact_gcd_weight vals freq (i * d))
            + exact_gcd_weight vals freq (u * d)))
    with ((pool_weight vals freq d -
           sum_range 2 (u - 1)
             (fun i => exact_gcd_weight vals freq (i * d)))
          - exact_gcd_weight vals freq (u * d)) by lia.
  apply sub_mod_canonical__solver_loop_plumbing. lia.
Qed.
Lemma fold_add_app__sieve_math_core : forall l1 l2 : list Z,
  fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  induction l1 as [| a l1 IH]; intros l2; simpl; [reflexivity |].
  rewrite IH. ring.
Qed.
Lemma sub_multisets_cons_split__sieve_math_core :
  forall (f : list Z -> Z) (x : Z) (P : list Z),
  fold_right Z.add 0 (map f (sub_multisets (x :: P)))
  = fold_right Z.add 0 (map (fun A => f (x :: A)) (sub_multisets P))
    + fold_right Z.add 0 (map f (sub_multisets P)).
Proof.
  intros f x P. simpl.
  rewrite map_app, fold_add_app__sieve_math_core, map_map. reflexivity.
Qed.
Lemma head_C__sieve_math_core : forall (x : Z) (L : list (list Z)),
  fold_right Z.add 0 (map (fun A => Zlength (x :: A)) L)
  = fold_right Z.add 0 (map (fun A : list Z => Zlength A) L) + Zlength L.
Proof.
  intros x L. induction L as [| a L IH]; cbn [fold_right map] in *.
  - rewrite Zlength_nil. ring.
  - rewrite IH, !Zlength_cons. unfold Z.succ. ring.
Qed.
Lemma head_S1__sieve_math_core : forall (x : Z) (L : list (list Z)),
  fold_right Z.add 0 (map (fun A => fold_right Z.add 0 (x :: A)) L)
  = x * Zlength L + fold_right Z.add 0 (map (fun A : list Z => fold_right Z.add 0 A) L).
Proof.
  intros x L. induction L as [| a L IH]; cbn [fold_right map] in *.
  - rewrite Zlength_nil. ring.
  - rewrite IH, !Zlength_cons. unfold Z.succ. ring.
Qed.
Lemma head_U__sieve_math_core : forall (x : Z) (L : list (list Z)),
  fold_right Z.add 0 (map (fun A => Zlength (x :: A) * fold_right Z.add 0 (x :: A)) L)
  = x * fold_right Z.add 0 (map (fun A : list Z => Zlength A) L)
    + fold_right Z.add 0 (map (fun A : list Z => Zlength A * fold_right Z.add 0 A) L)
    + x * Zlength L
    + fold_right Z.add 0 (map (fun A : list Z => fold_right Z.add 0 A) L).
Proof.
  intros x L. induction L as [| a L IH]; cbn [fold_right map] in *.
  - rewrite Zlength_nil. ring.
  - rewrite IH, !Zlength_cons. unfold Z.succ. ring.
Qed.
Lemma head_Q__sieve_math_core : forall (x : Z) (L : list (list Z)),
  fold_right Z.add 0 (map (fun A => fold_right Z.add 0 (x :: A) * fold_right Z.add 0 (x :: A)) L)
  = x * x * Zlength L
    + 2 * x * fold_right Z.add 0 (map (fun A : list Z => fold_right Z.add 0 A) L)
    + fold_right Z.add 0 (map (fun A : list Z => fold_right Z.add 0 A * fold_right Z.add 0 A) L).
Proof.
  intros x L. induction L as [| a L IH]; cbn [fold_right map] in *.
  - rewrite Zlength_nil. ring.
  - rewrite IH, !Zlength_cons. unfold Z.succ. ring.
Qed.
Lemma head_R__sieve_math_core : forall (x : Z) (L : list (list Z)),
  fold_right Z.add 0
    (map (fun A => Zlength (x :: A)
                   * (fold_right Z.add 0 (x :: A) * fold_right Z.add 0 (x :: A))) L)
  = x * x * fold_right Z.add 0 (map (fun A : list Z => Zlength A) L)
    + 2 * x * fold_right Z.add 0 (map (fun A : list Z => Zlength A * fold_right Z.add 0 A) L)
    + fold_right Z.add 0
        (map (fun A : list Z => Zlength A * (fold_right Z.add 0 A * fold_right Z.add 0 A)) L)
    + x * x * Zlength L
    + 2 * x * fold_right Z.add 0 (map (fun A : list Z => fold_right Z.add 0 A) L)
    + fold_right Z.add 0 (map (fun A : list Z => fold_right Z.add 0 A * fold_right Z.add 0 A) L).
Proof.
  intros x L. induction L as [| a L IH]; cbn [fold_right map] in *.
  - rewrite Zlength_nil. ring.
  - rewrite IH, !Zlength_cons. unfold Z.succ. ring.
Qed.
Lemma Zlength_map__sieve_math_core : forall (A B : Type) (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l. induction l as [| a l IH]; [reflexivity |].
  cbn [map]. rewrite !Zlength_cons, IH. reflexivity.
Qed.
Lemma sub_multisets_count__sieve_math_core : forall P : list Z,
  Zlength (sub_multisets P) = 2 ^ (Zlength P).
Proof.
  induction P as [| x P IH]; cbn [sub_multisets].
  - rewrite Zlength_nil. reflexivity.
  - rewrite Zlength_app, Zlength_map__sieve_math_core, IH, Zlength_cons.
    rewrite Z.pow_succ_r by apply Zlength_nonneg. lia.
Qed.
Lemma sub_multisets_aggregates__sieve_math_core : forall P : list Z,
  2 * fold_right Z.add 0 (map (fun A : list Z => Zlength A) (sub_multisets P))
      = Zlength P * 2 ^ Zlength P
  /\ 2 * fold_right Z.add 0 (map (fun A : list Z => fold_right Z.add 0 A) (sub_multisets P))
      = 2 ^ Zlength P * fold_right Z.add 0 P
  /\ 4 * fold_right Z.add 0
           (map (fun A : list Z => Zlength A * fold_right Z.add 0 A) (sub_multisets P))
      = (Zlength P + 1) * 2 ^ Zlength P * fold_right Z.add 0 P
  /\ 4 * fold_right Z.add 0
           (map (fun A : list Z => fold_right Z.add 0 A * fold_right Z.add 0 A)
                (sub_multisets P))
      = 2 ^ Zlength P * (fold_right Z.add 0 P * fold_right Z.add 0 P
                         + fold_right Z.add 0 (map (fun y : Z => y * y) P))
  /\ 8 * fold_right Z.add 0
           (map (fun A : list Z => Zlength A * (fold_right Z.add 0 A * fold_right Z.add 0 A))
                (sub_multisets P))
      = 2 ^ Zlength P
        * (2 * (Zlength P + 1) * fold_right Z.add 0 (map (fun y : Z => y * y) P)
           + (fold_right Z.add 0 P * fold_right Z.add 0 P
              - fold_right Z.add 0 (map (fun y : Z => y * y) P)) * (Zlength P + 2)).
Proof.
  intros P. induction P as [| x P IH].
  - cbn [sub_multisets map fold_right]. rewrite !Zlength_nil, Z.pow_0_r.
    repeat split; ring.
  - destruct IH as (IC & IS & IU & IQ & IR).
    pose proof (sub_multisets_count__sieve_math_core P) as HN.
    pose proof (Zlength_nonneg P) as HK.
    assert (HE : 2 ^ (Zlength P + 1) = 2 * 2 ^ Zlength P)
      by (rewrite Z.pow_add_r by lia; ring).
    assert (HS : fold_right Z.add 0 (x :: P) = x + fold_right Z.add 0 P) by reflexivity.
    assert (HQ : fold_right Z.add 0 (map (fun y : Z => y * y) (x :: P))
                 = x * x + fold_right Z.add 0 (map (fun y : Z => y * y) P)) by reflexivity.
    repeat split.
    + rewrite sub_multisets_cons_split__sieve_math_core. cbv beta.
      rewrite head_C__sieve_math_core, HN, !Zlength_cons.
      unfold Z.succ. rewrite HE.
      set (E := 2 ^ Zlength P) in *.
      set (C := fold_right Z.add 0 (map (fun A : list Z => Zlength A) (sub_multisets P))) in *.
      replace (2 * (C + E + C)) with (2 * (2 * C) + 2 * E) by ring.
      rewrite IC. ring.
    + rewrite sub_multisets_cons_split__sieve_math_core. cbv beta.
      rewrite head_S1__sieve_math_core, HN, !Zlength_cons, HS.
      unfold Z.succ. rewrite HE.
      set (E := 2 ^ Zlength P) in *.
      set (S1 := fold_right Z.add 0
                   (map (fun A : list Z => fold_right Z.add 0 A) (sub_multisets P))) in *.
      replace (2 * (x * E + S1 + S1)) with (2 * x * E + 2 * (2 * S1)) by ring.
      rewrite IS. ring.
    + rewrite sub_multisets_cons_split__sieve_math_core. cbv beta.
      rewrite head_U__sieve_math_core, HN, !Zlength_cons, HS.
      unfold Z.succ. rewrite HE.
      set (E := 2 ^ Zlength P) in *.
      set (C := fold_right Z.add 0 (map (fun A : list Z => Zlength A) (sub_multisets P))) in *.
      set (S1 := fold_right Z.add 0
                   (map (fun A : list Z => fold_right Z.add 0 A) (sub_multisets P))) in *.
      set (U := fold_right Z.add 0
                  (map (fun A : list Z => Zlength A * fold_right Z.add 0 A)
                       (sub_multisets P))) in *.
      replace (4 * (x * C + U + x * E + S1 + U))
        with (2 * x * (2 * C) + 2 * (4 * U) + 4 * x * E + 2 * (2 * S1)) by ring.
      rewrite IC, IU, IS. ring.
    + rewrite sub_multisets_cons_split__sieve_math_core. cbv beta.
      rewrite head_Q__sieve_math_core, HN, !Zlength_cons, HS, HQ.
      unfold Z.succ. rewrite HE.
      set (E := 2 ^ Zlength P) in *.
      set (S1 := fold_right Z.add 0
                   (map (fun A : list Z => fold_right Z.add 0 A) (sub_multisets P))) in *.
      set (Q := fold_right Z.add 0
                  (map (fun A : list Z => fold_right Z.add 0 A * fold_right Z.add 0 A)
                       (sub_multisets P))) in *.
      replace (4 * (x * x * E + 2 * x * S1 + Q + Q))
        with (4 * x * x * E + 4 * x * (2 * S1) + 2 * (4 * Q)) by ring.
      rewrite IS, IQ. ring.
    + rewrite sub_multisets_cons_split__sieve_math_core. cbv beta.
      rewrite head_R__sieve_math_core, HN, !Zlength_cons, HS, HQ.
      unfold Z.succ. rewrite HE.
      set (E := 2 ^ Zlength P) in *.
      set (C := fold_right Z.add 0 (map (fun A : list Z => Zlength A) (sub_multisets P))) in *.
      set (S1 := fold_right Z.add 0
                   (map (fun A : list Z => fold_right Z.add 0 A) (sub_multisets P))) in *.
      set (U := fold_right Z.add 0
                  (map (fun A : list Z => Zlength A * fold_right Z.add 0 A)
                       (sub_multisets P))) in *.
      set (Q := fold_right Z.add 0
                  (map (fun A : list Z => fold_right Z.add 0 A * fold_right Z.add 0 A)
                       (sub_multisets P))) in *.
      set (R := fold_right Z.add 0
                  (map (fun A : list Z =>
                          Zlength A * (fold_right Z.add 0 A * fold_right Z.add 0 A))
                       (sub_multisets P))) in *.
      replace (8 * (x * x * C + 2 * x * U + R + x * x * E + 2 * x * S1 + Q + R))
        with (4 * x * x * (2 * C) + 4 * x * (4 * U) + 2 * (8 * R)
              + 8 * x * x * E + 8 * x * (2 * S1) + 2 * (4 * Q)) by ring.
      rewrite IC, IU, IR, IS, IQ. ring.
Qed.
Lemma fold_map_sub__sieve_math_core :
  forall (f g : list Z -> Z) (L : list (list Z)),
  fold_right Z.add 0 (map (fun A => f A - g A) L)
  = fold_right Z.add 0 (map f L) - fold_right Z.add 0 (map g L).
Proof.
  intros f g L. induction L as [| a L IH]; cbn [map fold_right] in *; [ring |].
  rewrite IH. ring.
Qed.
Lemma fold_map_ext__sieve_math_core :
  forall (f g : list Z -> Z) (L : list (list Z)),
  (forall A : list Z, f A = g A) ->
  fold_right Z.add 0 (map f L) = fold_right Z.add 0 (map g L).
Proof.
  intros f g L H. induction L as [| a L IH]; cbn [map fold_right]; [reflexivity |].
  rewrite IH, H. reflexivity.
Qed.
Lemma subset_weight_sum_exact__sieve_math_core : forall P : list Z,
  8 * subset_weight_sum P
  = 2 ^ Zlength P
    * (2 * (Zlength P - 1) * fold_right Z.add 0 (map (fun y : Z => y * y) P)
       + Zlength P * (fold_right Z.add 0 P * fold_right Z.add 0 P
                      - fold_right Z.add 0 (map (fun y : Z => y * y) P))).
Proof.
  intros P.
  destruct (sub_multisets_aggregates__sieve_math_core P) as (IC & IS & IU & IQ & IR).
  unfold subset_weight_sum.
  rewrite (fold_map_ext__sieve_math_core subset_weight
             (fun A : list Z => Zlength A * (fold_right Z.add 0 A * fold_right Z.add 0 A)
                                - fold_right Z.add 0 A * fold_right Z.add 0 A))
    by (intros A; unfold subset_weight; rewrite Z.pow_2_r; ring).
  rewrite (fold_map_sub__sieve_math_core
             (fun A : list Z => Zlength A * (fold_right Z.add 0 A * fold_right Z.add 0 A))
             (fun A : list Z => fold_right Z.add 0 A * fold_right Z.add 0 A)).
  set (E := 2 ^ Zlength P) in *.
  set (Q := fold_right Z.add 0
              (map (fun A : list Z => fold_right Z.add 0 A * fold_right Z.add 0 A)
                   (sub_multisets P))) in *.
  set (R := fold_right Z.add 0
              (map (fun A : list Z =>
                      Zlength A * (fold_right Z.add 0 A * fold_right Z.add 0 A))
                   (sub_multisets P))) in *.
  replace (8 * (R - Q)) with (8 * R - 2 * (4 * Q)) by ring.
  rewrite IR, IQ. ring.
Qed.
Lemma pow_shift2__sieve_math_core : forall k : Z, 2 <= k -> 8 * 2 ^ (k - 2) = 2 * 2 ^ k.
Proof.
  intros k Hk.
  assert (H : 2 ^ k = 2 ^ (k - 2) * 2 ^ 2)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite H. ring.
Qed.
Lemma pow_shift3__sieve_math_core : forall k : Z, 2 <= k ->
  (k - 2) * (8 * 2 ^ (k - 3)) = (k - 2) * 2 ^ k.
Proof.
  intros k Hk.
  destruct (Z.eq_dec k 2) as [Heq | Hne].
  - subst k. reflexivity.
  - assert (H : 2 ^ k = 2 ^ (k - 3) * 2 ^ 3)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite H. ring.
Qed.
Lemma pool_closed_form_exact__sieve_math_core : forall (k S S2 : Z), 2 <= k ->
  8 * (S2 * 2 ^ (k - 2) * (k - 1) + (S * S - S2) * (2 ^ (k - 2) + (k - 2) * 2 ^ (k - 3)))
  = 2 ^ k * (2 * (k - 1) * S2 + k * (S * S - S2)).
Proof.
  intros k S S2 Hk.
  replace (8 * (S2 * 2 ^ (k - 2) * (k - 1)
                + (S * S - S2) * (2 ^ (k - 2) + (k - 2) * 2 ^ (k - 3))))
    with (S2 * (k - 1) * (8 * 2 ^ (k - 2))
          + (S * S - S2) * (8 * 2 ^ (k - 2))
          + (S * S - S2) * ((k - 2) * (8 * 2 ^ (k - 3)))) by ring.
  rewrite pow_shift2__sieve_math_core, pow_shift3__sieve_math_core by lia.
  ring.
Qed.
Lemma mod_poly_cong__sieve_math_core : forall S S2 c1 c2 c3 : Z,
  (S2 mod 998244353 * c1 * c2
   + (S mod 998244353 * (S mod 998244353) - S2 mod 998244353) * c3) mod 998244353
  = (S2 * c1 * c2 + (S * S - S2) * c3) mod 998244353.
Proof.
  intros S S2 c1 c2 c3.
  rewrite (Z.mod_eq S 998244353) by lia.
  rewrite (Z.mod_eq S2 998244353) by lia.
  set (q := S / 998244353). set (r := S2 / 998244353).
  replace ((S2 - 998244353 * r) * c1 * c2
           + ((S - 998244353 * q) * (S - 998244353 * q) - (S2 - 998244353 * r)) * c3)
    with ((S2 * c1 * c2 + (S * S - S2) * c3)
          + (- r * c1 * c2 + (- 2 * S * q + 998244353 * q * q + r) * c3) * 998244353)
    by ring.
  apply Z_mod_plus_full.
Qed.
Lemma subset_weight_sum_small__sieve_math_core : forall P : list Z,
  Zlength P < 2 -> subset_weight_sum P = 0.
Proof.
  intros P Hlt.
  destruct P as [| a [| b P']].
  - unfold subset_weight_sum. cbn [sub_multisets map fold_right].
    unfold subset_weight. rewrite Zlength_nil. cbn [fold_right].
    rewrite Z.pow_2_r. ring.
  - unfold subset_weight_sum. cbn [sub_multisets map fold_right app].
    unfold subset_weight. rewrite !Zlength_cons, !Zlength_nil.
    cbn [fold_right]. unfold Z.succ. rewrite !Z.pow_2_r. ring.
  - exfalso. rewrite !Zlength_cons in Hlt.
    pose proof (Zlength_nonneg P'). unfold Z.succ in Hlt. lia.
Qed.
Lemma subset_weight_sum_closed_form__sieve_math_core : forall P : list Z,
  subset_weight_sum P mod 998244353
  = pool_closed_form (Zlength P)
      (fold_right Z.add 0 P mod 998244353)
      (fold_right Z.add 0 (map (fun y : Z => y * y) P) mod 998244353).
Proof.
  intros P. unfold pool_closed_form.
  destruct (Zlength P <? 2) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite (subset_weight_sum_small__sieve_math_core P Hlt).
    apply Zmod_0_l.
  - apply Z.ltb_ge in Hlt.
    assert (Hexact : subset_weight_sum P
      = fold_right Z.add 0 (map (fun y : Z => y * y) P) * 2 ^ (Zlength P - 2) * (Zlength P - 1)
        + (fold_right Z.add 0 P * fold_right Z.add 0 P
           - fold_right Z.add 0 (map (fun y : Z => y * y) P))
          * (2 ^ (Zlength P - 2) + (Zlength P - 2) * 2 ^ (Zlength P - 3))).
    { pose proof (subset_weight_sum_exact__sieve_math_core P) as H1.
      pose proof (pool_closed_form_exact__sieve_math_core (Zlength P)
                    (fold_right Z.add 0 P)
                    (fold_right Z.add 0 (map (fun y : Z => y * y) P)) Hlt) as H2.
      lia. }
    rewrite Hexact.
    symmetry. apply mod_poly_cong__sieve_math_core.
Qed.
Lemma sum_range_one_hot__sieve_math_core :
  forall (a b i0 : Z) (f : Z -> Z),
  a <= i0 < b ->
  (forall i : Z, a <= i < b -> i <> i0 -> f i = 0) ->
  sum (fun i => a <= i < b) f = f i0.
Proof.
  intros a b i0 f Hi0 Hz.
  rewrite (sum_Z_range_split a i0 b f) by lia.
  rewrite (sum_Z_range_eq_zero a i0 f) by (intros i Hi; apply Hz; lia).
  rewrite (sum_Z_range_split i0 (i0 + 1) b f) by lia.
  rewrite (sum_Z_range_eq_zero (i0 + 1) b f) by (intros i Hi; apply Hz; lia).
  rewrite sum_Z_range_single. ring.
Qed.
Lemma In_Znth__sieve_math_core : forall (l : list Z) (x : Z),
  In x l -> exists j : Z, 0 <= j < Zlength l /\ Znth j l 0 = x.
Proof.
  intros l x Hin.
  destruct (In_nth l x 0 Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma NoDup_Znth_inj__sieve_math_core : forall (l : list Z) (j1 j2 : Z),
  NoDup l -> 0 <= j1 < Zlength l -> 0 <= j2 < Zlength l ->
  Znth j1 l 0 = Znth j2 l 0 -> j1 = j2.
Proof.
  intros l j1 j2 Hnd H1 H2 Heq.
  rewrite Zlength_correct in H1, H2.
  unfold Znth in Heq.
  apply (proj1 (NoDup_nth l 0)) with (i := Z.to_nat j1) (j := Z.to_nat j2) in Hnd;
    [ lia | lia | lia | exact Heq ].
Qed.
Lemma fold_map_filter_repeat__sieve_math_core :
  forall (h : Z -> Z) (c : Z -> bool) (v : Z) (n : nat),
  fold_right Z.add 0 (map h (filter c (repeat v n)))
  = (if c v then h v * Z.of_nat n else 0).
Proof.
  intros h c v n. destruct (c v) eqn:Hc.
  - induction n as [| n IH].
    + simpl. ring.
    + cbn [repeat filter]. rewrite Hc. cbn [map fold_right].
      rewrite IH, Nat2Z.inj_succ. ring.
  - induction n as [| n IH].
    + simpl. reflexivity.
    + cbn [repeat filter]. rewrite Hc. exact IH.
Qed.
Lemma fold_combine_as_range__sieve_math_core :
  forall (f : Z -> Z -> Z) (l1 l2 : list Z),
  Zlength l2 = Zlength l1 ->
  fold_right Z.add 0 (map (fun p : Z * Z => f (fst p) (snd p)) (combine l1 l2))
  = sum (fun i => 0 <= i < Zlength l1) (fun i => f (Znth i l1 0) (Znth i l2 0)).
Proof.
  intros f l1. induction l1 as [| a l1 IH]; intros l2 Hlen.
  - cbn [combine map fold_right]. rewrite Zlength_nil.
    rewrite sum_Z_range_empty by lia. reflexivity.
  - destruct l2 as [| b l2].
    { exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg l1). unfold Z.succ in Hlen. lia. }
    rewrite !Zlength_cons in Hlen.
    cbn [combine map fold_right fst snd].
    rewrite (IH l2) by lia.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg l1) as Hnn.
    rewrite (sum_Z_range_cons 0 (Z.succ (Zlength l1))) by lia.
    cbv beta. rewrite !Znth0_cons.
    f_equal.
    replace (Z.succ (Zlength l1)) with (Zlength l1 + 1) by lia.
    rewrite sum_Z_range_shift_1.
    apply sum_Z_range_ext. intros i Hi.
    rewrite !Znth_cons by lia.
    replace (i + 1 - 1) with i by lia. reflexivity.
Qed.
Lemma pool_fold_expand__sieve_math_core :
  forall (h : Z -> Z) (d : Z) (vals freq : list Z),
  Zlength freq = Zlength vals ->
  (forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0) ->
  fold_right Z.add 0 (map h (divisible_pool (expand vals freq) d))
  = fold_right Z.add 0
      (map (fun p : Z * Z => if (fst p) mod d =? 0 then h (fst p) * snd p else 0)
           (combine vals freq)).
Proof.
  intros h d vals. unfold divisible_pool.
  induction vals as [| v vs IH]; intros freq Hlen Hpos.
  - cbn [expand filter map fold_right combine]. reflexivity.
  - destruct freq as [| f fs].
    { exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg vs). unfold Z.succ in Hlen. lia. }
    assert (Hf : 0 <= f).
    { specialize (Hpos 0). rewrite Znth0_cons in Hpos. apply Hpos.
      rewrite Zlength_cons. pose proof (Zlength_nonneg fs). unfold Z.succ. lia. }
    rewrite !Zlength_cons in Hlen.
    cbn [expand].
    rewrite filter_app, map_app, fold_add_app__sieve_math_core.
    rewrite (fold_map_filter_repeat__sieve_math_core h (fun x => x mod d =? 0) v (Z.to_nat f)).
    rewrite (IH fs) by
      (try lia;
       intros i Hi; specialize (Hpos (i + 1));
       rewrite Znth_cons in Hpos by lia;
       replace (i + 1 - 1) with i in Hpos by lia;
       apply Hpos; rewrite Zlength_cons; unfold Z.succ; lia).
    cbn [combine map fold_right fst snd].
    rewrite Z2Nat.id by lia.
    destruct (v mod d =? 0); ring.
Qed.
Lemma table_entry_sum__sieve_math_core :
  forall (T : Z -> Z -> Z) (tab vals freq : list Z) (m maxv : Z),
  NoDup vals ->
  0 <= m <= maxv ->
  (forall i : Z, 0 <= i < Zlength vals ->
     Znth (Znth i vals 0) tab 0 = T (Znth i vals 0) (Znth i freq 0)) ->
  (forall v : Z, 0 <= v <= maxv -> ~ In v vals -> Znth v tab 0 = 0) ->
  Znth m tab 0
  = sum (fun j => 0 <= j < Zlength vals)
        (fun j => if Znth j vals 0 =? m then T (Znth j vals 0) (Znth j freq 0) else 0).
Proof.
  intros T tab vals freq m maxv Hnd Hm Htab Hzero.
  destruct (In_dec Z.eq_dec m vals) as [Hin | Hnin].
  - destruct (In_Znth__sieve_math_core vals m Hin) as [j0 [Hj0 Hval]].
    assert (Hz : forall j : Z, 0 <= j < Zlength vals -> j <> j0 ->
              (if Znth j vals 0 =? m then T (Znth j vals 0) (Znth j freq 0) else 0) = 0).
    { intros j Hj Hne. destruct (Znth j vals 0 =? m) eqn:Hq; [| reflexivity].
      exfalso. apply Z.eqb_eq in Hq. apply Hne.
      apply (NoDup_Znth_inj__sieve_math_core vals j j0 Hnd Hj Hj0).
      rewrite Hq, Hval. reflexivity. }
    rewrite (sum_range_one_hot__sieve_math_core 0 (Zlength vals) j0 _ Hj0 Hz).
    rewrite Hval, Z.eqb_refl, <- Hval. apply Htab. exact Hj0.
  - rewrite (Hzero m Hm Hnin). symmetry.
    apply sum_Z_range_eq_zero. intros j Hj.
    destruct (Znth j vals 0 =? m) eqn:Hq; [| reflexivity].
    exfalso. apply Z.eqb_eq in Hq. apply Hnin. rewrite <- Hq.
    apply Znth_In_Zlength. exact Hj.
Qed.
Lemma sum_range_swap_aux__sieve_math_core :
  forall (n : nat) (a b c e : Z) (f : Z -> Z -> Z),
  b - a <= Z.of_nat n ->
  sum (fun x => a <= x < b) (fun x => sum (fun y => c <= y < e) (fun y => f x y))
  = sum (fun y => c <= y < e) (fun y => sum (fun x => a <= x < b) (fun x => f x y)).
Proof.
  induction n as [| n IH]; intros a b c e f Hn.
  - rewrite (sum_Z_range_empty a b) by lia.
    symmetry. apply sum_Z_range_eq_zero. intros y Hy.
    apply sum_Z_range_empty. lia.
  - destruct (Z_le_gt_dec b a) as [Hle | Hgt].
    + rewrite (sum_Z_range_empty a b) by lia.
      symmetry. apply sum_Z_range_eq_zero. intros y Hy.
      apply sum_Z_range_empty. lia.
    + rewrite (sum_Z_range_cons a b) by lia. cbv beta.
      rewrite (IH (a + 1) b c e f) by (rewrite Nat2Z.inj_succ in Hn; lia).
      rewrite <- sum_Z_range_add.
      apply sum_Z_range_ext. intros y Hy.
      symmetry. rewrite (sum_Z_range_cons a b) by lia. cbv beta. reflexivity.
Qed.
Lemma sum_range_swap__sieve_math_core :
  forall (a b c e : Z) (f : Z -> Z -> Z),
  sum (fun x => a <= x < b) (fun x => sum (fun y => c <= y < e) (fun y => f x y))
  = sum (fun y => c <= y < e) (fun y => sum (fun x => a <= x < b) (fun x => f x y)).
Proof.
  intros a b c e f.
  apply (sum_range_swap_aux__sieve_math_core (Z.to_nat (b - a))). lia.
Qed.
Lemma table_multiples_sum__sieve_math_core :
  forall (T : Z -> Z -> Z) (tab vals freq : list Z) (d u maxv : Z),
  NoDup vals ->
  Zlength freq = Zlength vals ->
  1 <= d -> 0 <= u -> u * d <= maxv -> maxv < (u + 1) * d ->
  (forall i : Z, 0 <= i < Zlength vals -> 1 <= Znth i vals 0 <= maxv) ->
  (forall i : Z, 0 <= i < Zlength vals ->
     Znth (Znth i vals 0) tab 0 = T (Znth i vals 0) (Znth i freq 0)) ->
  (forall v : Z, 0 <= v <= maxv -> ~ In v vals -> Znth v tab 0 = 0) ->
  sum_range 1 u (fun i => Znth (i * d) tab 0)
  = fold_right Z.add 0
      (map (fun p : Z * Z => if (fst p) mod d =? 0 then T (fst p) (snd p) else 0)
           (combine vals freq)).
Proof.
  intros T tab vals freq d u maxv Hnd Hlen Hd Hu Hud Hmax Hvals Htab Hzero.
  rewrite (fold_combine_as_range__sieve_math_core
             (fun v f => if v mod d =? 0 then T v f else 0) vals freq Hlen).
  unfold sum_range.
  transitivity
    (sum (fun i => 1 <= i < u + 1)
       (fun i => sum (fun j => 0 <= j < Zlength vals)
          (fun j => if Znth j vals 0 =? i * d
                    then T (Znth j vals 0) (Znth j freq 0) else 0))).
  { apply sum_Z_range_ext. intros i Hi.
    apply (table_entry_sum__sieve_math_core T tab vals freq (i * d) maxv Hnd);
      [ split; nia | exact Htab | exact Hzero ]. }
  rewrite sum_range_swap__sieve_math_core.
  apply sum_Z_range_ext. intros j Hj.
  pose proof (Hvals j Hj) as Hvj.
  destruct (Znth j vals 0 mod d =? 0) eqn:Hdvd.
  - apply Z.eqb_eq in Hdvd.
    assert (Hv : Znth j vals 0 = d * (Znth j vals 0 / d))
      by (apply (Z.div_exact (Znth j vals 0) d); [lia | exact Hdvd]).
    assert (Hi0 : 1 <= Znth j vals 0 / d < u + 1) by nia.
    assert (Hz : forall i : Z, 1 <= i < u + 1 -> i <> Znth j vals 0 / d ->
              (if Znth j vals 0 =? i * d
               then T (Znth j vals 0) (Znth j freq 0) else 0) = 0).
    { intros i Hi Hne. destruct (Znth j vals 0 =? i * d) eqn:Hq; [| reflexivity].
      exfalso. apply Z.eqb_eq in Hq. apply Hne. nia. }
    rewrite (sum_range_one_hot__sieve_math_core 1 (u + 1) (Znth j vals 0 / d) _ Hi0 Hz).
    replace (Znth j vals 0 =? Znth j vals 0 / d * d) with true
      by (symmetry; apply Z.eqb_eq; lia).
    reflexivity.
  - apply sum_Z_range_eq_zero. intros i Hi.
    destruct (Znth j vals 0 =? i * d) eqn:Hq; [| reflexivity].
    exfalso. apply Z.eqb_eq in Hq.
    apply Z.eqb_neq in Hdvd. apply Hdvd.
    rewrite Hq. apply Z_mod_mult.
Qed.
Lemma Zlength_as_fold__sieve_math_core : forall l : list Z,
  Zlength l = fold_right Z.add 0 (map (fun _ : Z => 1) l).
Proof.
  induction l as [| a l IH]; [apply Zlength_nil |].
  cbn [map fold_right]. rewrite Zlength_cons, IH. unfold Z.succ. ring.
Qed.
Lemma fold_map_ext_list__sieve_math_core :
  forall (A : Type) (f g : A -> Z) (L : list A),
  (forall a : A, f a = g a) ->
  fold_right Z.add 0 (map f L) = fold_right Z.add 0 (map g L).
Proof.
  intros A f g L H. induction L as [| a L IH]; cbn [map fold_right]; [reflexivity |].
  rewrite IH, H. reflexivity.
Qed.
Lemma fold_map_mod_cong__sieve_math_core :
  forall (A : Type) (f g : A -> Z) (L : list A),
  (forall a : A, f a mod 998244353 = g a mod 998244353) ->
  fold_right Z.add 0 (map f L) mod 998244353
  = fold_right Z.add 0 (map g L) mod 998244353.
Proof.
  intros A f g L H. induction L as [| a L IH]; cbn [map fold_right]; [reflexivity |].
  rewrite (Zplus_mod (f a)), (Zplus_mod (g a)), H, IH. reflexivity.
Qed.
Lemma map_idZ__sieve_math_core : forall l : list Z, map (fun y : Z => y) l = l.
Proof.
  induction l as [| a l IH]; cbn [map]; [reflexivity |]. rewrite IH. reflexivity.
Qed.
Lemma pool_multiples_aggregate__sieve_math_core :
  forall (vals freq cnts sums squares : list Z) (d u maxv : Z),
  NoDup vals ->
  Zlength freq = Zlength vals ->
  aggregate_arrays vals freq cnts sums squares maxv ->
  1 <= d -> 0 <= u -> u * d <= maxv -> maxv < (u + 1) * d ->
  (forall i : Z, 0 <= i < Zlength vals -> 1 <= Znth i vals 0 <= maxv) ->
  (forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0) ->
  multiple_prefix_sum cnts d u = Zlength (divisible_pool (expand vals freq) d)
  /\ multiple_prefix_sum sums d u mod 998244353
     = fold_right Z.add 0 (divisible_pool (expand vals freq) d) mod 998244353
  /\ multiple_prefix_sum squares d u mod 998244353
     = fold_right Z.add 0
         (map (fun y : Z => y * y) (divisible_pool (expand vals freq) d)) mod 998244353.
Proof.
  intros vals freq cnts sums squares d u maxv Hnd Hlen Hagg Hd Hu Hud Hmax Hvals Hfpos.
  destruct Hagg as (Hlc & Hls & Hlq & Hentry & Hzero).
  unfold multiple_prefix_sum.
  split; [| split].
  - rewrite (table_multiples_sum__sieve_math_core (fun _ f => f) cnts vals freq d u maxv
               Hnd Hlen Hd Hu Hud Hmax Hvals
               (fun i Hi => proj1 (Hentry i Hi))
               (fun v Hv Hnin => proj1 (Hzero v Hv Hnin))).
    rewrite Zlength_as_fold__sieve_math_core.
    rewrite (pool_fold_expand__sieve_math_core (fun _ : Z => 1) d vals freq Hlen Hfpos).
    apply fold_map_ext_list__sieve_math_core. intros [v f].
    cbn [fst snd]. destruct (v mod d =? 0); ring.
  - rewrite <- (map_idZ__sieve_math_core (divisible_pool (expand vals freq) d)).
    rewrite (table_multiples_sum__sieve_math_core
               (fun v f => (v * f) mod 998244353) sums vals freq d u maxv
               Hnd Hlen Hd Hu Hud Hmax Hvals
               (fun i Hi => proj1 (proj2 (Hentry i Hi)))
               (fun v Hv Hnin => proj1 (proj2 (Hzero v Hv Hnin)))).
    rewrite (pool_fold_expand__sieve_math_core (fun y : Z => y) d vals freq Hlen Hfpos).
    apply fold_map_mod_cong__sieve_math_core. intros [v f].
    cbn [fst snd]. destruct (v mod d =? 0); [apply Zmod_mod | reflexivity].
  - rewrite (table_multiples_sum__sieve_math_core
               (fun v f => (v * v * f) mod 998244353) squares vals freq d u maxv
               Hnd Hlen Hd Hu Hud Hmax Hvals
               (fun i Hi => proj2 (proj2 (Hentry i Hi)))
               (fun v Hv Hnin => proj2 (proj2 (Hzero v Hv Hnin)))).
    rewrite (pool_fold_expand__sieve_math_core (fun y : Z => y * y) d vals freq Hlen Hfpos).
    apply fold_map_mod_cong__sieve_math_core. intros [v f].
    cbn [fst snd]. destruct (v mod d =? 0); [apply Zmod_mod | reflexivity].
Qed.
Lemma In_le_maximum_value__sieve_math_core : forall (l : list Z) (x : Z),
  In x l -> x <= maximum_value l.
Proof.
  unfold maximum_value. induction l as [| a l IH]; cbn [In fold_right].
  - contradiction.
  - intros x [Heq | Hin].
    + subst a. apply Z.le_max_l.
    + apply Z.le_trans with (fold_right Z.max 1 l); [apply IH; exact Hin | apply Z.le_max_r].
Qed.
Lemma pool_weight_closed_form__sieve_math_core :
  forall (vals freq cnts sums squares : list Z) (d u maxv k S S2 : Z),
  NoDup vals ->
  Zlength freq = Zlength vals ->
  aggregate_arrays vals freq cnts sums squares maxv ->
  1 <= d -> 0 <= u -> u * d <= maxv -> maxv < (u + 1) * d ->
  (forall i : Z, 0 <= i < Zlength vals -> 1 <= Znth i vals 0 <= maxv) ->
  (forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0) ->
  PoolAggregate cnts sums squares d u k S S2 ->
  pool_closed_form k S S2 = pool_weight vals freq d mod 998244353.
Proof.
  intros vals freq cnts sums squares d u maxv k S S2
         Hnd Hlen Hagg Hd Hu Hud Hmax Hvals Hfpos HPA.
  destruct (pool_multiples_aggregate__sieve_math_core vals freq cnts sums squares d u maxv
              Hnd Hlen Hagg Hd Hu Hud Hmax Hvals Hfpos) as (H1 & H2 & H3).
  destruct HPA as (Hk & HS & HS2).
  unfold pool_weight.
  rewrite subset_weight_sum_closed_form__sieve_math_core.
  rewrite Hk, H1, HS, H2, HS2, H3. reflexivity.
Qed.
Lemma peel_state_init__sieve_math_core :
  forall (vals freq cnts sums squares : list Z) (d t maxv k S S2 retval v : Z),
  Pre vals freq ->
  Zlength freq = Zlength vals ->
  (forall i : Z, 0 <= i < Zlength vals -> 1 <= Znth i vals 0 <= 100000) ->
  (forall i : Z, 0 <= i < Zlength freq -> 1 <= Znth i freq 0 <= 1000000000) ->
  maxv = maximum_value vals ->
  aggregate_arrays vals freq cnts sums squares maxv ->
  1 <= d -> 1 <= t -> v = t * d -> v > maxv -> (t - 1) * d <= maxv ->
  PoolAggregate cnts sums squares d (t - 1) k S S2 ->
  retval = pool_closed_form k S S2 ->
  PeelState vals freq d 1 retval.
Proof.
  intros vals freq cnts sums squares d t maxv k S S2 retval v
         HPre Hlen Hvals Hfreq Hmaxv Hagg Hd Ht Hv Hvm Htd HPA Hret.
  unfold Pre in HPre.
  assert (Hvb : forall i : Z, 0 <= i < Zlength vals -> 1 <= Znth i vals 0 <= maxv).
  { intros i Hi. split; [ apply (Hvals i Hi) |].
    rewrite Hmaxv. apply In_le_maximum_value__sieve_math_core.
    apply Znth_In_Zlength. exact Hi. }
  assert (Hfb : forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0).
  { intros i Hi. pose proof (Hfreq i Hi). lia. }
  assert (Hlt : maxv < (t - 1 + 1) * d) by nia.
  unfold PeelState, sum_range.
  rewrite (sum_Z_range_empty 2 (1 + 1)) by lia.
  rewrite Z.sub_0_r, Hret.
  exact (pool_weight_closed_form__sieve_math_core vals freq cnts sums squares d (t - 1) maxv
           k S S2 HPre Hlen Hagg Hd ltac:(lia) Htd Hlt Hvb Hfb HPA).
Qed.
Lemma In_sub_multisets__sieve_math_core : forall (l A : list Z) (x : Z),
  In A (sub_multisets l) -> In x A -> In x l.
Proof.
  induction l as [| a l IH]; intros A x HA Hx.
  - cbn [sub_multisets] in HA. destruct HA as [Heq | []]. subst A. contradiction.
  - cbn [sub_multisets] in HA. apply in_app_or in HA as [HA | HA].
    + apply in_map_iff in HA as [A' [Heq HA']]. subst A.
      destruct Hx as [Heq | Hx]; [left; exact Heq | right; apply (IH A' x HA' Hx)].
    + right. apply (IH A x HA Hx).
Qed.
Lemma gcd_divides_elem__sieve_math_core : forall (A : list Z) (x : Z),
  In x A -> Z.divide (fold_right Z.gcd 0 A) x.
Proof.
  induction A as [| a A IH]; intros x Hx; [contradiction |].
  cbn [fold_right]. destruct Hx as [Heq | Hx].
  - subst a. apply Z.gcd_divide_l.
  - apply Z.divide_trans with (fold_right Z.gcd 0 A);
      [apply Z.gcd_divide_r | apply IH; exact Hx].
Qed.
Lemma d_divides_gcd__sieve_math_core : forall (A : list Z) (d : Z),
  (forall x : Z, In x A -> Z.divide d x) -> Z.divide d (fold_right Z.gcd 0 A).
Proof.
  induction A as [| a A IH]; intros d H; cbn [fold_right].
  - apply Z.divide_0_r.
  - apply Z.gcd_greatest.
    + apply H. left. reflexivity.
    + apply IH. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma gcd_pos__sieve_math_core : forall A : list Z,
  A <> nil -> (forall x : Z, In x A -> 1 <= x) -> 1 <= fold_right Z.gcd 0 A.
Proof.
  intros A Hne H. destruct A as [| a A]; [contradiction |].
  cbn [fold_right].
  assert (Ha : 1 <= a) by (apply H; left; reflexivity).
  pose proof (Z.gcd_nonneg a (fold_right Z.gcd 0 A)) as Hnn.
  destruct (Z.eq_dec (Z.gcd a (fold_right Z.gcd 0 A)) 0) as [Heq | Hne0].
  - apply Z.gcd_eq_0_l in Heq. lia.
  - lia.
Qed.
Lemma gcd_le__sieve_math_core : forall (A : list Z) (a : Z),
  In a A -> 1 <= a -> fold_right Z.gcd 0 A <= a.
Proof.
  intros A a Ha Hpos.
  apply Z.divide_pos_le; [lia | apply gcd_divides_elem__sieve_math_core; exact Ha].
Qed.
Lemma In_expand__sieve_math_core : forall (vals freq : list Z) (x : Z),
  In x (expand vals freq) -> In x vals.
Proof.
  induction vals as [| v vs IH]; intros freq x H; [cbn [expand] in H; contradiction |].
  destruct freq as [| f fs]; [cbn [expand] in H; contradiction |].
  cbn [expand] in H. apply in_app_or in H as [H | H].
  - left. symmetry. apply (repeat_spec _ _ _ H).
  - right. apply (IH fs x H).
Qed.
Lemma filter_map_cons__sieve_math_core :
  forall (x : Z) (q : list Z -> bool) (L : list (list Z)),
  filter q (map (cons x) L) = map (cons x) (filter (fun A => q (x :: A)) L).
Proof.
  intros x q L. induction L as [| A L IH]; cbn [map filter]; [reflexivity |].
  destruct (q (x :: A)); cbn [map]; rewrite IH; reflexivity.
Qed.
Lemma filter_all_false__sieve_math_core :
  forall (g : list Z -> bool) (L : list (list Z)),
  (forall A : list Z, g A = false) -> filter g L = nil.
Proof.
  intros g L H. induction L as [| A L IH]; cbn [filter]; [reflexivity |].
  rewrite H. exact IH.
Qed.
Lemma sub_multisets_filter__sieve_math_core :
  forall (p : Z -> bool) (l : list Z) (q : list Z -> bool) (f : list Z -> Z),
  (forall A : list Z, q A = true -> Forall (fun x => p x = true) A) ->
  fold_right Z.add 0 (map f (filter q (sub_multisets (filter p l))))
  = fold_right Z.add 0 (map f (filter q (sub_multisets l))).
Proof.
  intros p l. induction l as [| x l IH]; intros q f Hq.
  - reflexivity.
  - cbn [filter]. destruct (p x) eqn:Hpx.
    + cbn [sub_multisets].
      rewrite !filter_app, !map_app, !fold_add_app__sieve_math_core.
      rewrite !filter_map_cons__sieve_math_core, !map_map.
      f_equal.
      * apply (IH (fun A => q (x :: A)) (fun A => f (x :: A))).
        intros A HA. specialize (Hq (x :: A) HA).
        inversion Hq as [| y ys Hy HFA]; exact HFA.
      * apply (IH q f Hq).
    + cbn [sub_multisets].
      rewrite filter_app, map_app, fold_add_app__sieve_math_core.
      rewrite filter_map_cons__sieve_math_core.
      rewrite (filter_all_false__sieve_math_core (fun A => q (x :: A)) (sub_multisets l)).
      * cbn [map fold_right]. rewrite (IH q f Hq). ring.
      * intros A. destruct (q (x :: A)) eqn:HqA; [| reflexivity].
        exfalso. specialize (Hq (x :: A) HqA).
        inversion Hq as [| y ys Hy HFA]. rewrite Hy in Hpx. discriminate.
Qed.
Lemma subset_weight_nil__sieve_math_core : subset_weight nil = 0.
Proof.
  unfold subset_weight. rewrite Zlength_nil. cbn [fold_right].
  rewrite Z.pow_2_r. ring.
Qed.
Lemma fold_partition_by_gcd__sieve_math_core :
  forall (f : list Z -> Z) (d u : Z) (L : list (list Z)),
  1 <= d -> 0 <= u ->
  (forall A : list Z, In A L ->
     (exists i : Z, 1 <= i <= u /\ fold_right Z.gcd 0 A = i * d) \/ f A = 0) ->
  fold_right Z.add 0 (map f L)
  = sum_range 1 u
      (fun i => fold_right Z.add 0
                  (map f (filter (fun A => fold_right Z.gcd 0 A =? i * d) L))).
Proof.
  intros f d u L Hd Hu HL.
  induction L as [| A L IH].
  - cbn [map fold_right filter]. unfold sum_range.
    symmetry. apply sum_Z_range_eq_zero. intros i Hi. reflexivity.
  - cbn [map fold_right].
    rewrite IH by (intros B HB; apply HL; right; exact HB).
    unfold sum_range.
    transitivity
      (sum (fun i => 1 <= i < u + 1)
           (fun i => if fold_right Z.gcd 0 A =? i * d then f A else 0)
       + sum (fun i => 1 <= i < u + 1)
             (fun i => fold_right Z.add 0
                         (map f (filter (fun B => fold_right Z.gcd 0 B =? i * d) L)))).
    2:{ rewrite <- sum_Z_range_add. apply sum_Z_range_ext. intros i Hi.
        cbn [filter]. destruct (fold_right Z.gcd 0 A =? i * d);
          cbn [map fold_right]; ring. }
    f_equal.
    destruct (HL A (or_introl eq_refl)) as [[i0 [Hi0 Hkey]] | Hf0].
    + assert (Hz : forall i : Z, 1 <= i < u + 1 -> i <> i0 ->
                (if fold_right Z.gcd 0 A =? i * d then f A else 0) = 0).
      { intros i Hi Hne. destruct (fold_right Z.gcd 0 A =? i * d) eqn:E; [| reflexivity].
        exfalso. apply Z.eqb_eq in E. apply Hne. nia. }
      rewrite (sum_range_one_hot__sieve_math_core 1 (u + 1) i0 _ ltac:(lia) Hz).
      rewrite Hkey, Z.eqb_refl. reflexivity.
    + rewrite (sum_Z_range_eq_zero 1 (u + 1)).
      * exact Hf0.
      * intros i Hi. destruct (fold_right Z.gcd 0 A =? i * d); [exact Hf0 | reflexivity].
Qed.
Lemma pool_weight_peel_partition__sieve_math_core :
  forall (vals freq : list Z) (d u maxv : Z),
  1 <= d -> 0 <= u -> u * d <= maxv -> maxv < (u + 1) * d ->
  (forall x : Z, In x vals -> 1 <= x <= maxv) ->
  pool_weight vals freq d
  = sum_range 1 u (fun i => exact_gcd_weight vals freq (i * d)).
Proof.
  intros vals freq d u maxv Hd Hu Hud Hmax Hvals.
  unfold pool_weight, subset_weight_sum, divisible_pool, exact_gcd_weight.
  rewrite (fold_partition_by_gcd__sieve_math_core subset_weight d u
             (sub_multisets (filter (fun x => x mod d =? 0) (expand vals freq))) Hd Hu).
  - unfold sub_multisets at 1. fold sub_multisets.
    unfold sum_range. apply sum_Z_range_ext. intros i Hi.
    apply (sub_multisets_filter__sieve_math_core (fun x => x mod d =? 0) (expand vals freq)
             (fun A => fold_right Z.gcd 0 A =? i * d) subset_weight).
    intros A HA. apply Z.eqb_eq in HA.
    rewrite Forall_forall. intros x Hx.
    apply Z.eqb_eq. apply Z.mod_divide; [lia |].
    apply Z.divide_trans with (fold_right Z.gcd 0 A).
    + rewrite HA. exists i. ring.
    + apply gcd_divides_elem__sieve_math_core. exact Hx.
  - intros A HA.
    assert (Hmem : forall x : Z, In x A -> 1 <= x <= maxv /\ Z.divide d x).
    { intros x Hx.
      pose proof (In_sub_multisets__sieve_math_core _ _ _ HA Hx) as Hxf.
      apply filter_In in Hxf as [Hxs Hxd].
      split.
      - apply Hvals. apply (In_expand__sieve_math_core vals freq x Hxs).
      - apply Z.mod_divide; [lia | apply Z.eqb_eq; exact Hxd]. }
    destruct A as [| a A'].
    + right. apply subset_weight_nil__sieve_math_core.
    + left.
      assert (Hane : In a (a :: A')) by (left; reflexivity).
      destruct (Hmem a Hane) as [Ha _].
      assert (Hg1 : 1 <= fold_right Z.gcd 0 (a :: A')).
      { apply gcd_pos__sieve_math_core; [discriminate |].
        intros x Hx. apply (proj1 (Hmem x Hx)). }
      assert (Hg2 : fold_right Z.gcd 0 (a :: A') <= maxv).
      { apply Z.le_trans with a; [| lia].
        apply gcd_le__sieve_math_core; [exact Hane | lia]. }
      assert (Hgd : Z.divide d (fold_right Z.gcd 0 (a :: A'))).
      { apply d_divides_gcd__sieve_math_core.
        intros x Hx. apply (proj2 (Hmem x Hx)). }
      destruct Hgd as [m Hm].
      exists m. split; [| lia].
      nia.
Qed.
Lemma vals_in_bounds__sieve_math_core :
  forall (vals : list Z) (maxv : Z),
  maxv = maximum_value vals ->
  (forall i : Z, 0 <= i < Zlength vals -> 1 <= Znth i vals 0 <= 100000) ->
  forall x : Z, In x vals -> 1 <= x <= maxv.
Proof.
  intros vals maxv Hm Hb x Hx.
  destruct (In_Znth__sieve_math_core vals x Hx) as [j [Hj Heq]].
  split.
  - rewrite <- Heq. apply (Hb j Hj).
  - rewrite Hm. apply In_le_maximum_value__sieve_math_core. exact Hx.
Qed.
Lemma ans_exact_prefix_step__sieve_math_core :
  forall (vals freq anslist : list Z) (d t maxv cur v : Z),
  Zlength anslist = maxv + 1 ->
  (forall x : Z, In x vals -> 1 <= x <= maxv) ->
  1 <= d -> d <= maxv -> 2 <= t -> v = t * d -> v > maxv -> v <= maxv + d ->
  PeelState vals freq d (t - 1) cur ->
  AnsExactPrefix vals freq maxv anslist d ->
  AnsExactPrefix vals freq maxv (replace_Znth d cur anslist) (d - 1).
Proof.
  intros vals freq anslist d t maxv cur v Hlen Hvals Hd Hdm Ht Hv Hvm Hvd HPeel HAns.
  assert (Hu : 0 <= t - 1) by lia.
  assert (Hud : (t - 1) * d <= maxv) by nia.
  assert (Hmx : maxv < (t - 1 + 1) * d) by nia.
  assert (Hpart : pool_weight vals freq d
                  = sum_range 1 (t - 1) (fun i => exact_gcd_weight vals freq (i * d)))
    by (apply (pool_weight_peel_partition__sieve_math_core vals freq d (t - 1) maxv);
        assumption).
  assert (Hcur : cur = exact_gcd_weight vals freq d mod 998244353).
  { unfold PeelState in HPeel.
    rewrite Hpart in HPeel.
    unfold sum_range in HPeel.
    rewrite (sum_Z_range_cons 1 (t - 1 + 1)) in HPeel by lia.
    cbv beta in HPeel.
    rewrite Z.mul_1_l in HPeel.
    replace (1 + 1) with 2 in HPeel by lia.
    rewrite Z.add_simpl_r in HPeel.
    exact HPeel. }
  unfold AnsExactPrefix. intros w Hw.
  destruct (Z.eq_dec w d) as [Heq | Hne].
  - subst w. rewrite Znth_replace_Znth_Same by lia. exact Hcur.
  - rewrite Znth_replace_Znth_Diff by lia. apply HAns. lia.
Qed.
Lemma fold_one_filter__sieve_math_core : forall (g : Z -> bool) (l : list Z),
  fold_right (fun (_ : Z) (acc : Z) => 1 + acc) 0 (filter g l)
  = fold_right Z.add 0 (map (fun x : Z => if g x then 1 else 0) l).
Proof.
  intros g l. induction l as [| a l IH]; cbn [filter map fold_right]; [reflexivity |].
  destruct (g a); cbn [fold_right]; lia.
Qed.
Lemma fold_fun_map__sieve_math_core : forall (g : Z -> Z) (l : list Z),
  fold_right (fun (x : Z) (acc : Z) => g x + acc) 0 l = fold_right Z.add 0 (map g l).
Proof.
  intros g l. induction l as [| a l IH]; cbn [map fold_right]; [reflexivity |].
  rewrite IH. reflexivity.
Qed.
Lemma fold_map_as_range__sieve_math_core : forall (g : Z -> Z) (l : list Z),
  fold_right Z.add 0 (map g l)
  = sum (fun i => 0 <= i < Zlength l) (fun i => g (Znth i l 0)).
Proof.
  intros g l. induction l as [| a l IH].
  - cbn [map fold_right]. rewrite Zlength_nil.
    rewrite sum_Z_range_empty by lia. reflexivity.
  - cbn [map fold_right]. rewrite IH, Zlength_cons.
    pose proof (Zlength_nonneg l) as Hnn.
    rewrite (sum_Z_range_cons 0 (Z.succ (Zlength l))) by lia.
    cbv beta. rewrite Znth0_cons. f_equal.
    replace (Z.succ (Zlength l)) with (Zlength l + 1) by lia.
    rewrite sum_Z_range_shift_1.
    apply sum_Z_range_ext. intros i Hi.
    rewrite Znth_cons by lia.
    replace (i + 1 - 1) with i by lia. reflexivity.
Qed.
Lemma set_card_count__sieve_math_core : forall (s : list Z) (v : Z),
  @set_card Z (fun j : Z => 0 <= j < Zlength s /\ Znth j s 0 = v)
    (finite_Z_range' 0 (Zlength s) (fun x : Z => Znth x s 0 = v))
  = fold_right Z.add 0 (map (fun y : Z => if y =? v then 1 else 0) s).
Proof.
  intros s v.
  rewrite (fold_map_as_range__sieve_math_core (fun y : Z => if y =? v then 1 else 0) s).
  unfold set_card, sum. cbn [enum finite_Z_range' finite_Z_range]. cbv beta.
  rewrite fold_one_filter__sieve_math_core.
  rewrite (fold_fun_map__sieve_math_core
             (fun x : Z => if Znth x s 0 =? v then 1 else 0) (Zrange 0 (Zlength s))).
  f_equal. apply map_ext. intros x.
  destruct (prop_dec (Znth x s 0 = v)) as [He | He];
    destruct (Znth x s 0 =? v) eqn:Hb; try reflexivity.
  - apply Z.eqb_neq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
Qed.
Lemma fold_expand_filter__sieve_math_core :
  forall (h : Z -> Z) (c : Z -> bool) (vals freq : list Z),
  Zlength freq = Zlength vals ->
  (forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0) ->
  fold_right Z.add 0 (map h (filter c (expand vals freq)))
  = fold_right Z.add 0
      (map (fun p : Z * Z => if c (fst p) then h (fst p) * snd p else 0)
           (combine vals freq)).
Proof.
  intros h c vals.
  induction vals as [| v vs IH]; intros freq Hlen Hpos.
  - cbn [expand filter map fold_right combine]. reflexivity.
  - destruct freq as [| f fs].
    { exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg vs). unfold Z.succ in Hlen. lia. }
    assert (Hf : 0 <= f).
    { specialize (Hpos 0). rewrite Znth0_cons in Hpos. apply Hpos.
      rewrite Zlength_cons. pose proof (Zlength_nonneg fs). unfold Z.succ. lia. }
    rewrite !Zlength_cons in Hlen.
    cbn [expand].
    rewrite filter_app, map_app, fold_add_app__sieve_math_core.
    rewrite (fold_map_filter_repeat__sieve_math_core h c v (Z.to_nat f)).
    rewrite (IH fs) by
      (try lia;
       intros i Hi; specialize (Hpos (i + 1));
       rewrite Znth_cons in Hpos by lia;
       replace (i + 1 - 1) with i in Hpos by lia;
       apply Hpos; rewrite Zlength_cons; unfold Z.succ; lia).
    cbn [combine map fold_right fst snd].
    rewrite Z2Nat.id by lia.
    destruct (c v); ring.
Qed.
Lemma count_as_filter__sieve_math_core : forall (c : Z -> bool) (l : list Z),
  fold_right Z.add 0 (map (fun y : Z => if c y then 1 else 0) l)
  = fold_right Z.add 0 (map (fun _ : Z => 1) (filter c l)).
Proof.
  intros c l. induction l as [| a l IH]; cbn [map filter fold_right]; [reflexivity |].
  destruct (c a); cbn [map fold_right]; lia.
Qed.
Lemma Zlength_repeat__sieve_math_core : forall (v : Z) (n : nat),
  Zlength (repeat v n) = Z.of_nat n.
Proof.
  intros v n. induction n as [| n IH]; [apply Zlength_nil |].
  cbn [repeat]. rewrite Zlength_cons, IH, Nat2Z.inj_succ. reflexivity.
Qed.
Lemma Zlength_expand__sieve_math_core : forall vals freq : list Z,
  Zlength freq = Zlength vals ->
  (forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0) ->
  Zlength (expand vals freq) = fold_right Z.add 0 freq.
Proof.
  induction vals as [| v vs IH]; intros freq Hlen Hpos.
  - destruct freq as [| f fs].
    + reflexivity.
    + exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg fs). unfold Z.succ in Hlen. lia.
  - destruct freq as [| f fs].
    { exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg vs). unfold Z.succ in Hlen. lia. }
    assert (Hf : 0 <= f).
    { specialize (Hpos 0). rewrite Znth0_cons in Hpos. apply Hpos.
      rewrite Zlength_cons. pose proof (Zlength_nonneg fs). unfold Z.succ. lia. }
    rewrite !Zlength_cons in Hlen.
    cbn [expand fold_right].
    rewrite Zlength_app, Zlength_repeat__sieve_math_core, Z2Nat.id by lia.
    rewrite (IH fs) by
      (try lia;
       intros i Hi; specialize (Hpos (i + 1));
       rewrite Znth_cons in Hpos by lia;
       replace (i + 1 - 1) with i in Hpos by lia;
       apply Hpos; rewrite Zlength_cons; unfold Z.succ; lia).
    reflexivity.
Qed.
Lemma count_expand__sieve_math_core :
  forall (vals freq : list Z) (i : Z),
  NoDup vals -> Zlength freq = Zlength vals ->
  (forall j : Z, 0 <= j < Zlength freq -> 0 <= Znth j freq 0) ->
  0 <= i < Zlength vals ->
  fold_right Z.add 0
    (map (fun y : Z => if y =? Znth i vals 0 then 1 else 0) (expand vals freq))
  = Znth i freq 0.
Proof.
  intros vals freq i Hnd Hlen Hpos Hi.
  rewrite count_as_filter__sieve_math_core.
  rewrite (fold_expand_filter__sieve_math_core (fun _ : Z => 1)
             (fun y : Z => y =? Znth i vals 0) vals freq Hlen Hpos).
  rewrite (fold_combine_as_range__sieve_math_core
             (fun v f => if v =? Znth i vals 0 then 1 * f else 0) vals freq Hlen).
  assert (Hz : forall j : Z, 0 <= j < Zlength vals -> j <> i ->
            (if Znth j vals 0 =? Znth i vals 0 then 1 * Znth j freq 0 else 0) = 0).
  { intros j Hj Hne. destruct (Znth j vals 0 =? Znth i vals 0) eqn:E; [| reflexivity].
    exfalso. apply Z.eqb_eq in E. apply Hne.
    apply (NoDup_Znth_inj__sieve_math_core vals j i Hnd Hj Hi E). }
  rewrite (sum_range_one_hot__sieve_math_core 0 (Zlength vals) i _ Hi Hz).
  rewrite Z.eqb_refl. ring.
Qed.
Lemma expand_is_expanded_multiset__sieve_math_core :
  forall vals freq : list Z,
  NoDup vals -> Zlength freq = Zlength vals ->
  (forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0) ->
  ExpandedMultiset vals freq (expand vals freq).
Proof.
  intros vals freq Hnd Hlen Hpos.
  unfold ExpandedMultiset. split; [| split].
  - apply Zlength_expand__sieve_math_core; assumption.
  - rewrite Forall_forall. intros x Hx.
    apply (In_expand__sieve_math_core vals freq x Hx).
  - intros i Hi.
    rewrite set_card_count__sieve_math_core.
    apply count_expand__sieve_math_core; assumption.
Qed.
Lemma bits_succ__sieve_math_core : forall (x : Z) (s : list Z),
  all_lists (length (x :: s)) (1 :: 0 :: nil)
  = map (cons 1) (all_lists (length s) (1 :: 0 :: nil))
    ++ map (cons 0) (all_lists (length s) (1 :: 0 :: nil)).
Proof.
  intros x s. cbn [length all_lists flat_map]. rewrite app_nil_r. reflexivity.
Qed.
Lemma sel_cons1__sieve_math_core : forall (A s : list Z) (x : Z),
  map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine (1 :: A) (x :: s)))
  = x :: map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine A s)).
Proof. intros A s x. cbn [combine filter fst snd map]. reflexivity. Qed.
Lemma sel_cons0__sieve_math_core : forall (A s : list Z) (x : Z),
  map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine (0 :: A) (x :: s)))
  = map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine A s)).
Proof. intros A s x. cbn [combine filter fst snd map]. reflexivity. Qed.
Lemma eqb_shift__sieve_math_core : forall a b c : Z, (c + a =? b) = (a =? b - c).
Proof.
  intros a b c.
  destruct (c + a =? b) eqn:E1; destruct (a =? b - c) eqn:E2; try reflexivity.
  - exfalso. apply Z.eqb_eq in E1. apply Z.eqb_neq in E2. lia.
  - exfalso. apply Z.eqb_neq in E1. apply Z.eqb_eq in E2. lia.
Qed.
Lemma filter_false_in__sieve_math_core :
  forall (g : list Z -> bool) (L : list (list Z)),
  (forall A : list Z, In A L -> g A = false) -> filter g L = nil.
Proof.
  intros g L H. induction L as [| A L IH]; cbn [filter]; [reflexivity |].
  rewrite (H A (or_introl eq_refl)). apply IH.
  intros B HB. apply H. right. exact HB.
Qed.
Lemma lepw_sum_le__sieve_math_core : forall A B : list Z,
  length B = length A ->
  forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B) = true ->
  fold_right Z.add 0 B <= fold_right Z.add 0 A.
Proof.
  induction A as [| a A IH]; intros B Hlen Hle.
  - destruct B as [| b B]; [cbn; lia | cbn in Hlen; discriminate].
  - destruct B as [| b B]; [cbn in Hlen; discriminate |].
    cbn [combine forallb fst snd] in Hle.
    apply andb_true_iff in Hle as [Hb Hrest].
    apply Z.leb_le in Hb.
    cbn [length] in Hlen.
    pose proof (IH B ltac:(lia) Hrest).
    cbn [fold_right]. lia.
Qed.
Lemma bits_length__sieve_math_core : forall (s B : list Z),
  In B (all_lists (length s) (1 :: 0 :: nil)) -> length B = length s.
Proof.
  intros s B HB. apply in_all_lists in HB as [Hlen _]. exact Hlen.
Qed.
Lemma bits_forall01__sieve_math_core : forall (s B : list Z),
  In B (all_lists (length s) (1 :: 0 :: nil)) ->
  Forall (fun x : Z => x = 0 \/ x = 1) B.
Proof.
  intros s B HB. apply in_all_lists in HB as [_ Hfa].
  rewrite Forall_forall in Hfa |- *. intros x Hx.
  destruct (Hfa x Hx) as [H1 | [H0 | []]]; [right | left]; auto.
Qed.
Lemma eqs_filter__sieve_math_core : forall (s A : list Z),
  length A = length s ->
  Forall (fun x : Z => x = 0 \/ x = 1) A ->
  filter (fun B : list Z =>
            andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B))
                 (Z.eqb (fold_right Z.add 0 B) (fold_right Z.add 0 A)))
         (all_lists (length s) (1 :: 0 :: nil))
  = A :: nil.
Proof.
  induction s as [| x s IH]; intros A Hlen HA.
  - destruct A as [| a A]; [| cbn in Hlen; discriminate].
    cbn [length all_lists filter combine forallb fold_right]. reflexivity.
  - destruct A as [| a A]; [cbn in Hlen; discriminate |].
    cbn [length] in Hlen. apply Nat.succ_inj in Hlen.
    inversion HA as [| y ys Hy HA']; subst.
    rewrite bits_succ__sieve_math_core.
    rewrite filter_app, !filter_map_cons__sieve_math_core.
    destruct Hy as [Ha | Ha]; subst a.
    + (* a = 0 : only b = 0 survives *)
      rewrite (filter_false_in__sieve_math_core
                 (fun B => andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                                   (combine (0 :: A) (1 :: B)))
                             (Z.eqb (fold_right Z.add 0 (1 :: B))
                                    (fold_right Z.add 0 (0 :: A))))).
      * cbn [map]. cbn [app].
        replace (filter (fun B : list Z =>
                   andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                           (combine (0 :: A) (0 :: B)))
                        (Z.eqb (fold_right Z.add 0 (0 :: B))
                               (fold_right Z.add 0 (0 :: A))))
                  (all_lists (length s) (1 :: 0 :: nil)))
          with (A :: nil).
        { reflexivity. }
        rewrite <- (IH A Hlen HA'). apply filter_ext.
        intros B. cbn [combine forallb fold_right fst snd]. reflexivity.
      * intros B HB. cbn [combine forallb fold_right fst snd]. reflexivity.
    + (* a = 1 *)
      rewrite (filter_false_in__sieve_math_core
                 (fun B => andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                                   (combine (1 :: A) (0 :: B)))
                             (Z.eqb (fold_right Z.add 0 (0 :: B))
                                    (fold_right Z.add 0 (1 :: A))))
                 (all_lists (length s) (1 :: 0 :: nil))).
      * replace (filter (fun B : list Z =>
                   andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                           (combine (1 :: A) (1 :: B)))
                        (Z.eqb (fold_right Z.add 0 (1 :: B))
                               (fold_right Z.add 0 (1 :: A))))
                  (all_lists (length s) (1 :: 0 :: nil)))
          with (A :: nil).
        { cbn [map app]. reflexivity. }
        rewrite <- (IH A Hlen HA'). apply filter_ext.
        intros B. cbn [combine forallb fold_right fst snd].
        try rewrite Z.leb_refl. cbn [andb].
        rewrite eqb_shift__sieve_math_core.
        replace (1 + fold_right Z.add 0 A - 1) with (fold_right Z.add 0 A) by lia.
        reflexivity.
      * intros B HB.
        cbn [combine forallb fold_right fst snd].
        destruct (forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B)) eqn:Hlp.
        2:{ rewrite Bool.andb_false_r. reflexivity. }
        cbn [andb]. try rewrite Z.leb_refl. cbn [andb].
        apply Z.eqb_neq.
        assert (HlB : length B = length A)
          by (rewrite Hlen; apply (bits_length__sieve_math_core s B HB)).
        pose proof (lepw_sum_le__sieve_math_core A B HlB Hlp).
        lia.
Qed.
Lemma fold_sel_map_cons1__sieve_math_core :
  forall (x : Z) (s : list Z) (L : list (list Z)),
  fold_right Z.add 0
    (map (fun B : list Z =>
            fold_right Z.add 0
              (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine B (x :: s)))))
         (map (cons 1) L))
  = x * Zlength L
    + fold_right Z.add 0
        (map (fun B : list Z =>
                fold_right Z.add 0
                  (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine B s))))
             L).
Proof.
  intros x s L. induction L as [| B L IH]; cbn [map fold_right].
  - rewrite Zlength_nil. ring.
  - rewrite IH, sel_cons1__sieve_math_core.
    cbn [map fold_right]. rewrite Zlength_cons. unfold Z.succ. ring.
Qed.
Lemma fold_sel_map_cons0__sieve_math_core :
  forall (x : Z) (s : list Z) (L : list (list Z)),
  fold_right Z.add 0
    (map (fun B : list Z =>
            fold_right Z.add 0
              (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine B (x :: s)))))
         (map (cons 0) L))
  = fold_right Z.add 0
      (map (fun B : list Z =>
              fold_right Z.add 0
                (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine B s))))
           L).
Proof.
  intros x s L. induction L as [| B L IH]; cbn [map fold_right]; [reflexivity |].
  rewrite IH, sel_cons0__sieve_math_core. reflexivity.
Qed.
Lemma drops_count_sum__sieve_math_core : forall (s A : list Z),
  length A = length s ->
  Forall (fun x : Z => x = 0 \/ x = 1) A ->
  Zlength (filter (fun B : list Z =>
             andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B))
                  (Z.eqb (fold_right Z.add 0 B) (fold_right Z.add 0 A - 1)))
             (all_lists (length s) (1 :: 0 :: nil)))
  = Zlength (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine A s)))
  /\ fold_right Z.add 0
       (map (fun B : list Z =>
               fold_right Z.add 0
                 (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine B s))))
            (filter (fun B : list Z =>
               andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B))
                    (Z.eqb (fold_right Z.add 0 B) (fold_right Z.add 0 A - 1)))
               (all_lists (length s) (1 :: 0 :: nil))))
     = (Zlength (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine A s))) - 1)
       * fold_right Z.add 0
           (map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine A s))).
Proof.
  induction s as [| x s IH]; intros A Hlen HA.
  - destruct A as [| a A]; [| cbn in Hlen; discriminate].
    cbn. split; [reflexivity | ring].
  - destruct A as [| a A]; [cbn in Hlen; discriminate |].
    cbn [length] in Hlen. apply Nat.succ_inj in Hlen.
    inversion HA as [| y ys Hy HA']; subst.
    destruct (IH A Hlen HA') as [ICount ISum].
    rewrite bits_succ__sieve_math_core.
    rewrite filter_app, !filter_map_cons__sieve_math_core.
    destruct Hy as [Ha | Ha]; subst a.
    + (* a = 0 *)
      rewrite (filter_false_in__sieve_math_core
                 (fun B : list Z =>
                    andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                            (combine (0 :: A) (1 :: B)))
                         (Z.eqb (fold_right Z.add 0 (1 :: B))
                                (fold_right Z.add 0 (0 :: A) - 1)))
                 (all_lists (length s) (1 :: 0 :: nil)))
        by (intros B HB; cbn [combine forallb fold_right fst snd]; reflexivity).
      rewrite (filter_ext
                 (fun B : list Z =>
                    andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                            (combine (0 :: A) (0 :: B)))
                         (Z.eqb (fold_right Z.add 0 (0 :: B))
                                (fold_right Z.add 0 (0 :: A) - 1)))
                 (fun B : list Z =>
                    andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B))
                         (Z.eqb (fold_right Z.add 0 B) (fold_right Z.add 0 A - 1))))
        by (intros B; cbn [combine forallb fold_right fst snd]; reflexivity).
      rewrite sel_cons0__sieve_math_core.
      cbn [map app].
      rewrite fold_sel_map_cons0__sieve_math_core.
      rewrite Zlength_map__sieve_math_core.
      split; [exact ICount | exact ISum].
    + (* a = 1 *)
      rewrite (filter_ext
                 (fun B : list Z =>
                    andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                            (combine (1 :: A) (1 :: B)))
                         (Z.eqb (fold_right Z.add 0 (1 :: B))
                                (fold_right Z.add 0 (1 :: A) - 1)))
                 (fun B : list Z =>
                    andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B))
                         (Z.eqb (fold_right Z.add 0 B) (fold_right Z.add 0 A - 1)))).
      2:{ intros B. cbn [combine forallb fold_right fst snd].
          try rewrite Z.leb_refl. cbn [andb].
          rewrite eqb_shift__sieve_math_core.
          replace (1 + fold_right Z.add 0 A - 1 - 1) with (fold_right Z.add 0 A - 1) by lia.
          reflexivity. }
      rewrite (filter_ext
                 (fun B : list Z =>
                    andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                            (combine (1 :: A) (0 :: B)))
                         (Z.eqb (fold_right Z.add 0 (0 :: B))
                                (fold_right Z.add 0 (1 :: A) - 1)))
                 (fun B : list Z =>
                    andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B))
                         (Z.eqb (fold_right Z.add 0 B) (fold_right Z.add 0 A)))).
      2:{ intros B. cbn [combine forallb fold_right fst snd].
          replace (1 + fold_right Z.add 0 A - 1) with (fold_right Z.add 0 A) by lia.
          reflexivity. }
      rewrite (eqs_filter__sieve_math_core s A Hlen HA').
      rewrite sel_cons1__sieve_math_core.
      rewrite map_app, fold_add_app__sieve_math_core.
      rewrite fold_sel_map_cons1__sieve_math_core, fold_sel_map_cons0__sieve_math_core.
      rewrite Zlength_app, !Zlength_map__sieve_math_core.
      rewrite ICount, ISum.
      cbn [map fold_right].
      rewrite !Zlength_cons. unfold Z.succ.
      rewrite Zlength_nil. split; ring.
Qed.
Lemma bits_sel_sub_multisets__sieve_math_core : forall s : list Z,
  map (fun A : list Z =>
         map snd (filter (fun q : Z * Z => Z.eqb (fst q) 1) (combine A s)))
      (all_lists (length s) (1 :: 0 :: nil))
  = sub_multisets s.
Proof.
  induction s as [| x s IH].
  - cbn. reflexivity.
  - rewrite bits_succ__sieve_math_core, map_app, !map_map.
    cbn [sub_multisets]. f_equal.
    + rewrite <- IH, map_map. apply map_ext. intros A.
      apply sel_cons1__sieve_math_core.
    + rewrite <- IH. apply map_ext. intros A.
      apply sel_cons0__sieve_math_core.
Qed.
Lemma fold_filter_map_pair__sieve_math_core :
  forall (f : list Z * list Z -> Z) (c : list Z * list Z -> bool)
         (A : list Z) (L2 : list (list Z)),
  fold_right Z.add 0 (map f (filter c (map (fun y : list Z => (A, y)) L2)))
  = fold_right Z.add 0
      (map (fun B : list Z => f (A, B)) (filter (fun B : list Z => c (A, B)) L2)).
Proof.
  intros f c A L2. induction L2 as [| B L2 IH]; cbn [map filter]; [reflexivity |].
  destruct (c (A, B)); cbn [map fold_right]; rewrite IH; reflexivity.
Qed.
Lemma fold_filter_list_prod__sieve_math_core :
  forall (f : list Z * list Z -> Z) (c : list Z * list Z -> bool)
         (L1 L2 : list (list Z)),
  fold_right Z.add 0 (map f (filter c (list_prod L1 L2)))
  = fold_right Z.add 0
      (map (fun A : list Z =>
              fold_right Z.add 0
                (map (fun B : list Z => f (A, B))
                     (filter (fun B : list Z => c (A, B)) L2)))
           L1).
Proof.
  intros f c L1 L2. induction L1 as [| A L1 IH];
    cbn [list_prod map fold_right]; [reflexivity |].
  rewrite filter_app, map_app, fold_add_app__sieve_math_core, IH.
  f_equal. apply fold_filter_map_pair__sieve_math_core.
Qed.
Lemma fold_filter_if__sieve_math_core :
  forall (g : list Z -> Z) (c : list Z -> bool) (L : list (list Z)),
  fold_right Z.add 0 (map g (filter c L))
  = fold_right Z.add 0 (map (fun A : list Z => if c A then g A else 0) L).
Proof.
  intros g c L. induction L as [| A L IH]; cbn [filter map fold_right]; [reflexivity |].
  destruct (c A); cbn [map fold_right]; lia.
Qed.
Lemma lepw_intro__sieve_math_core : forall A B : list Z,
  Zlength B = Zlength A ->
  (forall i : Z, 0 <= i < Zlength A -> Znth i B 0 <= Znth i A 0) ->
  forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B) = true.
Proof.
  induction A as [| a A IH]; intros B Hlen H; [reflexivity |].
  destruct B as [| b B].
  { exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg A). unfold Z.succ in Hlen. lia. }
  rewrite !Zlength_cons in Hlen.
  cbn [combine forallb fst snd].
  apply andb_true_iff. split.
  - apply Z.leb_le. specialize (H 0). rewrite !Znth0_cons in H. apply H.
    rewrite Zlength_cons. pose proof (Zlength_nonneg A). unfold Z.succ. lia.
  - apply IH; [lia |].
    intros i Hi. specialize (H (i + 1)).
    rewrite !Znth_cons in H by lia.
    replace (i + 1 - 1) with i in H by lia.
    apply H. rewrite Zlength_cons. unfold Z.succ. lia.
Qed.
Lemma lepw_elim__sieve_math_core : forall (A B : list Z) (i : Z),
  forallb (fun r : Z * Z => Z.leb (snd r) (fst r)) (combine A B) = true ->
  Zlength B = Zlength A -> 0 <= i < Zlength A ->
  Znth i B 0 <= Znth i A 0.
Proof.
  induction A as [| a A IH]; intros B i Hlp Hlen Hi.
  { rewrite Zlength_nil in Hi. lia. }
  destruct B as [| b B].
  { exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg A). unfold Z.succ in Hlen. lia. }
  cbn [combine forallb fst snd] in Hlp.
  apply andb_true_iff in Hlp as [Hb Hrest].
  rewrite Zlength_cons in Hlen. rewrite Zlength_cons in Hlen.
  rewrite Zlength_cons in Hi.
  destruct (Z.eq_dec i 0) as [Heq | Hne].
  - subst i. rewrite !Znth0_cons. apply Z.leb_le. exact Hb.
  - rewrite !Znth_cons by lia. apply IH.
    + exact Hrest.
    + lia.
    + lia.
Qed.
Lemma filter_andb_const__sieve_math_core :
  forall (g : bool) (h : list Z -> bool) (L : list (list Z)),
  filter (fun B : list Z => andb g (h B)) L = if g then filter h L else nil.
Proof.
  intros g h L. induction L as [| B L IH]; [destruct g; reflexivity |].
  cbn [filter]. destruct g; cbn [andb] in *; rewrite IH.
  - reflexivity.
  - reflexivity.
Qed.
Lemma fold_map_scal__sieve_math_core :
  forall (c : Z) (g : list Z -> Z) (L : list (list Z)),
  fold_right Z.add 0 (map (fun B : list Z => c * g B) L)
  = c * fold_right Z.add 0 (map g L).
Proof.
  intros c g L. induction L as [| B L IH]; cbn [map fold_right]; [ring |].
  rewrite IH. ring.
Qed.
Lemma fold_map_ext_in__sieve_math_core :
  forall (T : Type) (f g : T -> Z) (L : list T),
  (forall a : T, In a L -> f a = g a) ->
  fold_right Z.add 0 (map f L) = fold_right Z.add 0 (map g L).
Proof.
  intros T f g L H. induction L as [| a L IH]; cbn [map fold_right]; [reflexivity |].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity |].
  intros b Hb. apply H. right. exact Hb.
Qed.
Lemma pairs_sum__sieve_math_core : forall s : list Z,
  fold_right Z.add 0
    (map (fun q : list Z * list Z =>
            fold_right Z.add 0
              (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine (fst q) s)))
            * fold_right Z.add 0
                (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine (snd q) s))))
         (filter (fun q : list Z * list Z =>
                    andb (Z.eqb (fold_right Z.gcd 0
                                   (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1)
                                                    (combine (fst q) s)))) 1)
                         (andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                                  (combine (fst q) (snd q)))
                               (Z.eqb (fold_right Z.add 0 (snd q))
                                      (fold_right Z.add 0 (fst q) - 1))))
                 (list_prod (all_lists (length s) (1 :: 0 :: nil))
                            (all_lists (length s) (1 :: 0 :: nil)))))
  = fold_right Z.add 0
      (map subset_weight
           (filter (fun A : list Z => Z.eqb (fold_right Z.gcd 0 A) 1) (sub_multisets s))).
Proof.
  intros s.
  rewrite fold_filter_list_prod__sieve_math_core.
  cbn [fst snd].
  rewrite (fold_map_ext_in__sieve_math_core (list Z)
    (fun A : list Z =>
       fold_right Z.add 0
         (map (fun B : list Z =>
                 fold_right Z.add 0
                   (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine A s)))
                 * fold_right Z.add 0
                     (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine B s))))
              (filter (fun B : list Z =>
                         andb (Z.eqb (fold_right Z.gcd 0
                                        (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1)
                                                         (combine A s)))) 1)
                              (andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                                       (combine A B))
                                    (Z.eqb (fold_right Z.add 0 B)
                                           (fold_right Z.add 0 A - 1))))
                      (all_lists (length s) (1 :: 0 :: nil)))))
    (fun A : list Z =>
       if Z.eqb (fold_right Z.gcd 0
                   (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine A s)))) 1
       then subset_weight
              (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine A s)))
       else 0)
    (all_lists (length s) (1 :: 0 :: nil))).
  - rewrite fold_filter_if__sieve_math_core.
    rewrite <- bits_sel_sub_multisets__sieve_math_core.
    rewrite map_map. reflexivity.
  - intros A HA.
    rewrite filter_andb_const__sieve_math_core.
    destruct (Z.eqb (fold_right Z.gcd 0
                (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine A s)))) 1).
    + rewrite fold_map_scal__sieve_math_core.
      destruct (drops_count_sum__sieve_math_core s A
                  (bits_length__sieve_math_core s A HA)
                  (bits_forall01__sieve_math_core s A HA)) as [Hc Hsum].
      rewrite Hsum. unfold subset_weight. rewrite Z.pow_2_r. ring.
    + cbn [map fold_right]. reflexivity.
Qed.
Lemma Zlength_length__sieve_math_core : forall A B : list Z,
  Zlength A = Zlength B -> length A = length B.
Proof. intros A B H. rewrite !Zlength_correct in H. lia. Qed.
Lemma length_Zlength__sieve_math_core : forall A B : list Z,
  length A = length B -> Zlength A = Zlength B.
Proof. intros A B H. rewrite !Zlength_correct, H. reflexivity. Qed.
Lemma NoDup_bit_list__sieve_math_core : NoDup (1 :: 0 :: nil).
Proof.
  constructor.
  - cbn. intros [H | []]. discriminate.
  - constructor; [cbn; intros [] | constructor].
Qed.
Lemma pairs_valid__sieve_math_core : forall (s : list Z) (q : list Z * list Z),
  In q (filter (fun q0 : list Z * list Z =>
                  andb (Z.eqb (fold_right Z.gcd 0
                                 (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1)
                                                  (combine (fst q0) s)))) 1)
                       (andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                                (combine (fst q0) (snd q0)))
                             (Z.eqb (fold_right Z.add 0 (snd q0))
                                    (fold_right Z.add 0 (fst q0) - 1))))
               (list_prod (all_lists (length s) (1 :: 0 :: nil))
                          (all_lists (length s) (1 :: 0 :: nil)))) ->
  ValidSubsetPair s q
    (fold_right Z.add 0
       (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine (fst q) s)))
     * fold_right Z.add 0
         (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1) (combine (snd q) s)))).
Proof.
  intros s q Hq.
  apply filter_In in Hq as [Hin Hcond].
  destruct q as [A B]. cbn [fst snd] in *.
  apply in_prod_iff in Hin as [HA HB].
  apply andb_true_iff in Hcond as [Hgcd Hrest].
  apply andb_true_iff in Hrest as [Hlp Hsum].
  assert (HlA : Zlength A = Zlength s)
    by (apply length_Zlength__sieve_math_core; apply (bits_length__sieve_math_core s A HA)).
  assert (HlB : Zlength B = Zlength s)
    by (apply length_Zlength__sieve_math_core; apply (bits_length__sieve_math_core s B HB)).
  apply Z.eqb_eq in Hgcd. apply Z.eqb_eq in Hsum.
  unfold ValidSubsetPair.
  split; [exact HlA | split; [exact HlB | split]].
  - apply (bits_forall01__sieve_math_core s A HA).
  - split; [apply (bits_forall01__sieve_math_core s B HB) | split].
    + intros i Hi. apply (lepw_elim__sieve_math_core A B i Hlp); [lia | lia].
    + split; [exact Hsum | split; [| reflexivity]].
      exists 1. split; [| reflexivity].
      unfold IsPositiveGcd. split; [lia | split; [| symmetry; exact Hgcd]].
      intros Hnil. rewrite Hnil in Hgcd. cbn [fold_right] in Hgcd. discriminate.
Qed.
Lemma pairs_all__sieve_math_core : forall s : list Z,
  AllSubsetPairs s
    (filter (fun q0 : list Z * list Z =>
               andb (Z.eqb (fold_right Z.gcd 0
                              (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1)
                                               (combine (fst q0) s)))) 1)
                    (andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                             (combine (fst q0) (snd q0)))
                          (Z.eqb (fold_right Z.add 0 (snd q0))
                                 (fold_right Z.add 0 (fst q0) - 1))))
            (list_prod (all_lists (length s) (1 :: 0 :: nil))
                       (all_lists (length s) (1 :: 0 :: nil)))).
Proof.
  intros s. unfold AllSubsetPairs. split.
  - apply NoDup_filter_bool. apply NoDup_list_prod;
      apply NoDup_all_lists; apply NoDup_bit_list__sieve_math_core.
  - intros q. split.
    + intros Hq. eexists. apply pairs_valid__sieve_math_core. exact Hq.
    + intros [term Hterm]. destruct q as [A B].
      unfold ValidSubsetPair in Hterm.
      destruct Hterm as (HlA & HlB & HFA & HFB & Hpw & Hsum & [g [Hg Hg1]] & Hterm).
      subst g. unfold IsPositiveGcd in Hg.
      destruct Hg as (_ & _ & Hgcd).
      apply filter_In. split.
      * apply in_prod_iff. split; apply in_all_lists; split.
        -- apply Zlength_length__sieve_math_core. exact HlA.
        -- rewrite Forall_forall in HFA |- *. intros x Hx.
           destruct (HFA x Hx) as [H0 | H1]; subst x; cbn; auto.
        -- apply Zlength_length__sieve_math_core. exact HlB.
        -- rewrite Forall_forall in HFB |- *. intros x Hx.
           destruct (HFB x Hx) as [H0 | H1]; subst x; cbn; auto.
      * cbn [fst snd]. apply andb_true_iff. split.
        -- apply Z.eqb_eq. symmetry. exact Hgcd.
        -- apply andb_true_iff. split.
           ++ apply lepw_intro__sieve_math_core; [lia |].
              intros i Hi. apply Hpw. lia.
           ++ apply Z.eqb_eq. exact Hsum.
Qed.
Lemma solver_spec_final__sieve_math_core :
  forall (vals freq anslist : list Z) (maxv d : Z),
  Pre vals freq ->
  Zlength freq = Zlength vals ->
  (forall i : Z, 0 <= i < Zlength freq -> 1 <= Znth i freq 0 <= 1000000000) ->
  1 <= maxv ->
  d < 1 ->
  AnsExactPrefix vals freq maxv anslist d ->
  Spec vals freq (Znth 1 anslist 0).
Proof.
  intros vals freq anslist maxv d HPre Hlen Hfreq Hmaxv Hd HAns.
  unfold Pre in HPre.
  assert (Hpos : forall i : Z, 0 <= i < Zlength freq -> 0 <= Znth i freq 0)
    by (intros i Hi; pose proof (Hfreq i Hi); lia).
  assert (Hval : Znth 1 anslist 0 = exact_gcd_weight vals freq 1 mod 998244353)
    by (apply HAns; lia).
  unfold Spec.
  exists (expand vals freq).
  exists (filter (fun q0 : list Z * list Z =>
             andb (Z.eqb (fold_right Z.gcd 0
                            (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1)
                                             (combine (fst q0) (expand vals freq))))) 1)
                  (andb (forallb (fun r : Z * Z => Z.leb (snd r) (fst r))
                           (combine (fst q0) (snd q0)))
                        (Z.eqb (fold_right Z.add 0 (snd q0))
                               (fold_right Z.add 0 (fst q0) - 1))))
          (list_prod (all_lists (length (expand vals freq)) (1 :: 0 :: nil))
                     (all_lists (length (expand vals freq)) (1 :: 0 :: nil)))).
  exists (fun q : list Z * list Z =>
            fold_right Z.add 0
              (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1)
                               (combine (fst q) (expand vals freq))))
            * fold_right Z.add 0
                (map snd (filter (fun r : Z * Z => Z.eqb (fst r) 1)
                                 (combine (snd q) (expand vals freq))))).
  split; [apply expand_is_expanded_multiset__sieve_math_core; assumption |].
  split; [apply pairs_all__sieve_math_core |].
  split; [intros q Hq; apply pairs_valid__sieve_math_core; exact Hq |].
  rewrite Hval. f_equal.
  rewrite pairs_sum__sieve_math_core. reflexivity.
Qed.
