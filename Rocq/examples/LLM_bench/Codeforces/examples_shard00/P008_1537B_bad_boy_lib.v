Require Import Coq.ZArith.ZArith.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition zpair_fst (p : Z * Z) : Z := fst p.

Definition zpair_snd (p : Z * Z) : Z := snd p.

Definition Manhattan (p q : Z * Z) : Z :=
  Z.abs (fst p - fst q) + Z.abs (snd p - snd q).

Definition RoundTripThroughTwo (start p q : Z * Z) : Z :=
  Manhattan start p + Manhattan p q + Manhattan q start.

Definition InRoom (n m : Z) (p : Z * Z) : Prop :=
  1 <= fst p <= n /\ 1 <= snd p <= m.

Definition Pre (n m : Z) (start : Z * Z) : Prop :=
  1 <= n <= 1000000000 /\
  1 <= m <= 1000000000 /\
  InRoom n m start.

Definition Spec (n m : Z) (start p q : Z * Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : (Z * Z) * (Z * Z) =>
      InRoom n m (fst candidate) /\ InRoom n m (snd candidate))
    (fun candidate =>
      RoundTripThroughTwo start (fst candidate) (snd candidate))
    (RoundTripThroughTwo start p q) /\
  InRoom n m p /\ InRoom n m q.

Require Import Coq.micromega.Lia.
Lemma cycle_span_bound__final_result :
  forall lo hi s p q,
    lo <= s <= hi ->
    lo <= p <= hi ->
    lo <= q <= hi ->
    Z.abs (s - p) + Z.abs (p - q) + Z.abs (q - s)
      <= 2 * (hi - lo).
Proof.
  intros lo hi s p q Hs Hp Hq.
  destruct (Z_le_dec s p) as [Hsp | Hsp];
  destruct (Z_le_dec p q) as [Hpq | Hpq];
  destruct (Z_le_dec q s) as [Hqs | Hqs].
  all: repeat match goal with
       | H : ?x <= ?y |- context [Z.abs (?x - ?y)] =>
           rewrite (Z.abs_neq (x - y)) by lia
       | H : ~ ?x <= ?y |- context [Z.abs (?x - ?y)] =>
           rewrite (Z.abs_eq (x - y)) by lia
       end;
       lia.
Qed.
Lemma opposite_corners_spec__final_result :
  forall n m start,
    1 <= n ->
    1 <= m ->
    InRoom n m start ->
    Spec n m start (1, 1) (n, m).
Proof.
  intros n m [sx sy] Hn Hm Hstart.
  destruct Hstart as [[Hsxlo Hsxhi] [Hsylo Hsyhi]].
  unfold Spec.
  split.
  - unfold max_value_of_subset.
    exists ((1, 1), (n, m)).
    split.
    + unfold max_object_of_subset.
      split.
      * split; unfold InRoom; simpl; lia.
      * intros [[px py] [qx qy]] Hcandidate.
        destruct Hcandidate as [Hp Hq].
        destruct Hp as [[Hpxlo Hpxhi] [Hpylo Hpyhi]].
        destruct Hq as [[Hqxlo Hqxhi] [Hqylo Hqyhi]].
        pose proof
          (cycle_span_bound__final_result
             1 n sx px qx
             (conj Hsxlo Hsxhi)
             (conj Hpxlo Hpxhi)
             (conj Hqxlo Hqxhi)) as Hx.
        pose proof
          (cycle_span_bound__final_result
             1 m sy py qy
             (conj Hsylo Hsyhi)
             (conj Hpylo Hpyhi)
             (conj Hqylo Hqyhi)) as Hy.
        unfold RoundTripThroughTwo, Manhattan in *.
        cbn [fst snd] in *.
        rewrite (Z.abs_eq (sx - 1)) by lia.
        rewrite (Z.abs_eq (sy - 1)) by lia.
        rewrite (Z.abs_neq (1 - n)) by lia.
        rewrite (Z.abs_neq (1 - m)) by lia.
        rewrite (Z.abs_eq (n - sx)) by lia.
        rewrite (Z.abs_eq (m - sy)) by lia.
        lia.
    + reflexivity.
  - split; unfold InRoom; simpl; lia.
Qed.
