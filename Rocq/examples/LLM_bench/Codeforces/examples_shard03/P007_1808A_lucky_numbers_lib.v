Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SumLib.ListMember.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(l r : Z) -> Z, one starship number of the store.
   The luckiness of a number is the difference between its largest and its
   smallest decimal digit, and any number of [l .. r] whose luckiness is
   maximal may be printed.

   [DecimalDigits x ds] says that [ds] is the decimal representation of the
   positive integer [x], most significant digit first; see the note in P001 on
   why the relation is restated here instead of shared. *)
Definition DecimalDigits (x : Z) (ds : list Z) : Prop :=
  1 <= Zlength ds /\
  Forall (fun d => 0 <= d <= 9) ds /\
  Znth 0 ds 0 <> 0 /\
  fold_left (fun acc d => acc * 10 + d) ds 0 = x.

Definition Luckiness (x v : Z) : Prop :=
  exists ds lo hi, DecimalDigits x ds /\
    min_value_of_subset Z.le (fun d => In d ds) (fun d => d) lo /\
    max_value_of_subset Z.le (fun d => In d ds) (fun d => d) hi /\
    v = hi - lo.

Definition Pre (l r : Z) : Prop :=
  (* Every clause below is stated explicitly in the P007 solver Require, which
     therefore omits the Pre(...) call:
       1 <= l /\ l <= r /\ r <= 1000000. *)
  True.

Definition Spec (l r out : Z) : Prop :=
  exists v, l <= out <= r /\ Luckiness out v /\
    max_value_of_subset Z.le
      (fun p : Z * Z => l <= fst p <= r /\ Luckiness (fst p) (snd p))
      (fun p => snd p) v.

(* Representation bridges for the two file-scope tables the solver keeps.
   [LuckTable luckv] holds when position x of the table carries the luckiness
   of x, for every value the store can hold.  [BlockBestTable luckv bb] holds
   when entry b of the second table is the position of a value of block b whose
   tabulated luckiness is largest in that block; the blocks are the 1024-wide
   pieces of the same value range. *)
Definition LuckTable (luckv : list Z) : Prop :=
  Zlength luckv = 1000001 /\
  forall x, 1 <= x <= 1000000 -> Luckiness x (Znth x luckv 0).

Definition BlockBestTable (luckv bb : list Z) : Prop :=
  Zlength bb = 977 /\
  forall b, 0 <= b < 977 ->
    Z.max 1 (1024 * b) <= Znth b bb 0 <= Z.min 1000000 (1024 * b + 1023) /\
    (forall x, Z.max 1 (1024 * b) <= x <= Z.min 1000000 (1024 * b + 1023) ->
       Znth x luckv 0 <= Znth (Znth b bb 0) luckv 0).
