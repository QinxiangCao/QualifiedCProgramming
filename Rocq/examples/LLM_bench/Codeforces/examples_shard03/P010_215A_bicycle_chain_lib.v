Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SumLib.ZRect.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(a b : list Z) -> Z, how many gears are counted.
   Gear (i, j) pairs a pedal star with [a_i] teeth and a wheel star with [b_j]
   teeth, and its ratio is b_j / a_i.  Only gears with an integer ratio count,
   and the answer is how many of them reach the largest such ratio.  The
   statement guarantees that at least one integer gear exists. *)
Definition IntegerGear (a b : list Z) (i j : Z) : Prop :=
  0 <= i < Zlength a /\ 0 <= j < Zlength b /\ (Znth i a 0 | Znth j b 0).

Definition Pre (a b : list Z) : Prop :=
  (* Stated explicitly in the P010 solver Require, so dropped here:
       1 <= Zlength a <= 50 /\ 1 <= Zlength b <= 50 /\
       Forall (fun x => 1 <= x <= 10000) a /\
       Forall (fun x => 1 <= x <= 10000) b /\ *)
  mono_inc a /\ mono_inc b /\
  (exists i j, IntegerGear a b i j).

Definition Spec (a b : list Z) (out : Z) : Prop :=
  exists m,
    max_value_of_subset Z.le
      (fun p : Z * Z => IntegerGear a b (fst p) (snd p))
      (fun p => Znth (snd p) b 0 / Znth (fst p) a 0) m /\
    out = #(fun p : Z * Z => 0 <= fst p < Zlength a /\
                             0 <= snd p < Zlength b /\
                             Znth (snd p) b 0 = m * Znth (fst p) a 0).
