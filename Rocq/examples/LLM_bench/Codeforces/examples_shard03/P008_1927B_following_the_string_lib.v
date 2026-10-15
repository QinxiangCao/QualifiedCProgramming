Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(a : list Z) -> list Z, one string with the given trace.
   The trace of a string counts, at every position, how many earlier positions
   carry the same character.  The answer is any lowercase string (character
   codes 97 .. 122) whose trace is the given array; the statement guarantees
   that one exists. *)
Definition TraceOf (s a : list Z) : Prop :=
  Zlength s = Zlength a /\
  forall i, 0 <= i < Zlength a ->
    Znth i a 0 = #(fun j : Z => 0 <= j < i /\ Znth j s 0 = Znth i s 0).

Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P008 solver Require, so dropped here:
       1 <= Zlength a <= 200000 /\
       Forall (fun x => 0 <= x < Zlength a) a /\ *)
  exists s, Forall (fun c => 97 <= c <= 122) s /\ TraceOf s a.

Definition Spec (a : list Z) (out : list Z) : Prop :=
  Forall (fun c => 97 <= c <= 122) out /\ TraceOf out a.
