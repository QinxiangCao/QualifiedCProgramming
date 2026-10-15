(* Per-case signature: solve_case(s : list Z) -> Z.  The statement hands over a
   binary STRING, so [s] carries its characters as decimal source character
   codes: '0' is 48 and '1' is 49. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Cell (i, j) of an r x c matrix lies on the matrix's edge. *)
Definition OnBorder (r c i j : Z) : Prop :=
  i = 0 \/ i = r - 1 \/ j = 0 \/ j = c - 1.

(* [s] is the row-major writing-out of a beautiful r x c binary matrix: ones on
   its edges and zeros inside. The cell in row [i], column [j] is written at
   position [i * c + j] of the string. *)
Definition BeautifulFlat (r c : Z) (s : list Z) : Prop :=
  1 <= r /\ 1 <= c /\ Zlength s = r * c /\
  forall i j, 0 <= i < r -> 0 <= j < c ->
    (  OnBorder r c i j /\ Znth (i * c + j) s 0 = 49) \/
    (~ OnBorder r c i j /\ Znth (i * c + j) s 0 = 48).

(* The statement guarantees three things about the input: the length bound, that
   the string is binary, and that it really is the writing-out of SOME beautiful
   matrix — not necessarily a square one. (Binary-ness also follows from that
   last guarantee, but the statement asserts it separately, so it is kept.) *)
Definition Pre (s : list Z) : Prop :=
  (* 2 <= Zlength s <= 200000 /\
  Forall (fun ch => ch = 48 \/ ch = 49) s /\ *)
  exists r c, BeautifulFlat r c s.

(* The printed verdict: 1 for "Yes", 0 for "No". It is "Yes" exactly when some
   SQUARE beautiful matrix writes out to [s]. *)
Definition Spec (s : list Z) (out : Z) : Prop :=
  (out = 1 /\   exists q, BeautifulFlat q q s) \/
  (out = 0 /\ ~ exists q, BeautifulFlat q q s).
