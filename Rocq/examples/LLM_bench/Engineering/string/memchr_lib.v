Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.

Local Open Scope Z_scope.
Import ListNotations.
Local Open Scope list.

Definition memchr_result (bytes: list Z) (c n ret s: Z): Prop :=
  (exists i,
      0 <= i < n /\
      Znth i bytes 0 = c /\
      (forall k, 0 <= k < i -> Znth k bytes 0 <> c) /\
      ret = s + i) \/
  ((forall k, 0 <= k < n -> Znth k bytes 0 <> c) /\ ret = 0).
