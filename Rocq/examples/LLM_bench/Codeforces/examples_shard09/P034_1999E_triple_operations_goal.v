From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P034_1999E_triple_operations_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_full ( &( "fv" ) ) 200005 )
  **  (Int64Array.undef_full ( &( "pre" ) ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_full ( &( "fv" ) ) 200005 )
  **  (Int64Array.undef_full ( &( "pre" ) ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_full ( &( "pre" ) ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_full ( &( "pre" ) ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (((( &( "pre" ) ) + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.undef_seg ( &( "pre" ) ) 1 200005 )
  **  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= 200005)) (PreH8 : (TripleTablesPrefix fvs pres i )),
  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (200005 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 200005) ”
.

Definition solver_safety_wit_7 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ”
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ ((INT_MIN) <= ((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ ((i <> (INT_MIN)) \/ (3 <> (-1))) ”
  &&  “ (3 <> 0) ”
.

Definition solver_safety_wit_9 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_10 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (((Znth ((i - 1 ) - 0 ) pres 0) + (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) pres 0) + (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0) )) ”
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (((Znth ((i - 1 ) - 0 ) pres 0) + (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) pres 0) + (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0) )) ”
).

Definition solver_safety_wit_11_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (((Znth ((i - 1 ) - 0 ) pres 0) + (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) pres 0) + (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0) )) ”
.

Definition solver_safety_wit_12 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (Int64Array.seg ( &( "pre" ) ) 0 (i + 1 ) (app (pres) ((cons (((Znth ((i - 1 ) - 0 ) pres 0) + (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pre" ) ) (i + 1 ) 200005 )
  **  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs pres i )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (outs) ((cons (((2 * (Znth (Znth i ls 0) fvs 0) ) + ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_17 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (((2 * (Znth (Znth i ls 0) fvs 0) ) + ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((2 * (Znth (Znth i ls 0) fvs 0) ) + ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) )) ”
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (((2 * (Znth (Znth i ls 0) fvs 0) ) + ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((2 * (Znth (Znth i ls 0) fvs 0) ) + ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) )) ”
).

Definition solver_safety_wit_17_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (((2 * (Znth (Znth i ls 0) fvs 0) ) + ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ ((INT64_MIN) <= ((2 * (Znth (Znth i ls 0) fvs 0) ) + ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) )) ”
.

Definition solver_safety_wit_18 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) )) ”
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) )) ”
).

Definition solver_safety_wit_18_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_18_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ ((INT64_MIN) <= ((Znth (Znth i rs 0) pres 0) - (Znth (Znth i ls 0) pres 0) )) ”
.

Definition solver_safety_wit_19 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ ((2 * (Znth (Znth i ls 0) fvs 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (2 * (Znth (Znth i ls 0) fvs 0) )) ”
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ ((2 * (Znth (Znth i ls 0) fvs 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (2 * (Znth (Znth i ls 0) fvs 0) )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ ((2 * (Znth (Znth i ls 0) fvs 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ ((INT64_MIN) <= (2 * (Znth (Znth i ls 0) fvs 0) )) ”
.

Definition solver_safety_wit_20 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ (2 <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= 2) ”
.

Definition solver_entail_wit_1 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  (((( &( "pre" ) ) + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.undef_seg ( &( "pre" ) ) 1 200005 )
  **  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  EX (fvs: (@list Z)) (pres: (@list Z)),
  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres 1 ) ”
  &&  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 1 fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 1 pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) 1 200005 )
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 10000)) (PreH7 : ((Zlength (ls)) = q_pre)) (PreH8 : ((Zlength (rs)) = q_pre)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  (((( &( "pre" ) ) + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  EX (fvs: (@list Z)) (pres: (@list Z)),
  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres 1 ) ”
  &&  (IntArray.seg ( &( "fv" ) ) 0 1 fvs )
  **  (Int64Array.seg ( &( "pre" ) ) 0 1 pres )
).

Definition solver_entail_wit_2 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs pres i )),
  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (0 <= (i ÷ 3 )) ”
  &&  “ ((i ÷ 3 ) < i) ”
  &&  “ (q_pre <= INT_MAX) ”
  &&  “ (q_pre >= INT_MIN) ”
  &&  “ (i < 200005) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  TT && emp 
|--
  “ ((i ÷ 3 ) < i) ”
  &&  “ (0 <= (i ÷ 3 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  ((i ÷ 3 ) < i)
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (q_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (0 <= (i ÷ 3 ))
.

Definition solver_entail_wit_3 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs_2 pres_2 i )),
  (Int64Array.seg ( &( "pre" ) ) 0 (i + 1 ) (app (pres_2) ((cons (((Znth ((i - 1 ) - 0 ) pres_2 0) + (Znth (i - 0 ) (app (fvs_2) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs_2 0) + 1 )) ((@nil Z))))) 0) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "pre" ) ) (i + 1 ) 200005 )
  **  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs_2) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs_2 0) + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  EX (fvs: (@list Z)) (pres: (@list Z)),
  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres (i + 1 ) ) ”
  &&  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 (i + 1 ) pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) (i + 1 ) 200005 )
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs_2 pres_2 i )),
  TT && emp 
|--
  “ (TripleTablesPrefix (app (fvs_2) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs_2 0) + 1 )) ((@nil Z))))) (app (pres_2) ((cons (((Znth ((i - 1 ) - 0 ) pres_2 0) + (Znth (i - 0 ) (app (fvs_2) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs_2 0) + 1 )) ((@nil Z))))) 0) )) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs_2 pres_2 i )),
  (TripleTablesPrefix (app (fvs_2) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs_2 0) + 1 )) ((@nil Z))))) (app (pres_2) ((cons (((Znth ((i - 1 ) - 0 ) pres_2 0) + (Znth (i - 0 ) (app (fvs_2) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs_2 0) + 1 )) ((@nil Z))))) 0) )) ((@nil Z))))) (i + 1 ) )
.

Definition solver_entail_wit_4 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < q_pre)) -> (((1 <= (Znth k_2 ls 0)) /\ ((Znth k_2 ls 0) < (Znth k_2 rs 0))) /\ ((Znth k_2 rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 i )),
  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs_2 )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres_2 )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  EX (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)),
  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs 0 ) ”
  &&  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 0 outs )
  **  (Int64Array.undef_seg out_pre 0 q_pre )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < q_pre)) -> (((1 <= (Znth k_2 ls 0)) /\ ((Znth k_2 ls 0) < (Znth k_2 rs 0))) /\ ((Znth k_2 rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 i )),
  TT && emp 
|--
  “ (TripleOutputsPrefix ls rs (@nil Z) 0 ) ”
  &&  “ (TripleClosedFormBridge fvs_2 pres_2 ) ”
  &&  “ (TripleTablesBridge fvs_2 pres_2 ) ”
  &&  “ (TripleTablesPrefix fvs_2 pres_2 200005 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < q_pre)) -> (((1 <= (Znth k_2 ls 0)) /\ ((Znth k_2 ls 0) < (Znth k_2 rs 0))) /\ ((Znth k_2 rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 i )),
  (TripleOutputsPrefix ls rs (@nil Z) 0 )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < q_pre)) -> (((1 <= (Znth k_2 ls 0)) /\ ((Znth k_2 ls 0) < (Znth k_2 rs 0))) /\ ((Znth k_2 rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 i )),
  (TripleClosedFormBridge fvs_2 pres_2 )
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < q_pre)) -> (((1 <= (Znth k_2 ls 0)) /\ ((Znth k_2 ls 0) < (Znth k_2 rs 0))) /\ ((Znth k_2 rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 i )),
  (TripleTablesBridge fvs_2 pres_2 )
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < q_pre)) -> (((1 <= (Znth k_2 ls 0)) /\ ((Znth k_2 ls 0) < (Znth k_2 rs 0))) /\ ((Znth k_2 rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 i )),
  (TripleTablesPrefix fvs_2 pres_2 200005 )
.

Definition solver_entail_wit_4_split_goal_5 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i >= 200005)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < q_pre)) -> (((1 <= (Znth k_2 ls 0)) /\ ((Znth k_2 ls 0) < (Znth k_2 rs 0))) /\ ((Znth k_2 rs 0) <= 200000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= 200005)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 i )),
  forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))
.

Definition solver_entail_wit_5 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs_2: (@list Z)) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 200005 )) (PreH10 : (TripleTablesBridge fvs_2 pres_2 )) (PreH11 : (TripleClosedFormBridge fvs_2 pres_2 )) (PreH12 : (TripleOutputsPrefix ls rs outs_2 i )),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (outs_2) ((cons (((2 * (Znth (Znth i ls 0) fvs_2 0) ) + ((Znth (Znth i rs 0) pres_2 0) - (Znth (Znth i ls 0) pres_2 0) ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres_2 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs_2 )
|--
  EX (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)),
  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs (i + 1 ) ) ”
  &&  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 (i + 1 ) outs )
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (outs_2: (@list Z)) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 200005 )) (PreH10 : (TripleTablesBridge fvs_2 pres_2 )) (PreH11 : (TripleClosedFormBridge fvs_2 pres_2 )) (PreH12 : (TripleOutputsPrefix ls rs outs_2 i )),
  TT && emp 
|--
  “ (TripleOutputsPrefix ls rs (app (outs_2) ((cons (((2 * (Znth (Znth i ls 0) fvs_2 0) ) + ((Znth (Znth i rs 0) pres_2 0) - (Znth (Znth i ls 0) pres_2 0) ) )) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (outs_2: (@list Z)) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 200005 )) (PreH10 : (TripleTablesBridge fvs_2 pres_2 )) (PreH11 : (TripleClosedFormBridge fvs_2 pres_2 )) (PreH12 : (TripleOutputsPrefix ls rs outs_2 i )),
  (TripleOutputsPrefix ls rs (app (outs_2) ((cons (((2 * (Znth (Znth i ls 0) fvs_2 0) ) + ((Znth (Znth i rs 0) pres_2 0) - (Znth (Znth i ls 0) pres_2 0) ) )) ((@nil Z))))) (i + 1 ) )
.

Definition solver_return_wit_1 :=
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs_2: (@list Z)) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 <= q_pre)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 200005 )) (PreH10 : (TripleTablesBridge fvs_2 pres_2 )) (PreH11 : (TripleClosedFormBridge fvs_2 pres_2 )) (PreH12 : (TripleOutputsPrefix ls rs outs_2 i_2 )),
  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i_2 outs_2 )
  **  (Int64Array.undef_seg out_pre i_2 q_pre )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs_2 )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres_2 )
|--
  EX (fvs: (@list Z)) (pres: (@list Z)) (outs: (@list Z)),
  “ ((Zlength (outs)) = q_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (Spec (Znth i ls 0) (Znth i rs 0) (Znth i outs 0) )) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.full out_pre q_pre outs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
) \/
(
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (outs_2: (@list Z)) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 <= q_pre)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 200005 )) (PreH10 : (TripleTablesBridge fvs_2 pres_2 )) (PreH11 : (TripleClosedFormBridge fvs_2 pres_2 )) (PreH12 : (TripleOutputsPrefix ls rs outs_2 i_2 )),
  TT && emp 
|--
  “ forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (Spec (Znth i ls 0) (Znth i rs 0) (Znth i outs_2 0) )) ”
  &&  “ ((Zlength (outs_2)) = q_pre) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (outs_2: (@list Z)) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 <= q_pre)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 200005 )) (PreH10 : (TripleTablesBridge fvs_2 pres_2 )) (PreH11 : (TripleClosedFormBridge fvs_2 pres_2 )) (PreH12 : (TripleOutputsPrefix ls rs outs_2 i_2 )),
  forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (Spec (Znth i ls 0) (Znth i rs 0) (Znth i outs_2 0) ))
.

Definition solver_return_wit_1_split_goal_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (outs_2: (@list Z)) (fvs_2: (@list Z)) (pres_2: (@list Z)) (i_2: Z) (PreH1 : (i_2 >= q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 <= q_pre)) (PreH9 : (TripleTablesPrefix fvs_2 pres_2 200005 )) (PreH10 : (TripleTablesBridge fvs_2 pres_2 )) (PreH11 : (TripleClosedFormBridge fvs_2 pres_2 )) (PreH12 : (TripleOutputsPrefix ls rs outs_2 i_2 )),
  ((Zlength (outs_2)) = q_pre)
.

Definition solver_partial_solve_wit_1 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_full ( &( "fv" ) ) 200005 )
  **  (Int64Array.undef_full ( &( "pre" ) ) 200005 )
|--
  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000))) ”
  &&  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_full ( &( "pre" ) ) 200005 )
.

Definition solver_partial_solve_wit_2 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (PreH1 : (1 <= q_pre)) (PreH2 : (q_pre <= 10000)) (PreH3 : ((Zlength (ls)) = q_pre)) (PreH4 : ((Zlength (rs)) = q_pre)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000)))),
  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_full ( &( "pre" ) ) 200005 )
|--
  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < q_pre)) -> (((1 <= (Znth i ls 0)) /\ ((Znth i ls 0) < (Znth i rs 0))) /\ ((Znth i rs 0) <= 200000))) ”
  &&  (((( &( "pre" ) ) + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg ( &( "pre" ) ) 1 200005 )
  **  (((( &( "fv" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "fv" ) ) 1 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_3 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (0 <= (i ÷ 3 )) ”
  &&  “ ((i ÷ 3 ) < i) ”
  &&  “ (q_pre <= INT_MAX) ”
  &&  “ (q_pre >= INT_MIN) ”
  &&  “ (i < 200005) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres i ) ”
  &&  (((( &( "fv" ) ) + ((i ÷ 3 ) * sizeof(INT)))) # Int  |-> (Znth ((i ÷ 3 ) - 0 ) fvs 0))
  **  (IntArray.missing_i ( &( "fv" ) ) (i ÷ 3 ) 0 i fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
.

Definition solver_partial_solve_wit_4 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "fv" ) ) i 200005 )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (0 <= (i ÷ 3 )) ”
  &&  “ ((i ÷ 3 ) < i) ”
  &&  “ (q_pre <= INT_MAX) ”
  &&  “ (q_pre >= INT_MIN) ”
  &&  “ (i < 200005) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres i ) ”
  &&  (((( &( "fv" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.seg ( &( "fv" ) ) 0 i fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
.

Definition solver_partial_solve_wit_5 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (0 <= (i ÷ 3 )) ”
  &&  “ ((i ÷ 3 ) < i) ”
  &&  “ (q_pre <= INT_MAX) ”
  &&  “ (q_pre >= INT_MIN) ”
  &&  “ (i < 200005) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres i ) ”
  &&  (((( &( "pre" ) ) + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - 1 ) - 0 ) pres 0))
  **  (Int64Array.missing_i ( &( "pre" ) ) (i - 1 ) 0 i pres )
  **  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
.

Definition solver_partial_solve_wit_6 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (0 <= (i ÷ 3 )) ”
  &&  “ ((i ÷ 3 ) < i) ”
  &&  “ (q_pre <= INT_MAX) ”
  &&  “ (q_pre >= INT_MIN) ”
  &&  “ (i < 200005) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres i ) ”
  &&  (((( &( "fv" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) 0))
  **  (IntArray.missing_i ( &( "fv" ) ) i 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
.

Definition solver_partial_solve_wit_7 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (0 <= (i ÷ 3 ))) (PreH2 : ((i ÷ 3 ) < i)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (q_pre >= INT_MIN)) (PreH5 : (i < 200005)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 10000)) (PreH8 : ((Zlength (ls)) = q_pre)) (PreH9 : ((Zlength (rs)) = q_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= 200005)) (PreH13 : (TripleTablesPrefix fvs pres i )),
  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.undef_seg ( &( "pre" ) ) i 200005 )
|--
  “ (0 <= (i ÷ 3 )) ”
  &&  “ ((i ÷ 3 ) < i) ”
  &&  “ (q_pre <= INT_MAX) ”
  &&  “ (q_pre >= INT_MIN) ”
  &&  “ (i < 200005) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= 200005) ”
  &&  “ (TripleTablesPrefix fvs pres i ) ”
  &&  (((( &( "pre" ) ) + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg ( &( "pre" ) ) (i + 1 ) 200005 )
  **  (IntArray.seg ( &( "fv" ) ) 0 (i + 1 ) (app (fvs) ((cons (((Znth ((i ÷ 3 ) - 0 ) fvs 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.seg ( &( "pre" ) ) 0 i pres )
  **  (IntArray.undef_seg ( &( "fv" ) ) (i + 1 ) 200005 )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_8 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ (i < q_pre) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs i ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i l_pre i 0 q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
.

Definition solver_partial_solve_wit_9 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ (i < q_pre) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs i ) ”
  &&  (((( &( "fv" ) ) + ((Znth i ls 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i ls 0) fvs 0))
  **  (IntArray.missing_i ( &( "fv" ) ) (Znth i ls 0) 0 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
.

Definition solver_partial_solve_wit_10 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ (i < q_pre) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs i ) ”
  &&  (((r_pre + (i * sizeof(INT)))) # Int  |-> (Znth i rs 0))
  **  (IntArray.missing_i r_pre i 0 q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
.

Definition solver_partial_solve_wit_11 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
|--
  “ (i < q_pre) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs i ) ”
  &&  (((( &( "pre" ) ) + ((Znth i rs 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i rs 0) pres 0))
  **  (Int64Array.missing_i ( &( "pre" ) ) (Znth i rs 0) 0 200005 pres )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
.

Definition solver_partial_solve_wit_12 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (IntArray.full l_pre q_pre ls )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (i < q_pre) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs i ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i l_pre i 0 q_pre ls )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
.

Definition solver_partial_solve_wit_13 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (IntArray.full l_pre q_pre ls )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (i < q_pre) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs i ) ”
  &&  (((( &( "pre" ) ) + ((Znth i ls 0) * sizeof(INT64)))) # Int64  |-> (Znth (Znth i ls 0) pres 0))
  **  (Int64Array.missing_i ( &( "pre" ) ) (Znth i ls 0) 0 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
.

Definition solver_partial_solve_wit_14 :=
forall (rs: (@list Z)) (ls: (@list Z)) (q_pre: Z) (l_pre: Z) (r_pre: Z) (out_pre: Z) (outs: (@list Z)) (fvs: (@list Z)) (pres: (@list Z)) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= q_pre)) (PreH3 : (q_pre <= 10000)) (PreH4 : ((Zlength (ls)) = q_pre)) (PreH5 : ((Zlength (rs)) = q_pre)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= q_pre)) (PreH9 : (TripleTablesPrefix fvs pres 200005 )) (PreH10 : (TripleTablesBridge fvs pres )) (PreH11 : (TripleClosedFormBridge fvs pres )) (PreH12 : (TripleOutputsPrefix ls rs outs i )),
  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.seg out_pre 0 i outs )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (i < q_pre) ”
  &&  “ (1 <= q_pre) ”
  &&  “ (q_pre <= 10000) ”
  &&  “ ((Zlength (ls)) = q_pre) ”
  &&  “ ((Zlength (rs)) = q_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < q_pre)) -> (((1 <= (Znth k ls 0)) /\ ((Znth k ls 0) < (Znth k rs 0))) /\ ((Znth k rs 0) <= 200000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= q_pre) ”
  &&  “ (TripleTablesPrefix fvs pres 200005 ) ”
  &&  “ (TripleTablesBridge fvs pres ) ”
  &&  “ (TripleClosedFormBridge fvs pres ) ”
  &&  “ (TripleOutputsPrefix ls rs outs i ) ”
  &&  (((out_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (Int64Array.full ( &( "pre" ) ) 200005 pres )
  **  (IntArray.full l_pre q_pre ls )
  **  (IntArray.full r_pre q_pre rs )
  **  (IntArray.full ( &( "fv" ) ) 200005 fvs )
  **  (Int64Array.seg out_pre 0 i outs )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.

End VC_Correct.
