From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P057_1355C_count_triangles_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= B_pre)) (PreH3 : (B_pre <= C_pre)) (PreH4 : (C_pre <= D_pre)) (PreH5 : (D_pre <= 500000)),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= B_pre)) (PreH3 : (B_pre <= C_pre)) (PreH4 : (C_pre <= D_pre)) (PreH5 : (D_pre <= 500000)),
  ((( &( "s" ) )) # Int64  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
|--
  “ ((A_pre + B_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (A_pre + B_pre )) ”
.

Definition solver_safety_wit_3 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= B_pre)) (PreH3 : (B_pre <= C_pre)) (PreH4 : (C_pre <= D_pre)) (PreH5 : (D_pre <= 500000)) (PreH6 : ((A_pre + B_pre ) <= s)) (PreH7 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH8 : (0 <= total)) (PreH9 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH10 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((B_pre + C_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (B_pre + C_pre )) ”
.

Definition solver_safety_wit_4 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (s <= (B_pre + C_pre ))) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "xlo" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((s - C_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - C_pre )) ”
.

Definition solver_safety_wit_5 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (A_pre <= (s - C_pre ))) (PreH2 : (s <= (B_pre + C_pre ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "xlo" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((s - C_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - C_pre )) ”
.

Definition solver_safety_wit_6 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (A_pre > (s - C_pre ))) (PreH2 : (s <= (B_pre + C_pre ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "xhi" ) )) # Int64  |->_)
  **  ((( &( "xlo" ) )) # Int64  |-> A_pre)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((s - B_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - B_pre )) ”
.

Definition solver_safety_wit_7 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "xhi" ) )) # Int64  |->_)
  **  ((( &( "xlo" ) )) # Int64  |-> A_pre)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((s - B_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - B_pre )) ”
.

Definition solver_safety_wit_8 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (A_pre <= (s - C_pre ))) (PreH2 : (s <= (B_pre + C_pre ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "xhi" ) )) # Int64  |->_)
  **  ((( &( "xlo" ) )) # Int64  |-> (s - C_pre ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((s - B_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - B_pre )) ”
.

Definition solver_safety_wit_9 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "xhi" ) )) # Int64  |->_)
  **  ((( &( "xlo" ) )) # Int64  |-> (s - C_pre ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((s - B_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - B_pre )) ”
.

Definition solver_safety_wit_10 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo > xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ False ”
.

Definition solver_safety_wit_11 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ (((xhi - xlo ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((xhi - xlo ) + 1 )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ (((xhi - xlo ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((xhi - xlo ) + 1 )) ”
).

Definition solver_safety_wit_11_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ (((xhi - xlo ) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ ((INT64_MIN) <= ((xhi - xlo ) + 1 )) ”
.

Definition solver_safety_wit_12 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ ((xhi - xlo ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (xhi - xlo )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ ((xhi - xlo ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (xhi - xlo )) ”
).

Definition solver_safety_wit_12_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ ((xhi - xlo ) <= INT64_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ ((INT64_MIN) <= (xhi - xlo )) ”
.

Definition solver_safety_wit_13 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "pairs" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "zhi" ) )) # Int64  |->_)
  **  ((( &( "pairs" ) )) # Int64  |-> ((xhi - xlo ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ ((s - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (xlo <= xhi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "zhi" ) )) # Int64  |->_)
  **  ((( &( "pairs" ) )) # Int64  |-> ((xhi - xlo ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre >= (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "zhi" ) )) # Int64  |->_)
  **  ((( &( "pairs" ) )) # Int64  |-> ((xhi - xlo ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ ((s - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s - 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre >= (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "zhi" ) )) # Int64  |->_)
  **  ((( &( "pairs" ) )) # Int64  |-> ((xhi - xlo ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((total + (pairs * ((zhi - C_pre ) + 1 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + (pairs * ((zhi - C_pre ) + 1 ) ) )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((total + (pairs * ((zhi - C_pre ) + 1 ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + (pairs * ((zhi - C_pre ) + 1 ) ) )) ”
).

Definition solver_safety_wit_18_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((total + (pairs * ((zhi - C_pre ) + 1 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_18_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((INT64_MIN) <= (total + (pairs * ((zhi - C_pre ) + 1 ) ) )) ”
.

Definition solver_safety_wit_19 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((pairs * ((zhi - C_pre ) + 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (pairs * ((zhi - C_pre ) + 1 ) )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((pairs * ((zhi - C_pre ) + 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (pairs * ((zhi - C_pre ) + 1 ) )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((pairs * ((zhi - C_pre ) + 1 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((INT64_MIN) <= (pairs * ((zhi - C_pre ) + 1 ) )) ”
.

Definition solver_safety_wit_20 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ (((zhi - C_pre ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((zhi - C_pre ) + 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ ((zhi - C_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (zhi - C_pre )) ”
.

Definition solver_safety_wit_22 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "xlo" ) )) # Int64  |-> xlo)
  **  ((( &( "xhi" ) )) # Int64  |-> xhi)
  **  ((( &( "pairs" ) )) # Int64  |-> pairs)
  **  ((( &( "zhi" ) )) # Int64  |-> zhi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_23 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> (total + (pairs * ((zhi - C_pre ) + 1 ) ) ))
|--
  “ ((s + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s + 1 )) ”
.

Definition solver_safety_wit_24 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi < C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "C" ) )) # Int64  |-> C_pre)
  **  ((( &( "D" ) )) # Int64  |-> D_pre)
  **  ((( &( "s" ) )) # Int64  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((s + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (s + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= B_pre)) (PreH3 : (B_pre <= C_pre)) (PreH4 : (C_pre <= D_pre)) (PreH5 : (D_pre <= 500000)),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= (A_pre + B_pre )) ”
  &&  “ ((A_pre + B_pre ) <= ((B_pre + C_pre ) + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (((A_pre + B_pre ) - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre (A_pre + B_pre ) 0 ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= B_pre)) (PreH3 : (B_pre <= C_pre)) (PreH4 : (C_pre <= D_pre)) (PreH5 : (D_pre <= 500000)),
  TT && emp 
|--
  “ (TrianglePrefix A_pre B_pre C_pre D_pre (A_pre + B_pre ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= B_pre)) (PreH3 : (B_pre <= C_pre)) (PreH4 : (C_pre <= D_pre)) (PreH5 : (D_pre <= 500000)),
  (TrianglePrefix A_pre B_pre C_pre D_pre (A_pre + B_pre ) 0 )
.

Definition solver_entail_wit_2_1 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= s) ”
  &&  “ (s <= (B_pre + C_pre )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= ((s - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (A_pre = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  “ (B_pre = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre s total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (B_pre = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ (A_pre = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (B_pre = (Z.min (B_pre) ((s - B_pre ))))
.

Definition solver_entail_wit_2_1_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (A_pre = (Z.max (A_pre) ((s - C_pre ))))
.

Definition solver_entail_wit_2_2 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= s) ”
  &&  “ (s <= (B_pre + C_pre )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= ((s - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (A_pre = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  “ ((s - B_pre ) = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ (A_pre <= (s - B_pre )) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre s total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ ((s - B_pre ) = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ (A_pre = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((s - B_pre ) = (Z.min (B_pre) ((s - B_pre ))))
.

Definition solver_entail_wit_2_2_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre > (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (A_pre = (Z.max (A_pre) ((s - C_pre ))))
.

Definition solver_entail_wit_2_3 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= s) ”
  &&  “ (s <= (B_pre + C_pre )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= ((s - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ ((s - C_pre ) = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  “ (B_pre = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ ((s - C_pre ) <= B_pre) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre s total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (B_pre = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ ((s - C_pre ) = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (B_pre = (Z.min (B_pre) ((s - B_pre ))))
.

Definition solver_entail_wit_2_3_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre < (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((s - C_pre ) = (Z.max (A_pre) ((s - C_pre ))))
.

Definition solver_entail_wit_2_4 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= s) ”
  &&  “ (s <= (B_pre + C_pre )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= ((s - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ ((s - C_pre ) = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  “ ((s - B_pre ) = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ ((s - C_pre ) <= (s - B_pre )) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre s total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ ((s - B_pre ) = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ ((s - C_pre ) = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_2_4_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((s - B_pre ) = (Z.min (B_pre) ((s - B_pre ))))
.

Definition solver_entail_wit_2_4_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (B_pre >= (s - B_pre ))) (PreH2 : (A_pre <= (s - C_pre ))) (PreH3 : (s <= (B_pre + C_pre ))) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= B_pre)) (PreH6 : (B_pre <= C_pre)) (PreH7 : (C_pre <= D_pre)) (PreH8 : (D_pre <= 500000)) (PreH9 : ((A_pre + B_pre ) <= s)) (PreH10 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH11 : (0 <= total)) (PreH12 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH13 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((s - C_pre ) = (Z.max (A_pre) ((s - C_pre ))))
.

Definition solver_entail_wit_3_1 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre < (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= s) ”
  &&  “ (s <= (B_pre + C_pre )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= ((s - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (xlo = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  “ (xhi = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ (xlo <= xhi) ”
  &&  “ (((xhi - xlo ) + 1 ) = ((xhi - xlo ) + 1 )) ”
  &&  “ (1 <= ((xhi - xlo ) + 1 )) ”
  &&  “ (((xhi - xlo ) + 1 ) <= 500000) ”
  &&  “ (D_pre = (Z.min (D_pre) ((s - 1 )))) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre s total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre < (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (D_pre = (Z.min (D_pre) ((s - 1 )))) ”
  &&  “ (((xhi - xlo ) + 1 ) <= 500000) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre < (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (D_pre = (Z.min (D_pre) ((s - 1 ))))
.

Definition solver_entail_wit_3_1_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre < (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (((xhi - xlo ) + 1 ) <= 500000)
.

Definition solver_entail_wit_3_2 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre >= (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= s) ”
  &&  “ (s <= (B_pre + C_pre )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= ((s - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (xlo = (Z.max (A_pre) ((s - C_pre )))) ”
  &&  “ (xhi = (Z.min (B_pre) ((s - B_pre )))) ”
  &&  “ (xlo <= xhi) ”
  &&  “ (((xhi - xlo ) + 1 ) = ((xhi - xlo ) + 1 )) ”
  &&  “ (1 <= ((xhi - xlo ) + 1 )) ”
  &&  “ (((xhi - xlo ) + 1 ) <= 500000) ”
  &&  “ ((s - 1 ) = (Z.min (D_pre) ((s - 1 )))) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre s total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre >= (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ ((s - 1 ) = (Z.min (D_pre) ((s - 1 )))) ”
  &&  “ (((xhi - xlo ) + 1 ) <= 500000) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre >= (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((s - 1 ) = (Z.min (D_pre) ((s - 1 ))))
.

Definition solver_entail_wit_3_2_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (PreH1 : (D_pre >= (s - 1 ))) (PreH2 : (xlo <= xhi)) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= B_pre)) (PreH5 : (B_pre <= C_pre)) (PreH6 : (C_pre <= D_pre)) (PreH7 : (D_pre <= 500000)) (PreH8 : ((A_pre + B_pre ) <= s)) (PreH9 : (s <= (B_pre + C_pre ))) (PreH10 : (0 <= total)) (PreH11 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH12 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH13 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH14 : (xlo <= xhi)) (PreH15 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (((xhi - xlo ) + 1 ) <= 500000)
.

Definition solver_entail_wit_4_1 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= (s + 1 )) ”
  &&  “ ((s + 1 ) <= ((B_pre + C_pre ) + 1 )) ”
  &&  “ (0 <= (total + (pairs * ((zhi - C_pre ) + 1 ) ) )) ”
  &&  “ ((total + (pairs * ((zhi - C_pre ) + 1 ) ) ) <= (((s + 1 ) - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre (s + 1 ) (total + (pairs * ((zhi - C_pre ) + 1 ) ) ) ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (TrianglePrefix A_pre B_pre C_pre D_pre (s + 1 ) (total + (((xhi - xlo ) + 1 ) * ((zhi - C_pre ) + 1 ) ) ) ) ”
  &&  “ ((total + (((xhi - xlo ) + 1 ) * ((zhi - C_pre ) + 1 ) ) ) <= (((s + 1 ) - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (0 <= (total + (((xhi - xlo ) + 1 ) * ((zhi - C_pre ) + 1 ) ) )) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (TrianglePrefix A_pre B_pre C_pre D_pre (s + 1 ) (total + (((xhi - xlo ) + 1 ) * ((zhi - C_pre ) + 1 ) ) ) )
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  ((total + (((xhi - xlo ) + 1 ) * ((zhi - C_pre ) + 1 ) ) ) <= (((s + 1 ) - (A_pre + B_pre ) ) * 250000000000 ))
.

Definition solver_entail_wit_4_1_split_goal_3 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi >= C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (0 <= (total + (((xhi - xlo ) + 1 ) * ((zhi - C_pre ) + 1 ) ) ))
.

Definition solver_entail_wit_4_2 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi < C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= B_pre) ”
  &&  “ (B_pre <= C_pre) ”
  &&  “ (C_pre <= D_pre) ”
  &&  “ (D_pre <= 500000) ”
  &&  “ ((A_pre + B_pre ) <= (s + 1 )) ”
  &&  “ ((s + 1 ) <= ((B_pre + C_pre ) + 1 )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= (((s + 1 ) - (A_pre + B_pre ) ) * 250000000000 )) ”
  &&  “ (TrianglePrefix A_pre B_pre C_pre D_pre (s + 1 ) total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi < C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (TrianglePrefix A_pre B_pre C_pre D_pre (s + 1 ) total ) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (s: Z) (total: Z) (xlo: Z) (xhi: Z) (pairs: Z) (zhi: Z) (PreH1 : (zhi < C_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= (B_pre + C_pre ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (xlo = (Z.max (A_pre) ((s - C_pre ))))) (PreH12 : (xhi = (Z.min (B_pre) ((s - B_pre ))))) (PreH13 : (xlo <= xhi)) (PreH14 : (pairs = ((xhi - xlo ) + 1 ))) (PreH15 : (1 <= pairs)) (PreH16 : (pairs <= 500000)) (PreH17 : (zhi = (Z.min (D_pre) ((s - 1 ))))) (PreH18 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (TrianglePrefix A_pre B_pre C_pre D_pre (s + 1 ) total )
.

Definition solver_return_wit_1 :=
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (s > (B_pre + C_pre ))) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (Spec A_pre B_pre C_pre D_pre total ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (s > (B_pre + C_pre ))) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  TT && emp 
|--
  “ (Spec A_pre B_pre C_pre D_pre total ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (C_pre: Z) (D_pre: Z) (total: Z) (s: Z) (PreH1 : (s > (B_pre + C_pre ))) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= B_pre)) (PreH4 : (B_pre <= C_pre)) (PreH5 : (C_pre <= D_pre)) (PreH6 : (D_pre <= 500000)) (PreH7 : ((A_pre + B_pre ) <= s)) (PreH8 : (s <= ((B_pre + C_pre ) + 1 ))) (PreH9 : (0 <= total)) (PreH10 : (total <= ((s - (A_pre + B_pre ) ) * 250000000000 ))) (PreH11 : (TrianglePrefix A_pre B_pre C_pre D_pre s total )),
  (Spec A_pre B_pre C_pre D_pre total )
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
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.

End VC_Correct.
