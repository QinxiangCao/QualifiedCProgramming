From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P067_1415D_xor_gun_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ ((i_2 + 1 ) < (Zlength (values)))) -> ((Znth i_2 values 0) <= (Znth (i_2 + 1 ) values 0)))) (PreH5 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "bz" ) )) # Int  |->_)
  **  ((( &( "by_count" ) )) # Int  |-> 0)
  **  ((( &( "bx" ) )) # Int  |-> 0)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int  |-> (Znth (i + 1 ) values 0))
  **  ((( &( "y" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth (i - 1 ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "by_count" ) )) # Int  |->_)
  **  ((( &( "bx" ) )) # Int  |-> 0)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int  |-> (Znth (i + 1 ) values 0))
  **  ((( &( "y" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth (i - 1 ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "bx" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "z" ) )) # Int  |-> (Znth (i + 1 ) values 0))
  **  ((( &( "y" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth (i - 1 ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "z" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "y" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth (i - 1 ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "z" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "y" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "x" ) )) # Int  |-> (Znth (i - 1 ) values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH6 : (1 <= i)) (PreH7 : ((i + 1 ) < n_pre)) (PreH8 : (vx = (Znth (i - 1 ) values 0))) (PreH9 : (vy = (Znth i values 0))) (PreH10 : (vz = (Znth (i + 1 ) values 0))) (PreH11 : (by_count = 0)) (PreH12 : (bz = 0)) (PreH13 : (1 <= vx)) (PreH14 : (vx <= 1000000000)) (PreH15 : (1 <= vy)) (PreH16 : (vy <= 1000000000)) (PreH17 : (1 <= vz)) (PreH18 : (vz <= 1000000000)) (PreH19 : (1 <= x)) (PreH20 : (x <= vx)) (PreH21 : (0 <= bx)) (PreH22 : (bx <= 30)) (PreH23 : (BitScanState vx x bx )) (PreH24 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> vy)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> vy)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= x) ”
  &&  “ (1 <= 31) ”
  &&  “ (0 <= 1) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> vy)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> vy)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "x" ) )) # Int  |-> (Z.shiftr x 1))
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((bx + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (bx + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH6 : (1 <= i)) (PreH7 : ((i + 1 ) < n_pre)) (PreH8 : (vx = (Znth (i - 1 ) values 0))) (PreH9 : (vy = (Znth i values 0))) (PreH10 : (vz = (Znth (i + 1 ) values 0))) (PreH11 : (x = 1)) (PreH12 : (bz = 0)) (PreH13 : (1 <= vx)) (PreH14 : (vx <= 1000000000)) (PreH15 : (1 <= vy)) (PreH16 : (vy <= 1000000000)) (PreH17 : (1 <= vz)) (PreH18 : (vz <= 1000000000)) (PreH19 : (0 <= bx)) (PreH20 : (bx <= 30)) (PreH21 : (BitScanState vx x bx )) (PreH22 : (1 <= y)) (PreH23 : (y <= vy)) (PreH24 : (0 <= by_count)) (PreH25 : (by_count <= 30)) (PreH26 : (BitScanState vy y by_count )) (PreH27 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= y) ”
  &&  “ (1 <= 31) ”
  &&  “ (0 <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "z" ) )) # Int  |-> vz)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "y" ) )) # Int  |-> (Z.shiftr y 1))
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((by_count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (by_count + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH6 : (1 <= i)) (PreH7 : ((i + 1 ) < n_pre)) (PreH8 : (vx = (Znth (i - 1 ) values 0))) (PreH9 : (vy = (Znth i values 0))) (PreH10 : (vz = (Znth (i + 1 ) values 0))) (PreH11 : (x = 1)) (PreH12 : (y = 1)) (PreH13 : (1 <= vx)) (PreH14 : (vx <= 1000000000)) (PreH15 : (1 <= vy)) (PreH16 : (vy <= 1000000000)) (PreH17 : (1 <= vz)) (PreH18 : (vz <= 1000000000)) (PreH19 : (0 <= bx)) (PreH20 : (bx <= 30)) (PreH21 : (BitScanState vx x bx )) (PreH22 : (0 <= by_count)) (PreH23 : (by_count <= 30)) (PreH24 : (BitScanState vy y by_count )) (PreH25 : (1 <= z)) (PreH26 : (z <= vz)) (PreH27 : (0 <= bz)) (PreH28 : (bz <= 30)) (PreH29 : (BitScanState vz z bz )) (PreH30 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_20 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= z) ”
  &&  “ (1 <= 31) ”
  &&  “ (0 <= 1) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx)) (PreH15 : (vx <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "z" ) )) # Int  |-> (Z.shiftr z 1))
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((bz + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (bz + 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count = bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "bx" ) )) # Int  |-> bx)
  **  ((( &( "by_count" ) )) # Int  |-> by_count)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "bz" ) )) # Int  |-> bz)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (bx <> by_count)) (PreH2 : (z <= 1)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : (vx = (Znth (i - 1 ) values 0))) (PreH11 : (vy = (Znth i values 0))) (PreH12 : (vz = (Znth (i + 1 ) values 0))) (PreH13 : (x = 1)) (PreH14 : (y = 1)) (PreH15 : (1 <= vx)) (PreH16 : (vx <= 1000000000)) (PreH17 : (1 <= vy)) (PreH18 : (vy <= 1000000000)) (PreH19 : (1 <= vz)) (PreH20 : (vz <= 1000000000)) (PreH21 : (0 <= bx)) (PreH22 : (bx <= 30)) (PreH23 : (BitScanState vx x bx )) (PreH24 : (0 <= by_count)) (PreH25 : (by_count <= 30)) (PreH26 : (BitScanState vy y by_count )) (PreH27 : (1 <= z)) (PreH28 : (z <= vz)) (PreH29 : (0 <= bz)) (PreH30 : (bz <= 30)) (PreH31 : (BitScanState vz z bz )) (PreH32 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_25 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count <> bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (60 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 60) ”
.

Definition solver_safety_wit_27 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre > 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_28 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre <= 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "pre" ) ) 64 (repeat_Z (0) (64)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_29 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  (IntArray.full ( &( "pre" ) ) 64 (replace_Znth ((i + 1 )) ((Z.lxor (Znth i prefixes 0) (Znth i values 0))) (prefixes)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_31 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_32 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (INT_MAX <= INT_MAX) ”
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition solver_safety_wit_33 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> INT_MAX)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_34 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 60)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH6 : (0 <= l)) (PreH7 : (l < n_pre)) (PreH8 : (l <= mid)) (PreH9 : (mid <= (n_pre - 1 ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l mid (mid + 1 ) ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ ((mid + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mid + 1 )) ”
.

Definition solver_safety_wit_35 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 60)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH6 : (0 <= l)) (PreH7 : (l < n_pre)) (PreH8 : (l <= mid)) (PreH9 : (mid <= (n_pre - 1 ))) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l mid (mid + 1 ) ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ ((mid + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mid + 1 )) ”
.

Definition solver_safety_wit_37 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_38 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((mid + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mid + 1 )) ”
.

Definition solver_safety_wit_39 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ ((mid + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mid + 1 )) ”
.

Definition solver_safety_wit_41 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_42 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_43 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_44 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH2 : (r < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= mid)) (PreH10 : ((mid + 1 ) < n_pre)) (PreH11 : ((mid + 1 ) <= r)) (PreH12 : (r <= n_pre)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= INT_MAX)) (PreH15 : (PrefixXorTable values prefixes n_pre )) (PreH16 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((r - l ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((r - l ) - 1 )) ”
.

Definition solver_safety_wit_45 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH2 : (r < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= mid)) (PreH10 : ((mid + 1 ) < n_pre)) (PreH11 : ((mid + 1 ) <= r)) (PreH12 : (r <= n_pre)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= INT_MAX)) (PreH15 : (PrefixXorTable values prefixes n_pre )) (PreH16 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r - l ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r - l )) ”
.

Definition solver_safety_wit_46 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH2 : (r < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= mid)) (PreH10 : ((mid + 1 ) < n_pre)) (PreH11 : ((mid + 1 ) <= r)) (PreH12 : (r <= n_pre)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= INT_MAX)) (PreH15 : (PrefixXorTable values prefixes n_pre )) (PreH16 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_47 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) < ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (((r - l ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((r - l ) - 1 )) ”
.

Definition solver_safety_wit_48 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) < ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r - l ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r - l )) ”
.

Definition solver_safety_wit_49 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) < ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_50 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans = INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_51 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (l >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= n_pre)) (PreH9 : (0 <= ans)) (PreH10 : (ans <= INT_MAX)) (PreH11 : (PrefixXorTable values prefixes n_pre )) (PreH12 : (BruteSearchState values l l (l + 1 ) ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (INT_MAX <= INT_MAX) ”
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition solver_safety_wit_52 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans = INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_53 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ ((l + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (l + 1 )) ”
.

Definition solver_safety_wit_54 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ ((mid + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mid + 1 )) ”
.

Definition solver_safety_wit_55 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) < ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ((r - l ) - 1 ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_56 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) <= (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH2 : (r < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= mid)) (PreH10 : ((mid + 1 ) < n_pre)) (PreH11 : ((mid + 1 ) <= r)) (PreH12 : (r <= n_pre)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= INT_MAX)) (PreH15 : (PrefixXorTable values prefixes n_pre )) (PreH16 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_57 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) >= ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes 0) (Znth l prefixes 0)) > (Z.lxor (Znth (r + 1 ) prefixes 0) (Znth (mid + 1 ) prefixes 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ ((i_2 + 1 ) < (Zlength (values)))) -> ((Znth i_2 values 0) <= (Znth (i_2 + 1 ) values 0)))) (PreH5 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre - 1 )) ”
  &&  “ (NoEqualBitTriplePrefix values 1 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ ((i_2 + 1 ) < (Zlength (values)))) -> ((Znth i_2 values 0) <= (Znth (i_2 + 1 ) values 0)))) (PreH5 : (n_pre = (Zlength (values)))),
  TT && emp 
|--
  “ (NoEqualBitTriplePrefix values 1 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ ((i_2 + 1 ) < (Zlength (values)))) -> ((Znth i_2 values 0) <= (Znth (i_2 + 1 ) values 0)))) (PreH5 : (n_pre = (Zlength (values)))),
  (NoEqualBitTriplePrefix values 1 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ ((i_2 + 1 ) < (Zlength (values)))) -> ((Znth i_2 values 0) <= (Znth (i_2 + 1 ) values 0)))) (PreH5 : (n_pre = (Zlength (values)))),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ ((i_2 + 1 ) < (Zlength (values)))) -> ((Znth i_2 values 0) <= (Znth (i_2 + 1 ) values 0)))) (PreH5 : (n_pre = (Zlength (values)))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  EX (vx: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (vx = (Znth (i - 1 ) values 0)) ”
  &&  “ ((Znth i values 0) = (Znth i values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) = (Znth (i + 1 ) values 0)) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (1 <= vx) ”
  &&  “ (vx <= 1000000000) ”
  &&  “ (1 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= 1000000000) ”
  &&  “ (1 <= (Znth (i + 1 ) values 0)) ”
  &&  “ ((Znth (i + 1 ) values 0) <= 1000000000) ”
  &&  “ (1 <= (Znth (i - 1 ) values 0)) ”
  &&  “ ((Znth (i - 1 ) values 0) <= vx) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 30) ”
  &&  “ (BitScanState vx (Znth (i - 1 ) values 0) 0 ) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (BitScanState (Znth (i - 1 ) values 0) (Znth (i - 1 ) values 0) 0 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  (BitScanState (Znth (i - 1 ) values 0) (Znth (i - 1 ) values 0) 0 )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  EX (vx: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (vx = (Znth (i - 1 ) values 0)) ”
  &&  “ (vy = (Znth i values 0)) ”
  &&  “ (vz = (Znth (i + 1 ) values 0)) ”
  &&  “ (by_count = 0) ”
  &&  “ (bz = 0) ”
  &&  “ (1 <= vx) ”
  &&  “ (vx <= 1000000000) ”
  &&  “ (1 <= vy) ”
  &&  “ (vy <= 1000000000) ”
  &&  “ (1 <= vz) ”
  &&  “ (vz <= 1000000000) ”
  &&  “ (1 <= (Z.shiftr x 1)) ”
  &&  “ ((Z.shiftr x 1) <= vx) ”
  &&  “ (0 <= (bx + 1 )) ”
  &&  “ ((bx + 1 ) <= 30) ”
  &&  “ (BitScanState vx (Z.shiftr x 1) (bx + 1 ) ) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (BitScanState vx_2 (Z.shiftr x 1) (bx + 1 ) ) ”
  &&  “ ((bx + 1 ) <= 30) ”
  &&  “ ((Z.shiftr x 1) <= vx_2) ”
  &&  “ (1 <= (Z.shiftr x 1)) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  (BitScanState vx_2 (Z.shiftr x 1) (bx + 1 ) )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  ((bx + 1 ) <= 30)
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  ((Z.shiftr x 1) <= vx_2)
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  (1 <= (Z.shiftr x 1))
.

Definition solver_entail_wit_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  EX (vy_2: Z) (vx: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (vx = (Znth (i - 1 ) values 0)) ”
  &&  “ (vy_2 = (Znth i values 0)) ”
  &&  “ (vz = (Znth (i + 1 ) values 0)) ”
  &&  “ (x = 1) ”
  &&  “ (bz = 0) ”
  &&  “ (1 <= vx) ”
  &&  “ (vx <= 1000000000) ”
  &&  “ (1 <= vy_2) ”
  &&  “ (vy_2 <= 1000000000) ”
  &&  “ (1 <= vz) ”
  &&  “ (vz <= 1000000000) ”
  &&  “ (0 <= bx) ”
  &&  “ (bx <= 30) ”
  &&  “ (BitScanState vx x bx ) ”
  &&  “ (1 <= vy) ”
  &&  “ (vy <= vy_2) ”
  &&  “ (0 <= by_count) ”
  &&  “ (by_count <= 30) ”
  &&  “ (BitScanState vy_2 vy by_count ) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (BitScanState vy vy 0 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  (BitScanState vy vy 0 )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (bx: Z) (x: Z) (bz: Z) (by_count: Z) (vz: Z) (vy: Z) (vx_2: Z) (i: Z) (PreH1 : (x <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (by_count = 0)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy)) (PreH17 : (vy <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (1 <= x)) (PreH21 : (x <= vx_2)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx_2 x bx )) (PreH25 : (NoEqualBitTriplePrefix values i )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_5 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  EX (vy: Z) (vx: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (vx = (Znth (i - 1 ) values 0)) ”
  &&  “ (vy = (Znth i values 0)) ”
  &&  “ (vz = (Znth (i + 1 ) values 0)) ”
  &&  “ (x = 1) ”
  &&  “ (bz = 0) ”
  &&  “ (1 <= vx) ”
  &&  “ (vx <= 1000000000) ”
  &&  “ (1 <= vy) ”
  &&  “ (vy <= 1000000000) ”
  &&  “ (1 <= vz) ”
  &&  “ (vz <= 1000000000) ”
  &&  “ (0 <= bx) ”
  &&  “ (bx <= 30) ”
  &&  “ (BitScanState vx x bx ) ”
  &&  “ (1 <= (Z.shiftr y 1)) ”
  &&  “ ((Z.shiftr y 1) <= vy) ”
  &&  “ (0 <= (by_count + 1 )) ”
  &&  “ ((by_count + 1 ) <= 30) ”
  &&  “ (BitScanState vy (Z.shiftr y 1) (by_count + 1 ) ) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (BitScanState vy_2 (Z.shiftr y 1) (by_count + 1 ) ) ”
  &&  “ ((by_count + 1 ) <= 30) ”
  &&  “ ((Z.shiftr y 1) <= vy_2) ”
  &&  “ (1 <= (Z.shiftr y 1)) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  (BitScanState vy_2 (Z.shiftr y 1) (by_count + 1 ) )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  ((by_count + 1 ) <= 30)
.

Definition solver_entail_wit_5_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  ((Z.shiftr y 1) <= vy_2)
.

Definition solver_entail_wit_5_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  (1 <= (Z.shiftr y 1))
.

Definition solver_entail_wit_6 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  EX (vz_2: Z) (vy: Z) (vx: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (vx = (Znth (i - 1 ) values 0)) ”
  &&  “ (vy = (Znth i values 0)) ”
  &&  “ (vz_2 = (Znth (i + 1 ) values 0)) ”
  &&  “ (x = 1) ”
  &&  “ (y = 1) ”
  &&  “ (1 <= vx) ”
  &&  “ (vx <= 1000000000) ”
  &&  “ (1 <= vy) ”
  &&  “ (vy <= 1000000000) ”
  &&  “ (1 <= vz_2) ”
  &&  “ (vz_2 <= 1000000000) ”
  &&  “ (0 <= bx) ”
  &&  “ (bx <= 30) ”
  &&  “ (BitScanState vx x bx ) ”
  &&  “ (0 <= by_count) ”
  &&  “ (by_count <= 30) ”
  &&  “ (BitScanState vy y by_count ) ”
  &&  “ (1 <= vz) ”
  &&  “ (vz <= vz_2) ”
  &&  “ (0 <= bz) ”
  &&  “ (bz <= 30) ”
  &&  “ (BitScanState vz_2 vz bz ) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (BitScanState vz vz 0 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  (BitScanState vz vz 0 )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_6_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (by_count: Z) (y: Z) (bx: Z) (bz: Z) (x: Z) (vz: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (y <= 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (bz = 0)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz)) (PreH19 : (vz <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (1 <= y)) (PreH24 : (y <= vy_2)) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy_2 y by_count )) (PreH28 : (NoEqualBitTriplePrefix values i )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_7 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz_2: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz_2 = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz_2)) (PreH19 : (vz_2 <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy_2 y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz_2)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz_2 z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  EX (vz: Z) (vy: Z) (vx: Z),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (vx = (Znth (i - 1 ) values 0)) ”
  &&  “ (vy = (Znth i values 0)) ”
  &&  “ (vz = (Znth (i + 1 ) values 0)) ”
  &&  “ (x = 1) ”
  &&  “ (y = 1) ”
  &&  “ (1 <= vx) ”
  &&  “ (vx <= 1000000000) ”
  &&  “ (1 <= vy) ”
  &&  “ (vy <= 1000000000) ”
  &&  “ (1 <= vz) ”
  &&  “ (vz <= 1000000000) ”
  &&  “ (0 <= bx) ”
  &&  “ (bx <= 30) ”
  &&  “ (BitScanState vx x bx ) ”
  &&  “ (0 <= by_count) ”
  &&  “ (by_count <= 30) ”
  &&  “ (BitScanState vy y by_count ) ”
  &&  “ (1 <= (Z.shiftr z 1)) ”
  &&  “ ((Z.shiftr z 1) <= vz) ”
  &&  “ (0 <= (bz + 1 )) ”
  &&  “ ((bz + 1 ) <= 30) ”
  &&  “ (BitScanState vz (Z.shiftr z 1) (bz + 1 ) ) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz_2: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz_2 = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz_2)) (PreH19 : (vz_2 <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy_2 y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz_2)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz_2 z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (BitScanState vz_2 (Z.shiftr z 1) (bz + 1 ) ) ”
  &&  “ ((bz + 1 ) <= 30) ”
  &&  “ ((Z.shiftr z 1) <= vz_2) ”
  &&  “ (1 <= (Z.shiftr z 1)) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz_2: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz_2 = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz_2)) (PreH19 : (vz_2 <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy_2 y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz_2)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz_2 z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  (BitScanState vz_2 (Z.shiftr z 1) (bz + 1 ) )
.

Definition solver_entail_wit_7_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz_2: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz_2 = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz_2)) (PreH19 : (vz_2 <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy_2 y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz_2)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz_2 z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  ((bz + 1 ) <= 30)
.

Definition solver_entail_wit_7_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz_2: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz_2 = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz_2)) (PreH19 : (vz_2 <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy_2 y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz_2)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz_2 z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  ((Z.shiftr z 1) <= vz_2)
.

Definition solver_entail_wit_7_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz_2: Z) (vy_2: Z) (vx_2: Z) (i: Z) (PreH1 : (z > 1)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : (vx_2 = (Znth (i - 1 ) values 0))) (PreH10 : (vy_2 = (Znth i values 0))) (PreH11 : (vz_2 = (Znth (i + 1 ) values 0))) (PreH12 : (x = 1)) (PreH13 : (y = 1)) (PreH14 : (1 <= vx_2)) (PreH15 : (vx_2 <= 1000000000)) (PreH16 : (1 <= vy_2)) (PreH17 : (vy_2 <= 1000000000)) (PreH18 : (1 <= vz_2)) (PreH19 : (vz_2 <= 1000000000)) (PreH20 : (0 <= bx)) (PreH21 : (bx <= 30)) (PreH22 : (BitScanState vx_2 x bx )) (PreH23 : (0 <= by_count)) (PreH24 : (by_count <= 30)) (PreH25 : (BitScanState vy_2 y by_count )) (PreH26 : (1 <= z)) (PreH27 : (z <= vz_2)) (PreH28 : (0 <= bz)) (PreH29 : (bz <= 30)) (PreH30 : (BitScanState vz_2 z bz )) (PreH31 : (NoEqualBitTriplePrefix values i )),
  (1 <= (Z.shiftr z 1))
.

Definition solver_entail_wit_8_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (bx <> by_count)) (PreH2 : (z <= 1)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : (vx = (Znth (i - 1 ) values 0))) (PreH11 : (vy = (Znth i values 0))) (PreH12 : (vz = (Znth (i + 1 ) values 0))) (PreH13 : (x = 1)) (PreH14 : (y = 1)) (PreH15 : (1 <= vx)) (PreH16 : (vx <= 1000000000)) (PreH17 : (1 <= vy)) (PreH18 : (vy <= 1000000000)) (PreH19 : (1 <= vz)) (PreH20 : (vz <= 1000000000)) (PreH21 : (0 <= bx)) (PreH22 : (bx <= 30)) (PreH23 : (BitScanState vx x bx )) (PreH24 : (0 <= by_count)) (PreH25 : (by_count <= 30)) (PreH26 : (BitScanState vy y by_count )) (PreH27 : (1 <= z)) (PreH28 : (z <= vz)) (PreH29 : (0 <= bz)) (PreH30 : (bz <= 30)) (PreH31 : (BitScanState vz z bz )) (PreH32 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (NoEqualBitTriplePrefix values (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (bx <> by_count)) (PreH2 : (z <= 1)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : (vx = (Znth (i - 1 ) values 0))) (PreH11 : (vy = (Znth i values 0))) (PreH12 : (vz = (Znth (i + 1 ) values 0))) (PreH13 : (x = 1)) (PreH14 : (y = 1)) (PreH15 : (1 <= vx)) (PreH16 : (vx <= 1000000000)) (PreH17 : (1 <= vy)) (PreH18 : (vy <= 1000000000)) (PreH19 : (1 <= vz)) (PreH20 : (vz <= 1000000000)) (PreH21 : (0 <= bx)) (PreH22 : (bx <= 30)) (PreH23 : (BitScanState vx x bx )) (PreH24 : (0 <= by_count)) (PreH25 : (by_count <= 30)) (PreH26 : (BitScanState vy y by_count )) (PreH27 : (1 <= z)) (PreH28 : (z <= vz)) (PreH29 : (0 <= bz)) (PreH30 : (bz <= 30)) (PreH31 : (BitScanState vz z bz )) (PreH32 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (NoEqualBitTriplePrefix values (i + 1 ) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_8_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (bx <> by_count)) (PreH2 : (z <= 1)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : (vx = (Znth (i - 1 ) values 0))) (PreH11 : (vy = (Znth i values 0))) (PreH12 : (vz = (Znth (i + 1 ) values 0))) (PreH13 : (x = 1)) (PreH14 : (y = 1)) (PreH15 : (1 <= vx)) (PreH16 : (vx <= 1000000000)) (PreH17 : (1 <= vy)) (PreH18 : (vy <= 1000000000)) (PreH19 : (1 <= vz)) (PreH20 : (vz <= 1000000000)) (PreH21 : (0 <= bx)) (PreH22 : (bx <= 30)) (PreH23 : (BitScanState vx x bx )) (PreH24 : (0 <= by_count)) (PreH25 : (by_count <= 30)) (PreH26 : (BitScanState vy y by_count )) (PreH27 : (1 <= z)) (PreH28 : (z <= vz)) (PreH29 : (0 <= bz)) (PreH30 : (bz <= 30)) (PreH31 : (BitScanState vz z bz )) (PreH32 : (NoEqualBitTriplePrefix values i )),
  (NoEqualBitTriplePrefix values (i + 1 ) )
.

Definition solver_entail_wit_8_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (bx <> by_count)) (PreH2 : (z <= 1)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : (vx = (Znth (i - 1 ) values 0))) (PreH11 : (vy = (Znth i values 0))) (PreH12 : (vz = (Znth (i + 1 ) values 0))) (PreH13 : (x = 1)) (PreH14 : (y = 1)) (PreH15 : (1 <= vx)) (PreH16 : (vx <= 1000000000)) (PreH17 : (1 <= vy)) (PreH18 : (vy <= 1000000000)) (PreH19 : (1 <= vz)) (PreH20 : (vz <= 1000000000)) (PreH21 : (0 <= bx)) (PreH22 : (bx <= 30)) (PreH23 : (BitScanState vx x bx )) (PreH24 : (0 <= by_count)) (PreH25 : (by_count <= 30)) (PreH26 : (BitScanState vy y by_count )) (PreH27 : (1 <= z)) (PreH28 : (z <= vz)) (PreH29 : (0 <= bz)) (PreH30 : (bz <= 30)) (PreH31 : (BitScanState vz z bz )) (PreH32 : (NoEqualBitTriplePrefix values i )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_8_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (bx <> by_count)) (PreH2 : (z <= 1)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : (vx = (Znth (i - 1 ) values 0))) (PreH11 : (vy = (Znth i values 0))) (PreH12 : (vz = (Znth (i + 1 ) values 0))) (PreH13 : (x = 1)) (PreH14 : (y = 1)) (PreH15 : (1 <= vx)) (PreH16 : (vx <= 1000000000)) (PreH17 : (1 <= vy)) (PreH18 : (vy <= 1000000000)) (PreH19 : (1 <= vz)) (PreH20 : (vz <= 1000000000)) (PreH21 : (0 <= bx)) (PreH22 : (bx <= 30)) (PreH23 : (BitScanState vx x bx )) (PreH24 : (0 <= by_count)) (PreH25 : (by_count <= 30)) (PreH26 : (BitScanState vy y by_count )) (PreH27 : (1 <= z)) (PreH28 : (z <= vz)) (PreH29 : (0 <= bz)) (PreH30 : (bz <= 30)) (PreH31 : (BitScanState vz z bz )) (PreH32 : (NoEqualBitTriplePrefix values i )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_8_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count <> bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (NoEqualBitTriplePrefix values (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count <> bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (NoEqualBitTriplePrefix values (i + 1 ) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_8_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count <> bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  (NoEqualBitTriplePrefix values (i + 1 ) )
.

Definition solver_entail_wit_8_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count <> bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_8_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count <> bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_9 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre <= 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full ( &( "pre" ) ) 64 (repeat_Z (0) (64)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (PrefixXorTable values prefixes 0 ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (n_pre <= 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (PrefixXorTable values (repeat_Z (0) (64)) 0 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (n_pre <= 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  (PrefixXorTable values (repeat_Z (0) (64)) 0 )
.

Definition solver_entail_wit_9_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (n_pre <= 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_9_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (n_pre <= 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_10 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  (IntArray.full ( &( "pre" ) ) 64 (replace_Znth ((i + 1 )) ((Z.lxor (Znth i prefixes_2 0) (Znth i values 0))) (prefixes_2)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (PrefixXorTable values prefixes (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  TT && emp 
|--
  “ (PrefixXorTable values (replace_Znth ((i + 1 )) ((Z.lxor (Znth i prefixes_2 0) (Znth i values 0))) (prefixes_2)) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  (PrefixXorTable values (replace_Znth ((i + 1 )) ((Z.lxor (Znth i prefixes_2 0) (Znth i values 0))) (prefixes_2)) (i + 1 ) )
.

Definition solver_entail_wit_11 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= INT_MAX) ”
  &&  “ (INT_MAX <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values 0 0 (0 + 1 ) INT_MAX ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  TT && emp 
|--
  “ (BruteSearchState values 0 0 (0 + 1 ) INT_MAX ) ”
  &&  “ (PrefixXorTable values prefixes_2 n_pre ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  (BruteSearchState values 0 0 (0 + 1 ) INT_MAX )
.

Definition solver_entail_wit_11_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  (PrefixXorTable values prefixes_2 n_pre )
.

Definition solver_entail_wit_11_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_11_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes_2 i )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_12 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (l: Z) (PreH1 : (l < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= n_pre)) (PreH9 : (0 <= ans)) (PreH10 : (ans <= INT_MAX)) (PreH11 : (PrefixXorTable values prefixes_2 n_pre )) (PreH12 : (BruteSearchState values l l (l + 1 ) ans )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (l <= l) ”
  &&  “ (l <= (n_pre - 1 )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l l (l + 1 ) ans ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (l: Z) (PreH1 : (l < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= n_pre)) (PreH9 : (0 <= ans)) (PreH10 : (ans <= INT_MAX)) (PreH11 : (PrefixXorTable values prefixes_2 n_pre )) (PreH12 : (BruteSearchState values l l (l + 1 ) ans )),
  TT && emp 
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (l: Z) (PreH1 : (l < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= n_pre)) (PreH9 : (0 <= ans)) (PreH10 : (ans <= INT_MAX)) (PreH11 : (PrefixXorTable values prefixes_2 n_pre )) (PreH12 : (BruteSearchState values l l (l + 1 ) ans )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_12_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (l: Z) (PreH1 : (l < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= n_pre)) (PreH9 : (0 <= ans)) (PreH10 : (ans <= INT_MAX)) (PreH11 : (PrefixXorTable values prefixes_2 n_pre )) (PreH12 : (BruteSearchState values l l (l + 1 ) ans )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_13 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= (mid + 1 )) ”
  &&  “ ((mid + 1 ) <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid (mid + 1 ) ans ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  TT && emp 
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_13_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_14 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= (l + 1 )) ”
  &&  “ ((l + 1 ) <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values (l + 1 ) (l + 1 ) ((l + 1 ) + 1 ) ans ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  TT && emp 
|--
  “ (BruteSearchState values (l + 1 ) (l + 1 ) ((l + 1 ) + 1 ) ans ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_14_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  (BruteSearchState values (l + 1 ) (l + 1 ) ((l + 1 ) + 1 ) ans )
.

Definition solver_entail_wit_14_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_14_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (mid: Z) (l: Z) (PreH1 : ((mid + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l < n_pre)) (PreH9 : (l <= mid)) (PreH10 : (mid <= (n_pre - 1 ))) (PreH11 : (0 <= ans)) (PreH12 : (ans <= INT_MAX)) (PreH13 : (PrefixXorTable values prefixes_2 n_pre )) (PreH14 : (BruteSearchState values l mid (mid + 1 ) ans )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_15 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes_2 n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l < n_pre) ”
  &&  “ (l <= (mid + 1 )) ”
  &&  “ ((mid + 1 ) <= (n_pre - 1 )) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l (mid + 1 ) ((mid + 1 ) + 1 ) ans ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes_2 n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  TT && emp 
|--
  “ (BruteSearchState values l (mid + 1 ) ((mid + 1 ) + 1 ) ans ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes_2 n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (BruteSearchState values l (mid + 1 ) ((mid + 1 ) + 1 ) ans )
.

Definition solver_entail_wit_15_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes_2 n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))
.

Definition solver_entail_wit_15_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z), (((0 <= k_4) /\ ((k_4 + 1 ) < n_pre)) -> ((Znth k_4 values 0) <= (Znth (k_4 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes_2 n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_16_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) < ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) > (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes_2 n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= n_pre) ”
  &&  “ (0 <= ((r - l ) - 1 )) ”
  &&  “ (((r - l ) - 1 ) <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid (r + 1 ) ((r - l ) - 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) < ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) > (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes_2 n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  TT && emp 
|--
  “ (BruteSearchState values l mid (r + 1 ) ((r - l ) - 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_16_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) < ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) > (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes_2 n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (BruteSearchState values l mid (r + 1 ) ((r - l ) - 1 ) )
.

Definition solver_entail_wit_16_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) <= (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH2 : (r < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= mid)) (PreH10 : ((mid + 1 ) < n_pre)) (PreH11 : ((mid + 1 ) <= r)) (PreH12 : (r <= n_pre)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= INT_MAX)) (PreH15 : (PrefixXorTable values prefixes_2 n_pre )) (PreH16 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid (r + 1 ) ans ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) <= (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH2 : (r < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= mid)) (PreH10 : ((mid + 1 ) < n_pre)) (PreH11 : ((mid + 1 ) <= r)) (PreH12 : (r <= n_pre)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= INT_MAX)) (PreH15 : (PrefixXorTable values prefixes_2 n_pre )) (PreH16 : (BruteSearchState values l mid r ans )),
  TT && emp 
|--
  “ (BruteSearchState values l mid (r + 1 ) ans ) ”
  &&  emp
).

Definition solver_entail_wit_16_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) <= (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH2 : (r < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= mid)) (PreH10 : ((mid + 1 ) < n_pre)) (PreH11 : ((mid + 1 ) <= r)) (PreH12 : (r <= n_pre)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= INT_MAX)) (PreH15 : (PrefixXorTable values prefixes_2 n_pre )) (PreH16 : (BruteSearchState values l mid r ans )),
  (BruteSearchState values l mid (r + 1 ) ans )
.

Definition solver_entail_wit_16_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) >= ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) > (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes_2 n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes_2 )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (prefixes: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid (r + 1 ) ans ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) >= ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) > (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes_2 n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  TT && emp 
|--
  “ (BruteSearchState values l mid (r + 1 ) ans ) ”
  &&  emp
).

Definition solver_entail_wit_16_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes_2: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (((r - l ) - 1 ) >= ans)) (PreH2 : ((Z.lxor (Znth (mid + 1 ) prefixes_2 0) (Znth l prefixes_2 0)) > (Z.lxor (Znth (r + 1 ) prefixes_2 0) (Znth (mid + 1 ) prefixes_2 0)))) (PreH3 : (r < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 60)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (0 <= l)) (PreH10 : (l <= mid)) (PreH11 : ((mid + 1 ) < n_pre)) (PreH12 : ((mid + 1 ) <= r)) (PreH13 : (r <= n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= INT_MAX)) (PreH16 : (PrefixXorTable values prefixes_2 n_pre )) (PreH17 : (BruteSearchState values l mid r ans )),
  (BruteSearchState values l mid (r + 1 ) ans )
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans = INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec values (-1) ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans = INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  TT && emp 
|--
  “ (Spec values (-1) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans = INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  (Spec values (-1) )
.

Definition solver_return_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans <> INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec values ans ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans <> INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  TT && emp 
|--
  “ (Spec values ans ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (l: Z) (PreH1 : (ans <> INT_MAX)) (PreH2 : (l >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 60)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (0 <= l)) (PreH9 : (l <= n_pre)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= INT_MAX)) (PreH12 : (PrefixXorTable values prefixes n_pre )) (PreH13 : (BruteSearchState values l l (l + 1 ) ans )),
  (Spec values ans )
.

Definition solver_return_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre > 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec values 1 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (n_pre > 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (Spec values 1 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (n_pre > 60)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoEqualBitTriplePrefix values i )),
  (Spec values 1 )
.

Definition solver_return_wit_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count = bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec values 1 ) ”
  &&  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count = bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  TT && emp 
|--
  “ (Spec values 1 ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (bz: Z) (z: Z) (by_count: Z) (bx: Z) (y: Z) (x: Z) (vz: Z) (vy: Z) (vx: Z) (i: Z) (PreH1 : (by_count = bz)) (PreH2 : (bx = by_count)) (PreH3 : (z <= 1)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH9 : (1 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : (vx = (Znth (i - 1 ) values 0))) (PreH12 : (vy = (Znth i values 0))) (PreH13 : (vz = (Znth (i + 1 ) values 0))) (PreH14 : (x = 1)) (PreH15 : (y = 1)) (PreH16 : (1 <= vx)) (PreH17 : (vx <= 1000000000)) (PreH18 : (1 <= vy)) (PreH19 : (vy <= 1000000000)) (PreH20 : (1 <= vz)) (PreH21 : (vz <= 1000000000)) (PreH22 : (0 <= bx)) (PreH23 : (bx <= 30)) (PreH24 : (BitScanState vx x bx )) (PreH25 : (0 <= by_count)) (PreH26 : (by_count <= 30)) (PreH27 : (BitScanState vy y by_count )) (PreH28 : (1 <= z)) (PreH29 : (z <= vz)) (PreH30 : (0 <= bz)) (PreH31 : (bz <= 30)) (PreH32 : (BitScanState vz z bz )) (PreH33 : (NoEqualBitTriplePrefix values i )),
  (Spec values 1 )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (((a_pre + ((i + 1 ) * sizeof(INT)))) # Int  |-> (Znth (i + 1 ) values 0))
  **  (IntArray.missing_i a_pre (i + 1 ) 0 n_pre values )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoEqualBitTriplePrefix values i )),
  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (NoEqualBitTriplePrefix values i ) ”
  &&  (((a_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) values 0))
  **  (IntArray.missing_i a_pre (i - 1 ) 0 n_pre values )
.

Definition solver_partial_solve_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (PrefixXorTable values prefixes i ) ”
  &&  (((( &( "pre" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i prefixes 0))
  **  (IntArray.missing_i ( &( "pre" ) ) i 0 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (PrefixXorTable values prefixes i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
.

Definition solver_partial_solve_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (PrefixXorTable values prefixes i )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (PrefixXorTable values prefixes i ) ”
  &&  (((( &( "pre" ) ) + ((i + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "pre" ) ) (i + 1 ) 0 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full ( &( "pre" ) ) 64 prefixes )
|--
  “ (r < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= r) ”
  &&  “ (r <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid r ans ) ”
  &&  (((( &( "pre" ) ) + ((mid + 1 ) * sizeof(INT)))) # Int  |-> (Znth (mid + 1 ) prefixes 0))
  **  (IntArray.missing_i ( &( "pre" ) ) (mid + 1 ) 0 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (r < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= r) ”
  &&  “ (r <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid r ans ) ”
  &&  (((( &( "pre" ) ) + (l * sizeof(INT)))) # Int  |-> (Znth l prefixes 0))
  **  (IntArray.missing_i ( &( "pre" ) ) l 0 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (r < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= r) ”
  &&  “ (r <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid r ans ) ”
  &&  (((( &( "pre" ) ) + ((r + 1 ) * sizeof(INT)))) # Int  |-> (Znth (r + 1 ) prefixes 0))
  **  (IntArray.missing_i ( &( "pre" ) ) (r + 1 ) 0 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (prefixes: (@list Z)) (ans: Z) (r: Z) (mid: Z) (l: Z) (PreH1 : (r < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 60)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0)))) (PreH7 : (0 <= l)) (PreH8 : (l <= mid)) (PreH9 : ((mid + 1 ) < n_pre)) (PreH10 : ((mid + 1 ) <= r)) (PreH11 : (r <= n_pre)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= INT_MAX)) (PreH14 : (PrefixXorTable values prefixes n_pre )) (PreH15 : (BruteSearchState values l mid r ans )),
  (IntArray.full ( &( "pre" ) ) 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (r < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 60) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ ((k_2 + 1 ) < n_pre)) -> ((Znth k_2 values 0) <= (Znth (k_2 + 1 ) values 0))) ”
  &&  “ (0 <= l) ”
  &&  “ (l <= mid) ”
  &&  “ ((mid + 1 ) < n_pre) ”
  &&  “ ((mid + 1 ) <= r) ”
  &&  “ (r <= n_pre) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= INT_MAX) ”
  &&  “ (PrefixXorTable values prefixes n_pre ) ”
  &&  “ (BruteSearchState values l mid r ans ) ”
  &&  (((( &( "pre" ) ) + ((mid + 1 ) * sizeof(INT)))) # Int  |-> (Znth (mid + 1 ) prefixes 0))
  **  (IntArray.missing_i ( &( "pre" ) ) (mid + 1 ) 0 64 prefixes )
  **  (IntArray.full a_pre n_pre values )
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
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_entail_wit_16_1 : solver_entail_wit_16_1.
Axiom proof_of_solver_entail_wit_16_2 : solver_entail_wit_16_2.
Axiom proof_of_solver_entail_wit_16_3 : solver_entail_wit_16_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
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

End VC_Correct.
