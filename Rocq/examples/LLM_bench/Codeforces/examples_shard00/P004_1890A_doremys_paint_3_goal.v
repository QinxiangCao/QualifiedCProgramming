From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))),
  ((( &( "cy" ) )) # Int  |->_)
  **  ((( &( "cx" ) )) # Int  |-> 0)
  **  ((( &( "y" ) )) # Int  |-> (-1))
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))),
  ((( &( "cx" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> (-1))
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))),
  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_4 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))),
  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))),
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cy" ) )) # Int  |-> 0)
  **  ((( &( "cx" ) )) # Int  |-> 0)
  **  ((( &( "y" ) )) # Int  |-> (-1))
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cx + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cx + 1 )) ”
) \/
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cx + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cx + 1 )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cx + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((INT_MIN) <= (cx + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) <> x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_9 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) <> x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cy + 1 )) ”
) \/
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cy + 1 )) ”
).

Definition solver_safety_wit_10_split_goal_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((INT_MIN) <= (cy + 1 )) ”
.

Definition solver_safety_wit_11 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cy + 1 )) ”
) \/
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cy + 1 )) ”
).

Definition solver_safety_wit_11_split_goal_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((INT_MIN) <= (cy + 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) <> y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> (cx + 1 ))
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> (cy + 1 ))
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # Int  |-> (cy + 1 ))
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH8 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cx - cy ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cx - cy )) ”
) \/
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cx - cy ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cx - cy )) ”
).

Definition solver_safety_wit_17_split_goal_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cx - cy ) <= INT_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((INT_MIN) <= (cx - cy )) ”
.

Definition solver_safety_wit_18 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy <> 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) <= 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy - cx ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cy - cx )) ”
) \/
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) <= 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy - cx ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cy - cx )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) <= 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((cy - cx ) <= INT_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) <= 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((INT_MIN) <= (cy - cx )) ”
.

Definition solver_safety_wit_20 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) <= 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # Int  |-> cy)
  **  ((( &( "cx" ) )) # Int  |-> cx)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input 0)) /\ ((Znth idx_2 input 0) <= 100000)))),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input 0 (Znth 0 input 0) (-1) 0 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input 0)) /\ ((Znth idx_2 input 0) <= 100000)))),
  TT && emp 
|--
  “ (PaintScanState input 0 (Znth 0 input 0) (-1) 0 0 ) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input 0)) /\ ((Znth idx_2 input 0) <= 100000)))),
  (PaintScanState input 0 (Znth 0 input 0) (-1) 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (input: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (input)))) -> ((1 <= (Znth idx_2 input 0)) /\ ((Znth idx_2 input 0) <= 100000)))),
  forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))
.

Definition solver_entail_wit_2_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input (i + 1 ) x y (cx + 1 ) cy ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (PaintScanState input (i + 1 ) x y (cx + 1 ) cy ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = x)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (PaintScanState input (i + 1 ) x y (cx + 1 ) cy )
.

Definition solver_entail_wit_2_2 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input (i + 1 ) x (Znth i input 0) cx (cy + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (PaintScanState input (i + 1 ) x (Znth i input 0) cx (cy + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (PaintScanState input (i + 1 ) x (Znth i input 0) cx (cy + 1 ) )
.

Definition solver_entail_wit_2_3 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input (i + 1 ) x (Znth i input 0) cx (cy + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (PaintScanState input (i + 1 ) x y cx (cy + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (PaintScanState input (i + 1 ) x y cx (cy + 1 ) )
.

Definition solver_return_wit_1 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (Spec input 1 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (Spec input 1 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (cy = 0)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH9 : (PaintScanState input i x y cx cy )),
  (Spec input 1 )
.

Definition solver_return_wit_2 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cy - cx ) > 1)) (PreH2 : ((cx - cy ) <= 1)) (PreH3 : (cy <> 0)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (Spec input 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cy - cx ) > 1)) (PreH2 : ((cx - cy ) <= 1)) (PreH3 : (cy <> 0)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (Spec input 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cy - cx ) > 1)) (PreH2 : ((cx - cy ) <= 1)) (PreH3 : (cy <> 0)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (Spec input 0 )
.

Definition solver_return_wit_3 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cy - cx ) <= 1)) (PreH2 : ((cx - cy ) <= 1)) (PreH3 : (cy <> 0)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (Spec input 1 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cy - cx ) <= 1)) (PreH2 : ((cx - cy ) <= 1)) (PreH3 : (cy <> 0)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (Spec input 1 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cy - cx ) <= 1)) (PreH2 : ((cx - cy ) <= 1)) (PreH3 : (cy <> 0)) (PreH4 : (i >= n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (Spec input 1 )
.

Definition solver_return_wit_4 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) > 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (Spec input 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) > 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (Spec input 0 ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((cx - cy ) > 1)) (PreH2 : (cy <> 0)) (PreH3 : (i >= n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (Spec input 0 )
.

Definition solver_return_wit_5 :=
(
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) <> y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (Spec input 0 ) ”
  &&  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) <> y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  TT && emp 
|--
  “ (Spec input 0 ) ”
  &&  emp
).

Definition solver_return_wit_5_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) <> y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (Spec input 0 )
.

Definition solver_partial_solve_wit_1 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (2 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100)) (PreH4 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= (Zlength (input))) ”
  &&  “ ((Zlength (input)) <= 100) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (input)))) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 input 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
.

Definition solver_partial_solve_wit_2 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH8 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input i x y cx cy ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
.

Definition solver_partial_solve_wit_3 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y <> (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (y <> (-1)) ”
  &&  “ ((Znth i input 0) <> x) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input i x y cx cy ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
.

Definition solver_partial_solve_wit_4 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : (y = (-1))) (PreH2 : ((Znth i input 0) <> x)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH10 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ (y = (-1)) ”
  &&  “ ((Znth i input 0) <> x) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input i x y cx cy ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
.

Definition solver_partial_solve_wit_5 :=
forall (input: (@list Z)) (a_pre: Z) (n_pre: Z) (x: Z) (y: Z) (cx: Z) (cy: Z) (i: Z) (PreH1 : ((Znth i input 0) = y)) (PreH2 : (y <> (-1))) (PreH3 : ((Znth i input 0) <> x)) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000)))) (PreH11 : (PaintScanState input i x y cx cy )),
  (IntArray.full a_pre n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
|--
  “ ((Znth i input 0) = y) ”
  &&  “ (y <> (-1)) ”
  &&  “ ((Znth i input 0) <> x) ”
  &&  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (input))) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (idx: Z), (((0 <= idx) /\ (idx < n_pre)) -> ((1 <= (Znth idx input 0)) /\ ((Znth idx input 0) <= 100000))) ”
  &&  “ (PaintScanState input i x y cx cy ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
  **  (IntArray.undef_seg a_pre n_pre 100 )
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
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_return_wit_5 : solver_return_wit_5.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
