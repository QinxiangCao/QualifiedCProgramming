From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P081_1965C_folding_strip_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  ((( &( "mx" ) )) # Int  |->_)
  **  ((( &( "mn" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  ((( &( "mn" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "mx" ) )) # Int  |-> 0)
  **  ((( &( "mn" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-i) <= mn)) (PreH9 : (mn <= cur)) (PreH10 : (cur <= mx)) (PreH11 : (mx <= i)) (PreH12 : ((Z.land cur 1) = (Z.land i 1))) (PreH13 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-i) <= mn)) (PreH9 : (mn <= cur)) (PreH10 : (cur <= mx)) (PreH11 : (mx <= i)) (PreH12 : ((Z.land cur 1) = (Z.land i 1))) (PreH13 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Z.land cur 1) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-i) <= mn)) (PreH10 : (mn <= cur)) (PreH11 : (cur <= mx)) (PreH12 : (mx <= i)) (PreH13 : ((Z.land cur 1) = (Z.land i 1))) (PreH14 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_8 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Z.land cur 1) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-i) <= mn)) (PreH10 : (mn <= cur)) (PreH11 : (cur <= mx)) (PreH12 : (mx <= i)) (PreH13 : ((Z.land cur 1) = (Z.land i 1))) (PreH14 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_9 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Z.land cur 1) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((-i) <= mn)) (PreH11 : (mn <= cur)) (PreH12 : (cur <= mx)) (PreH13 : (mx <= i)) (PreH14 : ((Z.land cur 1) = (Z.land i 1))) (PreH15 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((cur + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cur + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Z.land cur 1) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((-i) <= mn)) (PreH11 : (mn <= cur)) (PreH12 : (cur <= mx)) (PreH13 : (mx <= i)) (PreH14 : ((Z.land cur 1) = (Z.land i 1))) (PreH15 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((cur + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cur + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Z.land cur 1) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((-i) <= mn)) (PreH11 : (mn <= cur)) (PreH12 : (cur <= mx)) (PreH13 : (mx <= i)) (PreH14 : ((Z.land cur 1) = (Z.land i 1))) (PreH15 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((cur - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cur - 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Z.land cur 1) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((-i) <= mn)) (PreH11 : (mn <= cur)) (PreH12 : (cur <= mx)) (PreH13 : (mx <= i)) (PreH14 : ((Z.land cur 1) = (Z.land i 1))) (PreH15 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((cur - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (cur - 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) < mn)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : ((Z.land cur 1) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= (Zlength (text)))) (PreH6 : ((Zlength (text)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((-i) <= mn)) (PreH12 : (mn <= cur)) (PreH13 : (cur <= mx)) (PreH14 : (mx <= i)) (PreH15 : ((Z.land cur 1) = (Z.land i 1))) (PreH16 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ False ”
.

Definition solver_safety_wit_14 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) < mn)) (PreH2 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((Z.land cur 1) = 0)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= (Zlength (text)))) (PreH6 : ((Zlength (text)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((-i) <= mn)) (PreH12 : (mn <= cur)) (PreH13 : (cur <= mx)) (PreH14 : (mx <= i)) (PreH15 : ((Z.land cur 1) = (Z.land i 1))) (PreH16 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ False ”
.

Definition solver_safety_wit_15 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) > mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ False ”
.

Definition solver_safety_wit_16 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) > mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ False ”
.

Definition solver_safety_wit_17 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) > mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ False ”
.

Definition solver_safety_wit_18 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) > mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ False ”
.

Definition solver_safety_wit_19 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "mx" ) )) # Int  |-> (cur + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "mx" ) )) # Int  |-> (cur + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_22 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_24 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur + 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_25 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> (cur - 1 ))
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_27 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-i) <= mn)) (PreH9 : (mn <= cur)) (PreH10 : (cur <= mx)) (PreH11 : (mx <= i)) (PreH12 : ((Z.land cur 1) = (Z.land i 1))) (PreH13 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((mx - mn ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (mx - mn )) ”
.

Definition solver_entail_wit_1 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((-0) <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((Z.land 0 1) = (Z.land 0 1)) ”
  &&  “ (FoldPrefixAlternatingState text 0 0 0 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text 0 0 0 0 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  (FoldPrefixAlternatingState text 0 0 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) (PreH4 : (n_pre = (Zlength (text)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))
.

Definition solver_entail_wit_2_1 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= mn) ”
  &&  “ (mn <= (cur + 1 )) ”
  &&  “ ((cur + 1 ) <= (cur + 1 )) ”
  &&  “ ((cur + 1 ) <= (i + 1 )) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn (cur + 1 ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn (cur + 1 ) ) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn (cur + 1 ) )
.

Definition solver_entail_wit_2_1_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_entail_wit_2_2 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= mn) ”
  &&  “ (mn <= (cur + 1 )) ”
  &&  “ ((cur + 1 ) <= (cur + 1 )) ”
  &&  “ ((cur + 1 ) <= (i + 1 )) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn (cur + 1 ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn (cur + 1 ) ) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn (cur + 1 ) )
.

Definition solver_entail_wit_2_2_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) > mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_entail_wit_2_3 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= (cur - 1 )) ”
  &&  “ ((cur - 1 ) <= (cur - 1 )) ”
  &&  “ ((cur - 1 ) <= mx) ”
  &&  “ (mx <= (i + 1 )) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) (cur - 1 ) mx ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) (cur - 1 ) mx ) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) (cur - 1 ) mx )
.

Definition solver_entail_wit_2_3_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_entail_wit_2_4 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= (cur - 1 )) ”
  &&  “ ((cur - 1 ) <= (cur - 1 )) ”
  &&  “ ((cur - 1 ) <= mx) ”
  &&  “ (mx <= (i + 1 )) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) (cur - 1 ) mx ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) (cur - 1 ) mx ) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_4_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) (cur - 1 ) mx )
.

Definition solver_entail_wit_2_4_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) < mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_entail_wit_2_5 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= mn) ”
  &&  “ (mn <= (cur + 1 )) ”
  &&  “ ((cur + 1 ) <= mx) ”
  &&  “ (mx <= (i + 1 )) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn mx ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn mx ) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_5_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn mx )
.

Definition solver_entail_wit_2_5_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_entail_wit_2_6 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= mn) ”
  &&  “ (mn <= (cur + 1 )) ”
  &&  “ ((cur + 1 ) <= mx) ”
  &&  “ (mx <= (i + 1 )) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn mx ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn mx ) ”
  &&  “ ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_6_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur + 1 ) mn mx )
.

Definition solver_entail_wit_2_6_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur + 1 ) <= mx)) (PreH2 : ((cur + 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur + 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_entail_wit_2_7 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= mn) ”
  &&  “ (mn <= (cur - 1 )) ”
  &&  “ ((cur - 1 ) <= mx) ”
  &&  “ (mx <= (i + 1 )) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) mn mx ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) mn mx ) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_7_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) mn mx )
.

Definition solver_entail_wit_2_7_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : ((Z.land cur 1) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_entail_wit_2_8 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((-(i + 1 )) <= mn) ”
  &&  “ (mn <= (cur - 1 )) ”
  &&  “ ((cur - 1 ) <= mx) ”
  &&  “ (mx <= (i + 1 )) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) mn mx ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) mn mx ) ”
  &&  “ ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1)) ”
  &&  emp
).

Definition solver_entail_wit_2_8_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  (FoldPrefixAlternatingState text (i + 1 ) (cur - 1 ) mn mx )
.

Definition solver_entail_wit_2_8_split_goal_2 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((cur - 1 ) <= mx)) (PreH2 : ((cur - 1 ) >= mn)) (PreH3 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : ((Z.land cur 1) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-i) <= mn)) (PreH13 : (mn <= cur)) (PreH14 : (cur <= mx)) (PreH15 : (mx <= i)) (PreH16 : ((Z.land cur 1) = (Z.land i 1))) (PreH17 : (FoldPrefixAlternatingState text i cur mn mx )),
  ((Z.land (cur - 1 ) 1) = (Z.land (i + 1 ) 1))
.

Definition solver_return_wit_1 :=
(
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-i) <= mn)) (PreH9 : (mn <= cur)) (PreH10 : (cur <= mx)) (PreH11 : (mx <= i)) (PreH12 : ((Z.land cur 1) = (Z.land i 1))) (PreH13 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (SpecAlternatingEdges text (mx - mn ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-i) <= mn)) (PreH9 : (mn <= cur)) (PreH10 : (cur <= mx)) (PreH11 : (mx <= i)) (PreH12 : ((Z.land cur 1) = (Z.land i 1))) (PreH13 : (FoldPrefixAlternatingState text i cur mn mx )),
  TT && emp 
|--
  “ (SpecAlternatingEdges text (mx - mn ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (text: (@list Z)) (n_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((-i) <= mn)) (PreH9 : (mn <= cur)) (PreH10 : (cur <= mx)) (PreH11 : (mx <= i)) (PreH12 : ((Z.land cur 1) = (Z.land i 1))) (PreH13 : (FoldPrefixAlternatingState text i cur mn mx )),
  (SpecAlternatingEdges text (mx - mn ) )
.

Definition solver_partial_solve_wit_1 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Z.land cur 1) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-i) <= mn)) (PreH10 : (mn <= cur)) (PreH11 : (cur <= mx)) (PreH12 : (mx <= i)) (PreH13 : ((Z.land cur 1) = (Z.land i 1))) (PreH14 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((Z.land cur 1) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((-i) <= mn) ”
  &&  “ (mn <= cur) ”
  &&  “ (cur <= mx) ”
  &&  “ (mx <= i) ”
  &&  “ ((Z.land cur 1) = (Z.land i 1)) ”
  &&  “ (FoldPrefixAlternatingState text i cur mn mx ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 :=
forall (text: (@list Z)) (n_pre: Z) (s_pre: Z) (mx: Z) (cur: Z) (mn: Z) (i: Z) (PreH1 : ((Z.land cur 1) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((-i) <= mn)) (PreH10 : (mn <= cur)) (PreH11 : (cur <= mx)) (PreH12 : (mx <= i)) (PreH13 : ((Z.land cur 1) = (Z.land i 1))) (PreH14 : (FoldPrefixAlternatingState text i cur mn mx )),
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((Z.land cur 1) = 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= (Zlength (text))) ”
  &&  “ ((Zlength (text)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (text)))) -> (((Znth k text 0) = 48) \/ ((Znth k text 0) = 49))) ”
  &&  “ (n_pre = (Zlength (text))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((-i) <= mn) ”
  &&  “ (mn <= cur) ”
  &&  “ (cur <= mx) ”
  &&  “ (mx <= i) ”
  &&  “ ((Z.land cur 1) = (Z.land i 1)) ”
  &&  “ (FoldPrefixAlternatingState text i cur mn mx ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Axiom proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Axiom proof_of_solver_entail_wit_2_6 : solver_entail_wit_2_6.
Axiom proof_of_solver_entail_wit_2_7 : solver_entail_wit_2_7.
Axiom proof_of_solver_entail_wit_2_8 : solver_entail_wit_2_8.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
