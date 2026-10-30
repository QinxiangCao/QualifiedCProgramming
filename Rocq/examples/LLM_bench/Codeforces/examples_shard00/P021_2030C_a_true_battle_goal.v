From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH5 : ((Znth 0 values 0) <> 49)) (PreH6 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoAdjacentOnesBefore values i )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH5 : ((Znth 0 values 0) <> 49)) (PreH6 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (NoAdjacentOnesBefore values i )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH6 : ((Znth 0 values 0) <> 49)) (PreH7 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (49 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH6 : ((Znth 0 values 0) <> 49)) (PreH7 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoAdjacentOnesBefore values i )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49))) ”
  &&  “ ((Znth 0 values 0) <> 49) ”
  &&  “ ((Znth ((Zlength (values)) - 1 ) values 0) <> 49) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  “ (NoAdjacentOnesBefore values 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  TT && emp 
|--
  “ (NoAdjacentOnesBefore values 0 ) ”
  &&  “ ((Znth (n_pre - 1 ) values 0) <> 49) ”
  &&  “ ((Znth 0 values 0) <> 49) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (NoAdjacentOnesBefore values 0 )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  ((Znth (n_pre - 1 ) values 0) <> 49)
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  ((Znth 0 values 0) <> 49)
.

Definition solver_entail_wit_1_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))
.

Definition solver_entail_wit_2_1 :=
(
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49))) ”
  &&  “ ((Znth 0 values 0) <> 49) ”
  &&  “ ((Znth ((Zlength (values)) - 1 ) values 0) <> 49) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (NoAdjacentOnesBefore values (i + 1 ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  TT && emp 
|--
  “ (NoAdjacentOnesBefore values (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  (NoAdjacentOnesBefore values (i + 1 ) )
.

Definition solver_entail_wit_2_2 :=
(
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49))) ”
  &&  “ ((Znth 0 values 0) <> 49) ”
  &&  “ ((Znth ((Zlength (values)) - 1 ) values 0) <> 49) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ”
  &&  “ (NoAdjacentOnesBefore values (i + 1 ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  TT && emp 
|--
  “ (NoAdjacentOnesBefore values (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  (NoAdjacentOnesBefore values (i + 1 ) )
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH6 : ((Znth 0 values 0) <> 49)) (PreH7 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec values 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH6 : ((Znth 0 values 0) <> 49)) (PreH7 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoAdjacentOnesBefore values i )),
  TT && emp 
|--
  “ (Spec values 0 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH6 : ((Znth 0 values 0) <> 49)) (PreH7 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoAdjacentOnesBefore values i )),
  (Spec values 0 )
.

Definition solver_return_wit_2 :=
(
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec values 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  TT && emp 
|--
  “ (Spec values 1 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : ((Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH3 : ((i + 1 ) < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH8 : ((Znth 0 values 0) <> 49)) (PreH9 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 1 ))) (PreH12 : (NoAdjacentOnesBefore values i )),
  (Spec values 1 )
.

Definition solver_return_wit_3 :=
(
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec values 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  TT && emp 
|--
  “ (Spec values 1 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (Spec values 1 )
.

Definition solver_return_wit_4 :=
(
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec values 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  TT && emp 
|--
  “ (Spec values 1 ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (Spec values 1 )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49))) ”
  &&  (((s_pre + (0 * sizeof(CHAR)))) # Char  |-> (Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre 0 0 (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (PreH1 : ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((Znth 0 (app (values) ((cons (0) ((@nil Z))))) 0) <> 49) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> (((Znth i values 0) = 48) \/ ((Znth i values 0) = 49))) ”
  &&  (((s_pre + ((n_pre - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (n_pre - 1 ) (app (values) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (n_pre - 1 ) 0 (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH6 : ((Znth 0 values 0) <> 49)) (PreH7 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49))) ”
  &&  “ ((Znth 0 values 0) <> 49) ”
  &&  “ ((Znth ((Zlength (values)) - 1 ) values 0) <> 49) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (NoAdjacentOnesBefore values i ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (values) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
.

Definition solver_partial_solve_wit_4 :=
forall (values: (@list Z)) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49)))) (PreH7 : ((Znth 0 values 0) <> 49)) (PreH8 : ((Znth ((Zlength (values)) - 1 ) values 0) <> 49)) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (NoAdjacentOnesBefore values i )),
  (CharArray.full s_pre (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
|--
  “ ((Znth i (app (values) ((cons (0) ((@nil Z))))) 0) = 49) ”
  &&  “ ((i + 1 ) < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 200000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> (((Znth k values 0) = 48) \/ ((Znth k values 0) = 49))) ”
  &&  “ ((Znth 0 values 0) <> 49) ”
  &&  “ ((Znth ((Zlength (values)) - 1 ) values 0) <> 49) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (n_pre - 1 )) ”
  &&  “ (NoAdjacentOnesBefore values i ) ”
  &&  (((s_pre + ((i + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (i + 1 ) (app (values) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (i + 1 ) 0 (n_pre + 1 ) (app (values) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
