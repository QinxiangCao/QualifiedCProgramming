From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P020_1994B_fun_game_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (source)))) -> (((Znth i source 0) = 48) \/ ((Znth i source 0) = 49)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (target)))) -> (((Znth i_2 target 0) = 48) \/ ((Znth i_2 target 0) = 49)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (48 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_3 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 48)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_5 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ False ”
.

Definition solver_safety_wit_6 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (strncmp_result source target n_pre retval )) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (i = n_pre)) (PreH10 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH11 : (valid_string source )) (PreH12 : (valid_string target )) (PreH13 : ((string_length (source)) = n_pre)) (PreH14 : ((string_length (target)) = n_pre)),
  (store_string s_pre source )
  **  (store_string t_pre target )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))),
  ((( &( "j" ) )) # Int  |->_)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Znth i source 0) = 49)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH13 : (0 <= j)) (PreH14 : (j <= i)) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (48 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_9 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Znth i source 0) = 49)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH14 : (0 <= j)) (PreH15 : (j <= i)) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Znth i source 0) = 49)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH13 : (0 <= j)) (PreH14 : (j <= i)) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 48)) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Znth i source 0) = 49)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH14 : (0 <= j)) (PreH15 : (j <= i)) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (source)))) -> (((Znth i source 0) = 48) \/ ((Znth i source 0) = 49)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (target)))) -> (((Znth i_2 target 0) = 48) \/ ((Znth i_2 target 0) = 49)))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 source 0) = 48)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (source)))) -> (((Znth i source 0) = 48) \/ ((Znth i source 0) = 49)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (target)))) -> (((Znth i_2 target 0) = 48) \/ ((Znth i_2 target 0) = 49)))),
  TT && emp 
|--
  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (source)))) -> (((Znth i source 0) = 48) \/ ((Znth i source 0) = 49)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (target)))) -> (((Znth i_2 target 0) = 48) \/ ((Znth i_2 target 0) = 49)))),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth k_3 source 0) = 48))
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (source)))) -> (((Znth i source 0) = 48) \/ ((Znth i source 0) = 49)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (target)))) -> (((Znth i_2 target 0) = 48) \/ ((Znth i_2 target 0) = 49)))),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (source)))) -> (((Znth i source 0) = 48) \/ ((Znth i source 0) = 49)))) (PreH7 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < (Zlength (target)))) -> (((Znth i_2 target 0) = 48) \/ ((Znth i_2 target 0) = 49)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))
.

Definition solver_entail_wit_2 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 48)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 source 0) = 48)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
.

Definition solver_entail_wit_3 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (i = n_pre) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ (valid_string source ) ”
  &&  “ (valid_string target ) ”
  &&  “ ((string_length (source)) = n_pre) ”
  &&  “ ((string_length (target)) = n_pre) ”
  &&  (store_string s_pre source )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (store_string t_pre target )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ ((string_length (target)) = n_pre) ”
  &&  “ ((string_length (source)) = n_pre) ”
  &&  “ (valid_string target ) ”
  &&  “ (valid_string source ) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ ((string_length (target)) = n_pre) ”
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ ((string_length (source)) = n_pre) ”
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ (valid_string target ) ”
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ (valid_string source ) ”
.

Definition solver_entail_wit_3_split_goal_5 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48)) ”
.

Definition solver_entail_wit_3_split_goal_6 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
.

Definition solver_entail_wit_3_split_goal_7 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
.

Definition solver_entail_wit_3_split_goal_spatial :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> (((Znth k_4 source 0) = 48) \/ ((Znth k_4 source 0) = 49)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> (((Znth k_5 target 0) = 48) \/ ((Znth k_5 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < i)) -> ((Znth k_6 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
.

Definition solver_entail_wit_4 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (source)))) -> (((Znth k_5 source 0) = 48) \/ ((Znth k_5 source 0) = 49)))) (PreH10 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (target)))) -> (((Znth k_6 target 0) = 48) \/ ((Znth k_6 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < i)) -> ((Znth k_7 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i source 0) = 49) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= i) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 < 0)) -> ((Znth k_4 target 0) = 48)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (source)))) -> (((Znth k_5 source 0) = 48) \/ ((Znth k_5 source 0) = 49)))) (PreH10 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (target)))) -> (((Znth k_6 target 0) = 48) \/ ((Znth k_6 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < i)) -> ((Znth k_7 source 0) = 48))),
  TT && emp 
|--
  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 < 0)) -> ((Znth k_4 target 0) = 48)) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ ((Znth i source 0) = 49) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (source)))) -> (((Znth k_5 source 0) = 48) \/ ((Znth k_5 source 0) = 49)))) (PreH10 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (target)))) -> (((Znth k_6 target 0) = 48) \/ ((Znth k_6 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < i)) -> ((Znth k_7 source 0) = 48))),
  forall (k_4: Z), (((0 <= k_4) /\ (k_4 < 0)) -> ((Znth k_4 target 0) = 48))
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (source)))) -> (((Znth k_5 source 0) = 48) \/ ((Znth k_5 source 0) = 49)))) (PreH10 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (target)))) -> (((Znth k_6 target 0) = 48) \/ ((Znth k_6 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < i)) -> ((Znth k_7 source 0) = 48))),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (source)))) -> (((Znth k_5 source 0) = 48) \/ ((Znth k_5 source 0) = 49)))) (PreH10 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (target)))) -> (((Znth k_6 target 0) = 48) \/ ((Znth k_6 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < i)) -> ((Znth k_7 source 0) = 48))),
  ((Znth i source 0) = 49)
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (source)))) -> (((Znth k_5 source 0) = 48) \/ ((Znth k_5 source 0) = 49)))) (PreH10 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (target)))) -> (((Znth k_6 target 0) = 48) \/ ((Znth k_6 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < i)) -> ((Znth k_7 source 0) = 48))),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))
.

Definition solver_entail_wit_4_split_goal_5 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (source)))) (PreH5 : (n_pre = (Zlength (target)))) (PreH6 : (1 <= (Zlength (source)))) (PreH7 : ((Zlength (source)) <= 200000)) (PreH8 : ((Zlength (target)) = (Zlength (source)))) (PreH9 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (source)))) -> (((Znth k_5 source 0) = 48) \/ ((Znth k_5 source 0) = 49)))) (PreH10 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (target)))) -> (((Znth k_6 target 0) = 48) \/ ((Znth k_6 target 0) = 49)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : forall (k_7: Z), (((0 <= k_7) /\ (k_7 < i)) -> ((Znth k_7 source 0) = 48))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))
.

Definition solver_entail_wit_5 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 48)) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Znth i source 0) = 49)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH14 : (0 <= j)) (PreH15 : (j <= i)) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i source 0) = 49) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= i) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (j + 1 ))) -> ((Znth k_4 target 0) = 48)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
.

Definition solver_return_wit_1 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Znth i source 0) = 49)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH13 : (0 <= j)) (PreH14 : (j <= i)) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec source target 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Znth i source 0) = 49)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH13 : (0 <= j)) (PreH14 : (j <= i)) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  TT && emp 
|--
  “ (Spec source target 1 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Znth i source 0) = 49)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH13 : (0 <= j)) (PreH14 : (j <= i)) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (Spec source target 1 )
.

Definition solver_return_wit_2 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Znth i source 0) = 49)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH14 : (0 <= j)) (PreH15 : (j <= i)) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec source target 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Znth i source 0) = 49)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH14 : (0 <= j)) (PreH15 : (j <= i)) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  TT && emp 
|--
  “ (Spec source target 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (n_pre: Z) (j: Z) (i: Z) (PreH1 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 48)) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Znth i source 0) = 49)) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH14 : (0 <= j)) (PreH15 : (j <= i)) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (Spec source target 0 )
.

Definition solver_return_wit_3 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (store_string s_pre source )
  **  (store_string t_pre target )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec source target 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
|--
  “ (Spec source target 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
).

Definition solver_return_wit_3_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
|--
  “ (Spec source target 0 ) ”
.

Definition solver_return_wit_3_split_goal_spatial :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
|--
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
.

Definition solver_return_wit_4 :=
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (store_string s_pre source )
  **  (store_string t_pre target )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (Spec source target 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
) \/
(
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
|--
  “ (Spec source target 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
).

Definition solver_return_wit_4_split_goal_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
|--
  “ (Spec source target 1 ) ”
.

Definition solver_return_wit_4_split_goal_spatial :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strncmp_result source target n_pre retval )) (PreH3 : (n_pre = (Zlength (source)))) (PreH4 : (n_pre = (Zlength (target)))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 200000)) (PreH7 : ((Zlength (target)) = (Zlength (source)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH10 : (i = n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH12 : (valid_string source )) (PreH13 : (valid_string target )) (PreH14 : ((string_length (source)) = n_pre)) (PreH15 : ((string_length (target)) = n_pre)),
  (CharArray.full t_pre ((string_length (target)) + 1 ) (c_string (target)) )
  **  (CharArray.full s_pre ((string_length (source)) + 1 ) (c_string (source)) )
|--
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_1 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
.

Definition solver_partial_solve_wit_2_pure :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH8 : (i = n_pre)) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH10 : (valid_string source )) (PreH11 : (valid_string target )) (PreH12 : ((string_length (source)) = n_pre)) (PreH13 : ((string_length (target)) = n_pre)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string s_pre source )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (store_string t_pre target )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (valid_string source ) ”
  &&  “ (valid_string target ) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre < INT_MAX) ”
  &&  “ ((string_length (source)) < INT_MAX) ”
  &&  “ ((string_length (target)) < INT_MAX) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (n_pre = (Zlength (source)))) (PreH2 : (n_pre = (Zlength (target)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 200000)) (PreH5 : ((Zlength (target)) = (Zlength (source)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH8 : (i = n_pre)) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48))) (PreH10 : (valid_string source )) (PreH11 : (valid_string target )) (PreH12 : ((string_length (source)) = n_pre)) (PreH13 : ((string_length (target)) = n_pre)),
  (store_string s_pre source )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (store_string t_pre target )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (valid_string source ) ”
  &&  “ (valid_string target ) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre < INT_MAX) ”
  &&  “ ((string_length (source)) < INT_MAX) ”
  &&  “ ((string_length (target)) < INT_MAX) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (i = n_pre) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ (valid_string source ) ”
  &&  “ (valid_string target ) ”
  &&  “ ((string_length (source)) = n_pre) ”
  &&  “ ((string_length (target)) = n_pre) ”
  &&  (store_string s_pre source )
  **  (store_string t_pre target )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (n_pre: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (n_pre = (Zlength (source)))) (PreH3 : (n_pre = (Zlength (target)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 200000)) (PreH6 : ((Zlength (target)) = (Zlength (source)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Znth i source 0) = 49)) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48))) (PreH13 : (0 <= j)) (PreH14 : (j <= i)) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48))),
  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.full t_pre (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
|--
  “ (j < i) ”
  &&  “ (n_pre = (Zlength (source))) ”
  &&  “ (n_pre = (Zlength (target))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 200000) ”
  &&  “ ((Zlength (target)) = (Zlength (source))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> (((Znth k source 0) = 48) \/ ((Znth k source 0) = 49))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> (((Znth k_2 target 0) = 48) \/ ((Znth k_2 target 0) = 49))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i source 0) = 49) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 source 0) = 48)) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= i) ”
  &&  “ forall (k_4: Z), (((0 <= k_4) /\ (k_4 < j)) -> ((Znth k_4 target 0) = 48)) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre j 0 (n_pre + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) 200005 )
  **  (CharArray.undef_seg t_pre (n_pre + 1 ) 200005 )
.

Module Type VC_Correct.

Include string_Strategy_Correct.

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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
