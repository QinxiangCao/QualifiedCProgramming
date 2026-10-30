From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (old_pre0: Z) (old_okpre0: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> old_okpre0)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (old_pre0: Z) (old_okpre0: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> old_okpre0)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (old_okpre0: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> old_okpre0)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (old_okpre0: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> old_okpre0)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> 1)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ”
).

Definition solver_safety_wit_6_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values )) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values )) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (0) ((app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) 0) >= 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values )) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (1) ((app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) 0) < 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values )) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (0) ((app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_suf_terminal: Z) (old_oksuf_terminal: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH7 : (PrefixResidualState values pre_values okpre_values )) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> old_suf_terminal)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> old_oksuf_terminal)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_suf_terminal: Z) (old_oksuf_terminal: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH7 : (PrefixResidualState values pre_values okpre_values )) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> old_suf_terminal)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> old_oksuf_terminal)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_suf_terminal: Z) (old_oksuf_terminal: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH7 : (PrefixResidualState values pre_values okpre_values )) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> old_suf_terminal)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> old_oksuf_terminal)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_oksuf_terminal: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH7 : (PrefixResidualState values pre_values okpre_values )) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> old_oksuf_terminal)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_oksuf_terminal: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH7 : (PrefixResidualState values pre_values okpre_values )) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> old_oksuf_terminal)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_20 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_oksuf_terminal: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH7 : (PrefixResidualState values pre_values okpre_values )) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> old_oksuf_terminal)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : (PrefixResidualState values pre_values okpre_values )) (PreH12 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH14 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) )) ”
).

Definition solver_safety_wit_22_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_22_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) )) ”
.

Definition solver_safety_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_24 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_25 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH16 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH17 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH16 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH17 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (suf_leading)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH17 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH18 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_leading: (@list Z)) (new_suf_i: Z) (new_oksuf_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH16 : (new_oksuf_i = 0)) (PreH17 : ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)))) (PreH18 : ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH22 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_29 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_leading: (@list Z)) (new_suf_i: Z) (new_oksuf_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH16 : (new_oksuf_i = 1)) (PreH17 : ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)))) (PreH18 : ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH22 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_30 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre okpre_values 0) <> 0)) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values 0) = 0)) (PreH2 : ((Znth n_pre okpre_values 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_32 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre okpre_values 0) = 0)) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_33 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values 0) <> 0)) (PreH2 : ((Znth n_pre okpre_values 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_34 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_35 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ ((i + 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_37 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_38 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) )) ”
).

Definition solver_safety_wit_38_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_38_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((INT64_MIN) <= ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) )) ”
.

Definition solver_safety_wit_39 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((i - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_41 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_42 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "x" ) )) # Int64  |->_)
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_43 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_44 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |->_)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |->_)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) )) ”
).

Definition solver_safety_wit_44_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |->_)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_44_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |->_)
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((INT64_MIN) <= ((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) )) ”
.

Definition solver_safety_wit_45 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |-> ((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ))
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_46 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH2 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH3 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH4 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH16 : (PrefixResidualState values pre_values okpre_values )) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |-> ((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ))
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((i + 2 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_47 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH2 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH3 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH4 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH16 : (PrefixResidualState values pre_values okpre_values )) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |-> ((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ))
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_48 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) = (Znth ((i + 2 ) - 1 ) suf_values 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values okpre_values )) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  ((( &( "y" ) )) # Int64  |-> ((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ))
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "x" ) )) # Int64  |-> ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ))
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_49 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) <> (Znth ((i + 2 ) - 1 ) suf_values 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values okpre_values )) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_50 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) okpre_values 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_51 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) = 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_52 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) < 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_53 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) < 0)) (PreH2 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH3 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH4 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH16 : (PrefixResidualState values pre_values okpre_values )) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_54 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "okpre" ) )) # Ptr  |-> okpre_pre)
  **  ((( &( "oksuf" ) )) # Ptr  |-> oksuf_pre)
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (old_okpre0: Z) (old_pre0: Z),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> old_okpre0)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> 1)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = 1) ”
  &&  “ ((Zlength (okpre_values)) = 1) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < 1)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 1 pre_values )
  **  (Int64Array.seg_shape pre_pre 1 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 1 okpre_values )
  **  (CharArray.seg_shape okpre_pre 1 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))),
  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (((okpre_pre + (0 * sizeof(CHAR)))) # Char  |-> 1)
  **  (CharArray.missing_i_shape okpre_pre 0 0 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = 1) ”
  &&  “ ((Zlength (okpre_values)) = 1) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < 1)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.seg pre_pre 0 1 pre_values )
  **  (Int64Array.seg_shape pre_pre 1 (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 1 okpre_values )
  **  (CharArray.seg_shape okpre_pre 1 (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_entail_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 i pre_values_2 )
  **  (Int64Array.seg_shape pre_pre i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 i okpre_values_2 )
  **  (CharArray.seg_shape okpre_pre i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (old_okpre_i: Z) (old_pre_i: Z) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> old_pre_i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 i okpre_values )
  **  (((okpre_pre + (i * sizeof(CHAR)))) # Char  |-> old_okpre_i)
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
.

Definition solver_entail_wit_3_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_entail_wit_4_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))) 0) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (0) ((app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) okpre_values )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))) 0) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (0) ((app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) okpre_values )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_entail_wit_4_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) 0) >= 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH12 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (1) ((app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) okpre_values )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) 0) >= 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH12 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (1) ((app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) okpre_values )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_entail_wit_4_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) 0) < 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH12 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (0) ((app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) okpre_values )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) 0) < 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = i)) (PreH10 : ((Zlength (okpre_values_2)) = i)) (PreH11 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH12 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (CharArray.full okpre_pre (i + 1 ) (replace_Znth (i) (0) ((app (okpre_values_2) ((cons (old_okpre_i) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values_2) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) okpre_values )
  **  (CharArray.seg_shape okpre_pre (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_entail_wit_5 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 i pre_values_2 )
  **  (Int64Array.seg_shape pre_pre i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 i okpre_values_2 )
  **  (CharArray.seg_shape okpre_pre i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  EX (old_oksuf_terminal: Z) (old_suf_terminal: Z) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> old_suf_terminal)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> old_oksuf_terminal)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  TT && emp 
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= (Zlength (values)))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = i)) (PreH9 : ((Zlength (okpre_values_2)) = i)) (PreH10 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH11 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < i)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= (Zlength (values)))) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))
.

Definition solver_entail_wit_6 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH6 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH7 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> 1)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - n_pre )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - n_pre )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (n_pre + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - n_pre ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - n_pre ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 (n_pre + 1 ) )
  **  (Int64Array.seg suf_pre (n_pre + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 (n_pre + 1 ) )
  **  (CharArray.seg oksuf_pre (n_pre + 1 ) (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (suf_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH9 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH10 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))),
  (((suf_pre + ((n_pre + 1 ) * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape suf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
  **  (((oksuf_pre + ((n_pre + 1 ) * sizeof(CHAR)))) # Char  |-> 1)
  **  (CharArray.missing_i_shape oksuf_pre (n_pre + 1 ) 0 (n_pre + 2 ) )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - n_pre )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - n_pre )) ”
  &&  “ (PrefixResidualState values pre_values_2 okpre_values_2 ) ”
  &&  “ (SuffixResidualState values (n_pre + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - n_pre ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - n_pre ) - q ) )))) ”
  &&  (Int64Array.seg_shape suf_pre 0 (n_pre + 1 ) )
  **  (Int64Array.seg suf_pre (n_pre + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (n_pre + 1 ) )
  **  (CharArray.seg oksuf_pre (n_pre + 1 ) (n_pre + 2 ) oksuf_values )
).

Definition solver_entail_wit_7 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i >= 1)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH13 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH14 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH15 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_prefix: (@list Z)) (suf_prefix: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_prefix)) = (i + 1 )) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (suf_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i >= 1)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH13 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH14 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH15 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
|--
  EX (oksuf_prefix: (@list Z)) (suf_prefix: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_prefix)) = (i + 1 )) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values_2 okpre_values_2 ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
).

Definition solver_entail_wit_8 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix_2: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix_2)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH16 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.full suf_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values_2 0) )) (suf_prefix)) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix_2 )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (new_suf_i: Z) (oksuf_prefix: (@list Z)) (suf_leading: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (suf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix_2: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix_2)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH16 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.missing_i suf_pre i 0 (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values_2 0) )) (suf_prefix)) )
|--
  EX (suf_leading: (@list Z)),
  “ (((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ) = (Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i + 1 ) - (i + 1 ) ) suf_values_2 0) )) (suf_prefix)) 0)) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_prefix_2)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values_2 okpre_values_2 ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 ) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) )) ”
  &&  “ (((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ) <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.seg suf_pre 0 i suf_leading )
).

Definition solver_entail_wit_9_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_leading_2: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i_2: Z) (i: Z) (PreH1 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values_2 0) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (suf_leading_2)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH16 : (new_suf_i_2 = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ))) (PreH17 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i_2)) (PreH18 : (new_suf_i_2 <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH19 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH20 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (CharArray.full oksuf_pre (i + 1 ) (replace_Znth (i) (0) (oksuf_prefix)) )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading_2) ((cons (new_suf_i_2) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
|--
  (EX (new_oksuf_i: Z) (new_suf_i: Z) (oksuf_leading: (@list Z)) (suf_leading: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_leading)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (new_oksuf_i = 0) ”
  &&  “ ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i))) ”
  &&  “ ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1)) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values ))
  ||
  (EX (new_oksuf_i: Z) (new_suf_i: Z) (oksuf_leading: (@list Z)) (suf_leading: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_leading)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (new_oksuf_i = 1) ”
  &&  “ ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i))) ”
  &&  “ ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1)) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values ))
.

Definition solver_entail_wit_9_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_leading_2: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i_2: Z) (i: Z) (PreH1 : ((Znth (i - 0 ) (app (suf_leading_2) ((cons (new_suf_i_2) ((@nil Z))))) 0) >= 0)) (PreH2 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values_2 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (suf_leading_2)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH16 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH17 : (new_suf_i_2 = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ))) (PreH18 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i_2)) (PreH19 : (new_suf_i_2 <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH20 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH21 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (CharArray.full oksuf_pre (i + 1 ) (replace_Znth (i) (1) (oksuf_prefix)) )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading_2) ((cons (new_suf_i_2) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
|--
  (EX (new_oksuf_i: Z) (new_suf_i: Z) (oksuf_leading: (@list Z)) (suf_leading: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_leading)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (new_oksuf_i = 0) ”
  &&  “ ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i))) ”
  &&  “ ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1)) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values ))
  ||
  (EX (new_oksuf_i: Z) (new_suf_i: Z) (oksuf_leading: (@list Z)) (suf_leading: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_leading)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (new_oksuf_i = 1) ”
  &&  “ ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i))) ”
  &&  “ ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1)) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values ))
.

Definition solver_entail_wit_9_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_leading_2: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i_2: Z) (i: Z) (PreH1 : ((Znth (i - 0 ) (app (suf_leading_2) ((cons (new_suf_i_2) ((@nil Z))))) 0) < 0)) (PreH2 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values_2 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (suf_leading_2)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH16 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH17 : (new_suf_i_2 = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ))) (PreH18 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i_2)) (PreH19 : (new_suf_i_2 <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH20 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH21 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (CharArray.full oksuf_pre (i + 1 ) (replace_Znth (i) (0) (oksuf_prefix)) )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading_2) ((cons (new_suf_i_2) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
|--
  (EX (new_oksuf_i: Z) (new_suf_i: Z) (oksuf_leading: (@list Z)) (suf_leading: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_leading)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (new_oksuf_i = 0) ”
  &&  “ ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i))) ”
  &&  “ ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1)) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values ))
  ||
  (EX (new_oksuf_i: Z) (new_suf_i: Z) (oksuf_leading: (@list Z)) (suf_leading: (@list Z)) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_leading)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (new_oksuf_i = 1) ”
  &&  “ ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i))) ”
  &&  “ ((((Znth 0 oksuf_values 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1)) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values ))
.

Definition solver_entail_wit_10_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_leading: (@list Z)) (oksuf_leading: (@list Z)) (new_suf_i: Z) (new_oksuf_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH15 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ))) (PreH16 : (new_oksuf_i = 0)) (PreH17 : ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)))) (PreH18 : ((((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH21 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ ((i - 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values ((i - 1 ) + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1 ) ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - (i - 1 ) ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 ((i - 1 ) + 1 ) )
  **  (Int64Array.seg suf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 ((i - 1 ) + 1 ) )
  **  (CharArray.seg oksuf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (suf_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_leading: (@list Z)) (oksuf_leading: (@list Z)) (new_suf_i: Z) (new_oksuf_i: Z) (i: Z) (PreH1 : (new_suf_i <= INT64_MAX)) (PreH2 : (new_suf_i >= INT64_MIN)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_leading)) = i)) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH16 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH17 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ))) (PreH18 : (new_oksuf_i = 0)) (PreH19 : ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)))) (PreH20 : ((((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH21 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH22 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH24 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ ((i - 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ (PrefixResidualState values pre_values_2 okpre_values_2 ) ”
  &&  “ (SuffixResidualState values ((i - 1 ) + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1 ) ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - (i - 1 ) ) - q ) )))) ”
  &&  (Int64Array.seg_shape suf_pre 0 ((i - 1 ) + 1 ) )
  **  (Int64Array.seg suf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 ((i - 1 ) + 1 ) )
  **  (CharArray.seg oksuf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) oksuf_values )
).

Definition solver_entail_wit_10_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_leading: (@list Z)) (oksuf_leading: (@list Z)) (new_suf_i: Z) (new_oksuf_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_leading)) = i)) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH15 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ))) (PreH16 : (new_oksuf_i = 1)) (PreH17 : ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)))) (PreH18 : ((((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH19 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH20 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH21 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH22 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ ((i - 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values ((i - 1 ) + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1 ) ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - (i - 1 ) ) - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 ((i - 1 ) + 1 ) )
  **  (Int64Array.seg suf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 ((i - 1 ) + 1 ) )
  **  (CharArray.seg oksuf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (suf_pre: Z) (oksuf_pre: Z) (pre_values_2: (@list Z)) (okpre_values_2: (@list Z)) (suf_values_2: (@list Z)) (oksuf_values_2: (@list Z)) (suf_leading: (@list Z)) (oksuf_leading: (@list Z)) (new_suf_i: Z) (new_oksuf_i: Z) (i: Z) (PreH1 : (new_suf_i <= INT64_MAX)) (PreH2 : (new_suf_i >= INT64_MIN)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_leading)) = i)) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH16 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH17 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values_2 0) ))) (PreH18 : (new_oksuf_i = 1)) (PreH19 : ((new_oksuf_i = 1) -> (((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)))) (PreH20 : ((((Znth 0 oksuf_values_2 0) = 1) /\ (0 <= new_suf_i)) -> (new_oksuf_i = 1))) (PreH21 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH22 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH23 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH24 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg oksuf_pre 0 i oksuf_leading )
  **  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |-> new_oksuf_i)
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= (i - 1 )) ”
  &&  “ ((i - 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - (i - 1 ) )) ”
  &&  “ (PrefixResidualState values pre_values_2 okpre_values_2 ) ”
  &&  “ (SuffixResidualState values ((i - 1 ) + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - (i - 1 ) ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - (i - 1 ) ) - q ) )))) ”
  &&  (Int64Array.seg_shape suf_pre 0 ((i - 1 ) + 1 ) )
  **  (Int64Array.seg suf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 ((i - 1 ) + 1 ) )
  **  (CharArray.seg oksuf_pre ((i - 1 ) + 1 ) (n_pre + 2 ) oksuf_values )
).

Definition solver_entail_wit_11_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre okpre_values_2 0) = 0)) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH16 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values 1 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (suf_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre okpre_values_2 0) = 0)) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH15 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH16 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values_2 okpre_values_2 ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values_2 suf_values okpre_values_2 oksuf_values 1 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
).

Definition solver_entail_wit_11_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values_2 0) <> 0)) (PreH2 : ((Znth n_pre okpre_values_2 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH17 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values 1 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (suf_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values_2 0) <> 0)) (PreH2 : ((Znth n_pre okpre_values_2 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values_2)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values_2)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values_2 oksuf_values_2 )) (PreH16 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((((-1000000000) * k_4 ) <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= (1000000000 * k_4 ))))) (PreH17 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (Zlength (suf_values_2)))) -> ((((-1000000000) * ((n_pre - i ) - q_2 ) ) <= (Znth q_2 suf_values_2 0)) /\ ((Znth q_2 suf_values_2 0) <= (1000000000 * ((n_pre - i ) - q_2 ) ))))),
  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values_2)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values_2 okpre_values_2 ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values_2 suf_values okpre_values_2 oksuf_values 1 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
).

Definition solver_entail_wit_12_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) <> (Znth ((i + 2 ) - 1 ) suf_values_2 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH18 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH19 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1 ) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) <> (Znth ((i + 2 ) - 1 ) suf_values_2 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH18 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH19 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_12_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) <> (Znth ((i + 2 ) - 1 ) suf_values_2 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH18 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH19 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) )
.

Definition solver_entail_wit_12_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) okpre_values_2 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH15 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values_2 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1 ) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) okpre_values_2 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH15 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_12_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) okpre_values_2 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH13 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH14 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH15 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) )
.

Definition solver_entail_wit_12_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) = 0)) (PreH2 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH15 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH16 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1 ) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) = 0)) (PreH2 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH15 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH16 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_12_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) = 0)) (PreH2 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH15 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH16 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) )
.

Definition solver_entail_wit_12_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) < 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH16 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH17 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1 ) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) < 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH16 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH17 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_12_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) < 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH16 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH17 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) )
.

Definition solver_entail_wit_12_5 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) < 0)) (PreH2 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) >= 0)) (PreH3 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH4 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH16 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH17 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH18 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values_2 )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values_2 )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values_2 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  EX (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)),
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values (i + 1 ) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) < 0)) (PreH2 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) >= 0)) (PreH3 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH4 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH16 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH17 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH18 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  TT && emp 
|--
  “ (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_12_5_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (oksuf_values_2: (@list Z)) (suf_values_2: (@list Z)) (okpre_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) ) < 0)) (PreH2 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values_2 0) ) >= 0)) (PreH3 : ((Znth ((i + 2 ) - 1 ) oksuf_values_2 0) <> 0)) (PreH4 : ((Znth (i - 1 ) okpre_values_2 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (okpre_values_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (suf_values_2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (oksuf_values_2)) = (n_pre + 1 ))) (PreH16 : (PrefixResidualState values pre_values_2 okpre_values_2 )) (PreH17 : (SuffixResidualState values 1 suf_values_2 oksuf_values_2 )) (PreH18 : (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i )) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values_2 0)) /\ ((Znth q suf_values_2 0) <= (1000000000 * (n_pre - q ) ))))),
  (CheckedSwapPrefix values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 (i + 1 ) )
.

Definition solver_return_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ (Spec values 0 ) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ (Spec values 0 ) ”
  &&  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_return_wit_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ (Spec values 0 ) ”
.

Definition solver_return_wit_1_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_return_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) = (Znth ((i + 2 ) - 1 ) suf_values 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values okpre_values )) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (Spec values 1 ) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) = (Znth ((i + 2 ) - 1 ) suf_values 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values okpre_values )) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (Spec values 1 ) ”
  &&  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_return_wit_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) = (Znth ((i + 2 ) - 1 ) suf_values 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values okpre_values )) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (Spec values 1 ) ”
.

Definition solver_return_wit_2_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) = (Znth ((i + 2 ) - 1 ) suf_values 0))) (PreH2 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH3 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH4 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH5 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH16 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH17 : (PrefixResidualState values pre_values okpre_values )) (PreH18 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH19 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_return_wit_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values 0) = 0)) (PreH2 : ((Znth n_pre okpre_values 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (Spec values 1 ) ”
  &&  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values 0) = 0)) (PreH2 : ((Znth n_pre okpre_values 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (Spec values 1 ) ”
  &&  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
).

Definition solver_return_wit_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values 0) = 0)) (PreH2 : ((Znth n_pre okpre_values 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (Spec values 1 ) ”
.

Definition solver_return_wit_3_split_goal_spatial :=
forall (values: (@list Z)) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre pre_values 0) = 0)) (PreH2 : ((Znth n_pre okpre_values 0) <> 0)) (PreH3 : (i < 1)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.full_shape okpre_pre (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> old_pre_i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 i okpre_values )
  **  (((okpre_pre + (i * sizeof(CHAR)))) # Char  |-> old_okpre_i)
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i (cons (0) (values)) 0))
  **  (Int64Array.missing_i a_pre i 0 (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> old_pre_i)
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.seg okpre_pre 0 i okpre_values )
  **  (((okpre_pre + (i * sizeof(CHAR)))) # Char  |-> old_okpre_i)
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((pre_pre + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre (i - 1 ) 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre i 0 (i + 1 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = i)) (PreH8 : ((Zlength (okpre_values)) = i)) (PreH9 : (PrefixResidualState values pre_values okpre_values )) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((okpre_pre + ((i - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0))
  **  (CharArray.missing_i okpre_pre (i - 1 ) 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values )) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = i)) (PreH9 : ((Zlength (okpre_values)) = i)) (PreH10 : (PrefixResidualState values pre_values okpre_values )) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) = 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((okpre_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i okpre_pre i 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) 0) >= 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values )) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) 0) >= 0) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((okpre_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i okpre_pre i 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (old_pre_i: Z) (old_okpre_i: Z) (i: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) 0) < 0)) (PreH2 : ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = i)) (PreH10 : ((Zlength (okpre_values)) = i)) (PreH11 : (PrefixResidualState values pre_values okpre_values )) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))),
  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (CharArray.seg okpre_pre 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
|--
  “ ((Znth i (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) 0) < 0) ”
  &&  “ ((Znth ((i - 1 ) - 0 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = i) ”
  &&  “ ((Zlength (okpre_values)) = i) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < i)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  (((okpre_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i okpre_pre i 0 (i + 1 ) (app (okpre_values) ((cons (old_okpre_i) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (i + 1 ) (replace_Znth (i) (((Znth i (cons (0) (values)) 0) - (Znth ((i - 1 ) - 0 ) (app (pre_values) ((cons (old_pre_i) ((@nil Z))))) 0) )) ((app (pre_values) ((cons (old_pre_i) ((@nil Z))))))) )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.missing_i_shape pre_pre i i (n_pre + 1 ) )
  **  (Int64Array.full_shape suf_pre (n_pre + 2 ) )
  **  (CharArray.missing_i_shape okpre_pre i i (n_pre + 1 ) )
  **  (CharArray.full_shape oksuf_pre (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_prefix)) = (i + 1 )) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i (cons (0) (values)) 0))
  **  (Int64Array.missing_i a_pre i 0 (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
.

Definition solver_partial_solve_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_prefix)) = (i + 1 )) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((suf_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0))
  **  (Int64Array.missing_i suf_pre (i + 1 ) (i + 1 ) (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
.

Definition solver_partial_solve_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_prefix: (@list Z)) (oksuf_prefix: (@list Z)) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_prefix)) = (i + 1 ))) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) suf_prefix )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_prefix)) = (i + 1 )) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((suf_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i suf_pre i 0 (i + 1 ) suf_prefix )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
.

Definition solver_partial_solve_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH10 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (suf_leading)) = i)) (PreH12 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH16 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH17 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((oksuf_pre + ((i + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0))
  **  (CharArray.missing_i oksuf_pre (i + 1 ) (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre 0 i suf_leading )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> new_suf_i)
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
.

Definition solver_partial_solve_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (suf_leading)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH17 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH18 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
|--
  “ ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) 0))
  **  (Int64Array.missing_i suf_pre i 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
.

Definition solver_partial_solve_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (suf_leading)) = i)) (PreH13 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH16 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH17 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH18 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
|--
  “ ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) = 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i oksuf_pre i 0 (i + 1 ) oksuf_prefix )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
.

Definition solver_partial_solve_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : ((Znth (i - 0 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) 0) >= 0)) (PreH2 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH17 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH18 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH19 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
|--
  “ ((Znth (i - 0 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) 0) >= 0) ”
  &&  “ ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i oksuf_pre i 0 (i + 1 ) oksuf_prefix )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
.

Definition solver_partial_solve_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (pre_values: (@list Z)) (okpre_values: (@list Z)) (suf_values: (@list Z)) (oksuf_values: (@list Z)) (suf_leading: (@list Z)) (oksuf_prefix: (@list Z)) (new_suf_i: Z) (i: Z) (PreH1 : ((Znth (i - 0 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) 0) < 0)) (PreH2 : ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : ((Zlength (suf_leading)) = i)) (PreH14 : ((Zlength (oksuf_prefix)) = (i + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH17 : (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) ))) (PreH18 : (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i)) (PreH19 : (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) ))) (PreH20 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH21 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg oksuf_pre 0 (i + 1 ) oksuf_prefix )
|--
  “ ((Znth (i - 0 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) 0) < 0) ”
  &&  “ ((Znth ((i + 1 ) - (i + 1 ) ) oksuf_values 0) <> 0) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (suf_leading)) = i) ”
  &&  “ ((Zlength (oksuf_prefix)) = (i + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ (new_suf_i = ((Znth (i - 1 ) values 0) - (Znth 0 suf_values 0) )) ”
  &&  “ (((-1000000000) * ((n_pre - i ) + 1 ) ) <= new_suf_i) ”
  &&  “ (new_suf_i <= (1000000000 * ((n_pre - i ) + 1 ) )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((oksuf_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i oksuf_pre i 0 (i + 1 ) oksuf_prefix )
  **  (Int64Array.seg suf_pre 0 (i + 1 ) (app (suf_leading) ((cons (new_suf_i) ((@nil Z))))) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
.

Definition solver_partial_solve_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i < 1)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH11 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH15 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ (i < 1) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((okpre_pre + (n_pre * sizeof(CHAR)))) # Char  |-> (Znth n_pre okpre_values 0))
  **  (CharArray.missing_i okpre_pre n_pre 0 (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
.

Definition solver_partial_solve_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth n_pre okpre_values 0) <> 0)) (PreH2 : (i < 1)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = ((n_pre + 1 ) - i ))) (PreH12 : ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values (i + 1 ) suf_values oksuf_values )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) ))))),
  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
|--
  “ ((Znth n_pre okpre_values 0) <> 0) ”
  &&  “ (i < 1) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ ((Zlength (oksuf_values)) = ((n_pre + 1 ) - i )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values (i + 1 ) suf_values oksuf_values ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < (Zlength (suf_values)))) -> ((((-1000000000) * ((n_pre - i ) - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * ((n_pre - i ) - q ) )))) ”
  &&  (((pre_pre + (n_pre * sizeof(INT64)))) # Int64  |-> (Znth n_pre pre_values 0))
  **  (Int64Array.missing_i pre_pre n_pre 0 (n_pre + 1 ) pre_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.seg_shape suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 (i + 1 ) )
  **  (CharArray.seg oksuf_pre (i + 1 ) (n_pre + 2 ) oksuf_values )
.

Definition solver_partial_solve_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH12 : (PrefixResidualState values pre_values okpre_values )) (PreH13 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH14 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH16 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (((okpre_pre + ((i - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (i - 1 ) okpre_values 0))
  **  (CharArray.missing_i okpre_pre (i - 1 ) 0 (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
.

Definition solver_partial_solve_wit_20 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH13 : (PrefixResidualState values pre_values okpre_values )) (PreH14 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH15 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH17 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
|--
  “ ((Znth (i - 1 ) okpre_values 0) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (((oksuf_pre + ((i + 2 ) * sizeof(CHAR)))) # Char  |-> (Znth ((i + 2 ) - 1 ) oksuf_values 0))
  **  (CharArray.missing_i oksuf_pre (i + 2 ) 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
.

Definition solver_partial_solve_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0) ”
  &&  “ ((Znth (i - 1 ) okpre_values 0) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (((a_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i + 1 ) (cons (0) (values)) 0))
  **  (Int64Array.missing_i a_pre (i + 1 ) 0 (n_pre + 1 ) (cons (0) (values)) )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
.

Definition solver_partial_solve_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH2 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH11 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH14 : (PrefixResidualState values pre_values okpre_values )) (PreH15 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH16 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH18 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0) ”
  &&  “ ((Znth (i - 1 ) okpre_values 0) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (((pre_pre + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i - 1 ) pre_values 0))
  **  (Int64Array.missing_i pre_pre (i - 1 ) 0 (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
.

Definition solver_partial_solve_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH2 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH3 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : (1 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH12 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH15 : (PrefixResidualState values pre_values okpre_values )) (PreH16 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH17 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH19 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0) ”
  &&  “ ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0) ”
  &&  “ ((Znth (i - 1 ) okpre_values 0) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i (cons (0) (values)) 0))
  **  (Int64Array.missing_i a_pre i 0 (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
.

Definition solver_partial_solve_wit_24 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (pre_pre: Z) (suf_pre: Z) (okpre_pre: Z) (oksuf_pre: Z) (oksuf_values: (@list Z)) (suf_values: (@list Z)) (okpre_values: (@list Z)) (pre_values: (@list Z)) (i: Z) (PreH1 : (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0)) (PreH2 : (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0)) (PreH3 : ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0)) (PreH4 : ((Znth (i - 1 ) okpre_values 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (n_pre = (Zlength (values)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH13 : ((Zlength (okpre_values)) = (n_pre + 1 ))) (PreH14 : ((Zlength (suf_values)) = (n_pre + 1 ))) (PreH15 : ((Zlength (oksuf_values)) = (n_pre + 1 ))) (PreH16 : (PrefixResidualState values pre_values okpre_values )) (PreH17 : (SuffixResidualState values 1 suf_values oksuf_values )) (PreH18 : (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i )) (PreH19 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 ))))) (PreH20 : forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) ))))),
  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (Int64Array.seg suf_pre 1 (n_pre + 2 ) suf_values )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
|--
  “ (((Znth i (cons (0) (values)) 0) - ((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) ) >= 0) ”
  &&  “ (((Znth (i + 1 ) (cons (0) (values)) 0) - (Znth (i - 1 ) pre_values 0) ) >= 0) ”
  &&  “ ((Znth ((i + 2 ) - 1 ) oksuf_values 0) <> 0) ”
  &&  “ ((Znth (i - 1 ) okpre_values 0) <> 0) ”
  &&  “ (i < n_pre) ”
  &&  “ (2 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (okpre_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (suf_values)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (oksuf_values)) = (n_pre + 1 )) ”
  &&  “ (PrefixResidualState values pre_values okpre_values ) ”
  &&  “ (SuffixResidualState values 1 suf_values oksuf_values ) ”
  &&  “ (CheckedSwapPrefix values pre_values suf_values okpre_values oksuf_values i ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((((-1000000000) * k_2 ) <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= (1000000000 * k_2 )))) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q <= n_pre)) -> ((((-1000000000) * (n_pre - q ) ) <= (Znth q suf_values 0)) /\ ((Znth q suf_values 0) <= (1000000000 * (n_pre - q ) )))) ”
  &&  (((suf_pre + ((i + 2 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i + 2 ) - 1 ) suf_values 0))
  **  (Int64Array.missing_i suf_pre (i + 2 ) 1 (n_pre + 2 ) suf_values )
  **  (Int64Array.full a_pre (n_pre + 1 ) (cons (0) (values)) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.seg oksuf_pre 1 (n_pre + 2 ) oksuf_values )
  **  (CharArray.full okpre_pre (n_pre + 1 ) okpre_values )
  **  (Int64Array.seg_shape suf_pre 0 1 )
  **  (CharArray.seg_shape oksuf_pre 0 1 )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Axiom proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Axiom proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
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
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.

End VC_Correct.
