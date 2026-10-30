From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.
Local Open Scope sac.

(*----- Function conflicts -----*)

Definition conflicts_safety_wit_1 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH2 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH4 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : (0 <= left_override_pre)) (PreH16 : (left_override_pre <= 90)) (PreH17 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH18 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_2 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (i_pre > 0)) (PreH2 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH5 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : (0 <= left_override_pre)) (PreH17 : (left_override_pre <= 90)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((i_pre - 1 ) * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre - 1 ) * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_3 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (i_pre > 0)) (PreH2 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH5 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : (0 <= left_override_pre)) (PreH17 : (left_override_pre <= 90)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((i_pre - 1 ) * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre - 1 ) * m_pre )) ”
.

Definition conflicts_safety_wit_4 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (i_pre > 0)) (PreH2 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH5 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : (0 <= left_override_pre)) (PreH17 : (left_override_pre <= 90)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre - 1 )) ”
.

Definition conflicts_safety_wit_5 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (i_pre > 0)) (PreH2 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH5 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : (0 <= left_override_pre)) (PreH17 : (left_override_pre <= 90)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_6 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_7 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
.

Definition conflicts_safety_wit_8 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (i_pre <= 0)) (PreH2 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH5 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : (0 <= left_override_pre)) (PreH17 : (left_override_pre <= 90)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
.

Definition conflicts_safety_wit_9 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (i_pre <= 0)) (PreH2 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH5 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : (0 <= left_override_pre)) (PreH17 : (left_override_pre <= 90)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_10 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_11 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((i_pre + 1 ) * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre + 1 ) * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_12 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre + 1 ) * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre + 1 ) * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_13 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((i_pre + 1 ) * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre + 1 ) * m_pre )) ”
.

Definition conflicts_safety_wit_14 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre + 1 ) * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre + 1 ) * m_pre )) ”
.

Definition conflicts_safety_wit_15 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
.

Definition conflicts_safety_wit_16 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
.

Definition conflicts_safety_wit_17 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_18 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_19 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_20 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_21 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((j_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + 1 )) ”
.

Definition conflicts_safety_wit_22 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((j_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + 1 )) ”
.

Definition conflicts_safety_wit_23 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) >= n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + 1 )) ”
.

Definition conflicts_safety_wit_24 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) >= n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((j_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + 1 )) ”
.

Definition conflicts_safety_wit_25 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) >= n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_26 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) >= n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_27 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_28 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_29 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) + 1 )) ”
.

Definition conflicts_safety_wit_30 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((i_pre * m_pre ) + j_pre ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) + 1 )) ”
.

Definition conflicts_safety_wit_31 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) + 1 )) ”
.

Definition conflicts_safety_wit_32 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) + 1 )) ”
.

Definition conflicts_safety_wit_33 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_34 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_35 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_36 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_37 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_38 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_39 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_40 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_41 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_42 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_43 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_44 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_45 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_46 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_47 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_48 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_49 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) >= m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_50 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) >= m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_51 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) >= m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_52 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) >= m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_53 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_54 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_55 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_56 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_57 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_58 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_59 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_60 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_61 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_62 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_63 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_64 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_65 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_66 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_67 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_68 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_69 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_70 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_71 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_72 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_73 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_74 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_75 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_76 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_77 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_78 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_79 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_80 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_81 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_82 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_83 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_84 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_85 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((((i_pre * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre * m_pre ) + j_pre ) - 1 )) ”
.

Definition conflicts_safety_wit_86 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (((i_pre * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre * m_pre ) + j_pre )) ”
.

Definition conflicts_safety_wit_87 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ ((i_pre * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre * m_pre )) ”
.

Definition conflicts_safety_wit_88 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_89 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_90 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_91 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_92 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_93 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_94 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_95 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_96 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_97 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_98 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_99 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_100 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_101 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_102 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_103 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  ((( &( "left" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_104 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "left" ) )) # Char  |-> (signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_105 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_106 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_107 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_108 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_109 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_110 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_111 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_112 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition conflicts_safety_wit_113 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_114 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_115 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_116 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_117 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_118 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_119 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_120 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_121 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_122 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_123 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_124 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_125 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_126 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_127 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_128 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_129 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_130 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_131 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_132 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_133 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_134 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_135 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_safety_wit_136 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition conflicts_entail_wit_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (65 <= c_pre)) (PreH10 : (c_pre <= 90)) (PreH11 : (0 <= left_override_pre)) (PreH12 : (left_override_pre <= 90)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (65 <= c_pre)) (PreH10 : (c_pre <= 90)) (PreH11 : (0 <= left_override_pre)) (PreH12 : (left_override_pre <= 90)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition conflicts_entail_wit_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (65 <= c_pre)) (PreH10 : (c_pre <= 90)) (PreH11 : (0 <= left_override_pre)) (PreH12 : (left_override_pre <= 90)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )),
  ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))
.

Definition conflicts_entail_wit_1_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (65 <= c_pre)) (PreH10 : (c_pre <= 90)) (PreH11 : (0 <= left_override_pre)) (PreH12 : (left_override_pre <= 90)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )),
  (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))
.

Definition conflicts_entail_wit_1_split_goal_3 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (65 <= c_pre)) (PreH10 : (c_pre <= 90)) (PreH11 : (0 <= left_override_pre)) (PreH12 : (left_override_pre <= 90)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )),
  (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))
.

Definition conflicts_entail_wit_1_split_goal_4 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (65 <= c_pre)) (PreH10 : (c_pre <= 90)) (PreH11 : (0 <= left_override_pre)) (PreH12 : (left_override_pre <= 90)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )),
  ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))
.

Definition conflicts_return_wit_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_2 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_2_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_3 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_3_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_4 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_4_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_5 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_5_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_6 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_6_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_7 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_7_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_8 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_8_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_9 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_9_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_10 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_10_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_11 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_11_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_12 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_12_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_13 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_13_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_14 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_14_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_15 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_15_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_16 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )) ”
  &&  emp
).

Definition conflicts_return_wit_16_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) <> c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ))
.

Definition conflicts_return_wit_17 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_17_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_18 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_18_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_19 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_19_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_20 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_20_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_21 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_21_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_22 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_22_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_23 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_23_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_24 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )) ”
  &&  emp
).

Definition conflicts_return_wit_24_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre <> c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  ~((NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ))
.

Definition conflicts_return_wit_25 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_25_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_26 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_26_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_27 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_27_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_28 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_28_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_29 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_29_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_30 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_30_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_31 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_31_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_32 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_32_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_33 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_33_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_34 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_34_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_35 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_35_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_36 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_36_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_37 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_37_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_38 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_38_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_39 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_39_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_40 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_40_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((j_pre + 1 ) >= m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_41 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_41_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_42 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_42_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_43 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_43_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_44 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_44_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((i_pre + 1 ) >= n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_45 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_45_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_46 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_46_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : (i_pre <= 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_47 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_47_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = c_pre)) (PreH2 : (left_override_pre <> 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre c_pre )
.

Definition conflicts_return_wit_48 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 ) ”
  &&  emp
).

Definition conflicts_return_wit_48_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((signed_last_nbits ((Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0)) (8)) = c_pre)) (PreH2 : (left_override_pre = 0)) (PreH3 : (j_pre > 0)) (PreH4 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH5 : ((j_pre + 1 ) < m_pre)) (PreH6 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : ((i_pre + 1 ) < n_pre)) (PreH8 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH9 : (i_pre > 0)) (PreH10 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH12 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH13 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 100)) (PreH18 : (0 <= i_pre)) (PreH19 : (i_pre < n_pre)) (PreH20 : (0 <= j_pre)) (PreH21 : (j_pre < m_pre)) (PreH22 : (65 <= c_pre)) (PreH23 : (c_pre <= 90)) (PreH24 : (0 <= left_override_pre)) (PreH25 : (left_override_pre <= 90)) (PreH26 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH27 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre 0 )
.

Definition conflicts_return_wit_49 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_49_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )
.

Definition conflicts_return_wit_50 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_50_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((i_pre + 1 ) >= n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )
.

Definition conflicts_return_wit_51 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_51_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )
.

Definition conflicts_return_wit_52 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_52_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) = c_pre)) (PreH2 : ((j_pre + 1 ) < m_pre)) (PreH3 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : ((i_pre + 1 ) < n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )
.

Definition conflicts_return_wit_53 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_53_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )
.

Definition conflicts_return_wit_54 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_54_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : ((i_pre + 1 ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )
.

Definition conflicts_return_wit_55 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre ) ”
  &&  emp
).

Definition conflicts_return_wit_55_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  (NeighborConflict flat n_pre m_pre i_pre j_pre c_pre left_override_pre )
.

Definition conflicts_partial_solve_wit_1 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (i_pre > 0)) (PreH2 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH3 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH5 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : (0 <= left_override_pre)) (PreH17 : (left_override_pre <= 90)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre - 1 ) * m_pre ) + j_pre ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre - 1 ) * m_pre ) + j_pre ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_2 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre + 1 ) * m_pre ) + j_pre ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre + 1 ) * m_pre ) + j_pre ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_3 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((i_pre + 1 ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH4 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH6 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : (0 <= i_pre)) (PreH12 : (i_pre < n_pre)) (PreH13 : (0 <= j_pre)) (PreH14 : (j_pre < m_pre)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : (0 <= left_override_pre)) (PreH18 : (left_override_pre <= 90)) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre + 1 ) * m_pre ) + j_pre ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre + 1 ) * m_pre ) + j_pre ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_4 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : (i_pre > 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) + 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_5 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH3 : ((i_pre + 1 ) < n_pre)) (PreH4 : (i_pre <= 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) + 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_6 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH5 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH7 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 100)) (PreH12 : (0 <= i_pre)) (PreH13 : (i_pre < n_pre)) (PreH14 : (0 <= j_pre)) (PreH15 : (j_pre < m_pre)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : (0 <= left_override_pre)) (PreH19 : (left_override_pre <= 90)) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((i_pre + 1 ) >= n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) + 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_7 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : ((j_pre + 1 ) < m_pre)) (PreH2 : ((i_pre + 1 ) >= n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH6 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH8 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i_pre)) (PreH14 : (i_pre < n_pre)) (PreH15 : (0 <= j_pre)) (PreH16 : (j_pre < m_pre)) (PreH17 : (65 <= c_pre)) (PreH18 : (c_pre <= 90)) (PreH19 : (0 <= left_override_pre)) (PreH20 : (left_override_pre <= 90)) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((i_pre + 1 ) >= n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) + 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) + 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_8 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((j_pre + 1 ) >= m_pre) ”
  &&  “ ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_9 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH5 : ((i_pre + 1 ) < n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((j_pre + 1 ) >= m_pre) ”
  &&  “ ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_10 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : (i_pre <= 0)) (PreH6 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH7 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH9 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : (0 <= i_pre)) (PreH15 : (i_pre < n_pre)) (PreH16 : (0 <= j_pre)) (PreH17 : (j_pre < m_pre)) (PreH18 : (65 <= c_pre)) (PreH19 : (c_pre <= 90)) (PreH20 : (0 <= left_override_pre)) (PreH21 : (left_override_pre <= 90)) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((j_pre + 1 ) >= m_pre) ”
  &&  “ ((i_pre + 1 ) >= n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_11 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((j_pre + 1 ) >= m_pre)) (PreH4 : ((i_pre + 1 ) >= n_pre)) (PreH5 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : (i_pre > 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((j_pre + 1 ) >= m_pre) ”
  &&  “ ((i_pre + 1 ) >= n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_12 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH7 : (i_pre > 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre) ”
  &&  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((i_pre + 1 ) >= n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_13 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((i_pre + 1 ) >= n_pre)) (PreH6 : (i_pre <= 0)) (PreH7 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH8 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH10 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 100)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 100)) (PreH15 : (0 <= i_pre)) (PreH16 : (i_pre < n_pre)) (PreH17 : (0 <= j_pre)) (PreH18 : (j_pre < m_pre)) (PreH19 : (65 <= c_pre)) (PreH20 : (c_pre <= 90)) (PreH21 : (0 <= left_override_pre)) (PreH22 : (left_override_pre <= 90)) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre) ”
  &&  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((i_pre + 1 ) >= n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_14 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : (i_pre <= 0)) (PreH8 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH9 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH11 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 100)) (PreH16 : (0 <= i_pre)) (PreH17 : (i_pre < n_pre)) (PreH18 : (0 <= j_pre)) (PreH19 : (j_pre < m_pre)) (PreH20 : (65 <= c_pre)) (PreH21 : (c_pre <= 90)) (PreH22 : (0 <= left_override_pre)) (PreH23 : (left_override_pre <= 90)) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre) ”
  &&  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition conflicts_partial_solve_wit_15 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (c_pre: Z) (left_override_pre: Z) (PreH1 : (left_override_pre = 0)) (PreH2 : (j_pre > 0)) (PreH3 : ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre)) (PreH4 : ((j_pre + 1 ) < m_pre)) (PreH5 : ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH6 : ((i_pre + 1 ) < n_pre)) (PreH7 : ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre)) (PreH8 : (i_pre > 0)) (PreH9 : ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH10 : (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))) (PreH11 : (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre ))))) (PreH12 : ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 100)) (PreH17 : (0 <= i_pre)) (PreH18 : (i_pre < n_pre)) (PreH19 : (0 <= j_pre)) (PreH20 : (j_pre < m_pre)) (PreH21 : (65 <= c_pre)) (PreH22 : (c_pre <= 90)) (PreH23 : (0 <= left_override_pre)) (PreH24 : (left_override_pre <= 90)) (PreH25 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH26 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (left_override_pre = 0) ”
  &&  “ (j_pre > 0) ”
  &&  “ ((Znth (((i_pre * m_pre ) + j_pre ) + 1 ) flat 0) <> c_pre) ”
  &&  “ ((j_pre + 1 ) < m_pre) ”
  &&  “ ((Znth (((i_pre + 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ ((i_pre + 1 ) < n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + j_pre ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ ((i_pre > 0) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre + 1 ) < n_pre) -> ((0 <= (((i_pre + 1 ) * m_pre ) + j_pre )) /\ ((((i_pre + 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre + 1 ) < m_pre) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + 1 )) /\ ((((i_pre * m_pre ) + j_pre ) + 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((j_pre > 0) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (((g_pre + ((((i_pre * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

(*----- Function cell_colour -----*)

Definition cell_colour_safety_wit_1 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (0 <= left_override_pre)) (PreH10 : (left_override_pre <= 90)) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid flat )),
  ((( &( "c" ) )) # Char  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (65 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 65) ”
.

Definition cell_colour_safety_wit_2 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (0 <= left_override_pre)) (PreH10 : (left_override_pre <= 90)) (PreH11 : (65 <= c)) (PreH12 : (c <= 91)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )) (PreH15 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (90 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 90) ”
.

Definition cell_colour_safety_wit_3 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre )) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  ((( &( "c" ) )) # Char  |-> c)
|--
  “ False ”
.

Definition cell_colour_safety_wit_4 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : ~((NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre ))) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  ((( &( "c" ) )) # Char  |-> c)
|--
  “ False ”
.

Definition cell_colour_safety_wit_5 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (PreH1 : (c > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (0 <= left_override_pre)) (PreH11 : (left_override_pre <= 90)) (PreH12 : (65 <= c)) (PreH13 : (c <= 91)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )) (PreH16 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (90 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 90) ”
.

Definition cell_colour_safety_wit_6 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre )) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  ((( &( "c" ) )) # Char  |-> c)
|--
  “ ((c + 1 ) <= 127) ”
  &&  “ ((-128) <= (c + 1 )) ”
.

Definition cell_colour_entail_wit_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (0 <= left_override_pre)) (PreH10 : (left_override_pre <= 90)) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ (65 <= 65) ”
  &&  “ (65 <= 91) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre 65 ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (0 <= left_override_pre)) (PreH10 : (left_override_pre <= 90)) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre 65 ) ”
  &&  emp
).

Definition cell_colour_entail_wit_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (0 <= left_override_pre)) (PreH10 : (left_override_pre <= 90)) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid flat )),
  (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre 65 )
.

Definition cell_colour_entail_wit_2 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre )) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ (65 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 91) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre (c + 1 ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre )) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  TT && emp 
|--
  “ (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre (c + 1 ) ) ”
  &&  emp
).

Definition cell_colour_entail_wit_2_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre )) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre (c + 1 ) )
.

Definition cell_colour_return_wit_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (PreH1 : (c > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (0 <= left_override_pre)) (PreH11 : (left_override_pre <= 90)) (PreH12 : (65 <= c)) (PreH13 : (c <= 91)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )) (PreH16 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (LeastLegalColor flat n_pre m_pre i_pre j_pre left_override_pre 90 ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (PreH1 : (c > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (0 <= left_override_pre)) (PreH11 : (left_override_pre <= 90)) (PreH12 : (65 <= c)) (PreH13 : (c <= 91)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )) (PreH16 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  TT && emp 
|--
  “ (LeastLegalColor flat n_pre m_pre i_pre j_pre left_override_pre 90 ) ”
  &&  emp
).

Definition cell_colour_return_wit_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (PreH1 : (c > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (0 <= left_override_pre)) (PreH11 : (left_override_pre <= 90)) (PreH12 : (65 <= c)) (PreH13 : (c <= 91)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )) (PreH16 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (LeastLegalColor flat n_pre m_pre i_pre j_pre left_override_pre 90 )
.

Definition cell_colour_return_wit_2 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ~((NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre ))) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (LeastLegalColor flat n_pre m_pre i_pre j_pre left_override_pre c ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ~((NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre ))) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  TT && emp 
|--
  “ (LeastLegalColor flat n_pre m_pre i_pre j_pre left_override_pre c ) ”
  &&  emp
).

Definition cell_colour_return_wit_2_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ~((NeighborConflict flat n_pre m_pre i_pre j_pre c left_override_pre ))) (PreH4 : (CanonicalGrid flat )) (PreH5 : (c <= 90)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (0 <= left_override_pre)) (PreH15 : (left_override_pre <= 90)) (PreH16 : (65 <= c)) (PreH17 : (c <= 91)) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (LeastLegalColor flat n_pre m_pre i_pre j_pre left_override_pre c )
.

Definition cell_colour_partial_solve_wit_1_pure :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (PreH1 : (c <= 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (0 <= left_override_pre)) (PreH11 : (left_override_pre <= 90)) (PreH12 : (65 <= c)) (PreH13 : (c <= 91)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )) (PreH16 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "left_override" ) )) # Char  |-> left_override_pre)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
.

Definition cell_colour_partial_solve_wit_1_aux :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (left_override_pre: Z) (c: Z) (PreH1 : (c <= 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (0 <= left_override_pre)) (PreH11 : (left_override_pre <= 90)) (PreH12 : (65 <= c)) (PreH13 : (c <= 91)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )) (PreH16 : (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (0 <= left_override_pre) ”
  &&  “ (left_override_pre <= 90) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 91) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (NoConflictBelow flat n_pre m_pre i_pre j_pre left_override_pre c ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
.

Definition cell_colour_partial_solve_wit_1 := cell_colour_partial_solve_wit_1_pure -> cell_colour_partial_solve_wit_1_aux.

(*----- Function can_place -----*)

Definition can_place_safety_wit_1 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (1 <= s_pre)) (PreH10 : (s_pre <= 101)) (PreH11 : (65 <= c_pre)) (PreH12 : (c_pre <= 90)) (PreH13 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid flat )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + s_pre )) ”
.

Definition can_place_safety_wit_2 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((i_pre + s_pre ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + s_pre )) ”
.

Definition can_place_safety_wit_3 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((i_pre + s_pre ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_4 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((j_pre + s_pre ) > m_pre)) (PreH2 : ((i_pre + s_pre ) <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid flat )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_5 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (1 <= s_pre)) (PreH10 : (s_pre <= 101)) (PreH11 : (65 <= c_pre)) (PreH12 : (c_pre <= 90)) (PreH13 : ((i_pre + s_pre ) <= n_pre)) (PreH14 : ((j_pre + s_pre ) <= m_pre)) (PreH15 : (i_pre <= r)) (PreH16 : (r <= (i_pre + s_pre ))) (PreH17 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH18 : (CanonicalGrid flat )) (PreH19 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + s_pre )) ”
.

Definition can_place_safety_wit_6 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (1 <= s_pre)) (PreH10 : (s_pre <= 101)) (PreH11 : (65 <= c_pre)) (PreH12 : (c_pre <= 90)) (PreH13 : ((i_pre + s_pre ) <= n_pre)) (PreH14 : ((j_pre + s_pre ) <= m_pre)) (PreH15 : (i_pre <= r)) (PreH16 : (r < (i_pre + s_pre ))) (PreH17 : (j_pre <= q)) (PreH18 : (q <= (j_pre + s_pre ))) (PreH19 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + s_pre )) ”
.

Definition can_place_safety_wit_7 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((r * m_pre ) + q ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((r * m_pre ) + q )) ”
.

Definition can_place_safety_wit_8 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((r * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r * m_pre )) ”
.

Definition can_place_safety_wit_9 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) <> 0)),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_10 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition can_place_safety_wit_11 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition can_place_safety_wit_12 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (1 <= s_pre)) (PreH10 : (s_pre <= 101)) (PreH11 : (65 <= c_pre)) (PreH12 : (c_pre <= 90)) (PreH13 : ((i_pre + s_pre ) <= n_pre)) (PreH14 : ((j_pre + s_pre ) <= m_pre)) (PreH15 : (j_pre <= q)) (PreH16 : (q <= (j_pre + s_pre ))) (PreH17 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH18 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )) (PreH21 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH22 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + s_pre )) ”
.

Definition can_place_safety_wit_13 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (j_pre <= q)) (PreH17 : (q <= (j_pre + s_pre ))) (PreH18 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_14 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (i_pre > 0)) (PreH2 : (q < (j_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (j_pre <= q)) (PreH18 : (q <= (j_pre + s_pre ))) (PreH19 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((i_pre - 1 ) * m_pre ) + q ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre - 1 ) * m_pre ) + q )) ”
.

Definition can_place_safety_wit_15 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (i_pre > 0)) (PreH2 : (q < (j_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (j_pre <= q)) (PreH18 : (q <= (j_pre + s_pre ))) (PreH19 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((i_pre - 1 ) * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre - 1 ) * m_pre )) ”
.

Definition can_place_safety_wit_16 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (i_pre > 0)) (PreH2 : (q < (j_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (j_pre <= q)) (PreH18 : (q <= (j_pre + s_pre ))) (PreH19 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre - 1 )) ”
.

Definition can_place_safety_wit_17 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (i_pre > 0)) (PreH2 : (q < (j_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (j_pre <= q)) (PreH18 : (q <= (j_pre + s_pre ))) (PreH19 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition can_place_safety_wit_18 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_19 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((i_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + s_pre )) ”
.

Definition can_place_safety_wit_20 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (i_pre <= 0)) (PreH2 : (q < (j_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (j_pre <= q)) (PreH18 : (q <= (j_pre + s_pre ))) (PreH19 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + s_pre )) ”
.

Definition can_place_safety_wit_21 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((i_pre + s_pre ) * m_pre ) + q ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre + s_pre ) * m_pre ) + q )) ”
.

Definition can_place_safety_wit_22 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((((i_pre + s_pre ) * m_pre ) + q ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((i_pre + s_pre ) * m_pre ) + q )) ”
.

Definition can_place_safety_wit_23 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((i_pre + s_pre ) * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre + s_pre ) * m_pre )) ”
.

Definition can_place_safety_wit_24 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ (((i_pre + s_pre ) * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i_pre + s_pre ) * m_pre )) ”
.

Definition can_place_safety_wit_25 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + s_pre )) ”
.

Definition can_place_safety_wit_26 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((i_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + s_pre )) ”
.

Definition can_place_safety_wit_27 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_28 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_29 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition can_place_safety_wit_30 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition can_place_safety_wit_31 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition can_place_safety_wit_32 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition can_place_safety_wit_33 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < n_pre)) (PreH7 : (0 <= j_pre)) (PreH8 : (j_pre < m_pre)) (PreH9 : (1 <= s_pre)) (PreH10 : (s_pre <= 101)) (PreH11 : (65 <= c_pre)) (PreH12 : (c_pre <= 90)) (PreH13 : ((i_pre + s_pre ) <= n_pre)) (PreH14 : ((j_pre + s_pre ) <= m_pre)) (PreH15 : (i_pre <= r)) (PreH16 : (r <= (i_pre + s_pre ))) (PreH17 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH18 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH19 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid flat )) (PreH21 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH22 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH23 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + s_pre )) ”
.

Definition can_place_safety_wit_34 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r < (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH19 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH24 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_35 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (j_pre > 0)) (PreH2 : (r < (i_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (i_pre <= r)) (PreH18 : (r <= (i_pre + s_pre ))) (PreH19 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH20 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH25 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((r * m_pre ) + j_pre ) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((r * m_pre ) + j_pre ) - 1 )) ”
.

Definition can_place_safety_wit_36 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (j_pre > 0)) (PreH2 : (r < (i_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (i_pre <= r)) (PreH18 : (r <= (i_pre + s_pre ))) (PreH19 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH20 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH25 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((r * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((r * m_pre ) + j_pre )) ”
.

Definition can_place_safety_wit_37 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (j_pre > 0)) (PreH2 : (r < (i_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (i_pre <= r)) (PreH18 : (r <= (i_pre + s_pre ))) (PreH19 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH20 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH25 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((r * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r * m_pre )) ”
.

Definition can_place_safety_wit_38 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (j_pre > 0)) (PreH2 : (r < (i_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (i_pre <= r)) (PreH18 : (r <= (i_pre + s_pre ))) (PreH19 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH20 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH25 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition can_place_safety_wit_39 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) = c_pre)) (PreH2 : (j_pre > 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_40 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH2 : (j_pre > 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((j_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + s_pre )) ”
.

Definition can_place_safety_wit_41 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (j_pre <= 0)) (PreH2 : (r < (i_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (i_pre <= r)) (PreH18 : (r <= (i_pre + s_pre ))) (PreH19 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH20 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH25 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j_pre + s_pre )) ”
.

Definition can_place_safety_wit_42 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((((r * m_pre ) + j_pre ) + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((r * m_pre ) + j_pre ) + s_pre )) ”
.

Definition can_place_safety_wit_43 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((((r * m_pre ) + j_pre ) + s_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (((r * m_pre ) + j_pre ) + s_pre )) ”
.

Definition can_place_safety_wit_44 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((r * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((r * m_pre ) + j_pre )) ”
.

Definition can_place_safety_wit_45 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (((r * m_pre ) + j_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((r * m_pre ) + j_pre )) ”
.

Definition can_place_safety_wit_46 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((r * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r * m_pre )) ”
.

Definition can_place_safety_wit_47 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r * m_pre )) ”
.

Definition can_place_safety_wit_48 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_49 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition can_place_safety_wit_50 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition can_place_safety_wit_51 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition can_place_safety_wit_52 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition can_place_safety_wit_53 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition can_place_safety_wit_54 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH19 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH24 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "c" ) )) # Char  |-> c_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition can_place_entail_wit_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((j_pre + s_pre ) <= m_pre)) (PreH2 : ((i_pre + s_pre ) <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= i_pre) ”
  &&  “ (i_pre <= (i_pre + s_pre )) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((i_pre - i_pre ) * s_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((j_pre + s_pre ) <= m_pre)) (PreH2 : ((i_pre + s_pre ) <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((i_pre - i_pre ) * s_pre ) ) ”
  &&  emp
).

Definition can_place_entail_wit_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((j_pre + s_pre ) <= m_pre)) (PreH2 : ((i_pre + s_pre ) <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid flat )),
  (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((i_pre - i_pre ) * s_pre ) )
.

Definition can_place_entail_wit_2 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r < (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= r) ”
  &&  “ (r < (i_pre + s_pre )) ”
  &&  “ (j_pre <= j_pre) ”
  &&  “ (j_pre <= (j_pre + s_pre )) ”
  &&  “ ((j_pre < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + j_pre )) /\ (((r * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (j_pre - j_pre ) ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r < (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  TT && emp 
|--
  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (j_pre - j_pre ) ) ) ”
  &&  “ ((j_pre < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + j_pre )) /\ (((r * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_2_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r < (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (j_pre - j_pre ) ) )
.

Definition can_place_entail_wit_2_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r < (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  ((j_pre < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + j_pre )) /\ (((r * m_pre ) + j_pre ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_3 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i_pre + s_pre )) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r + 1 ) - i_pre ) * s_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  TT && emp 
|--
  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r + 1 ) - i_pre ) * s_pre ) ) ”
  &&  emp
).

Definition can_place_entail_wit_3_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r + 1 ) - i_pre ) * s_pre ) )
.

Definition can_place_entail_wit_4 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= r) ”
  &&  “ (r < (i_pre + s_pre )) ”
  &&  “ (j_pre <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (j_pre + s_pre )) ”
  &&  “ (((q + 1 ) < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + (q + 1 ) )) /\ (((r * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + ((q + 1 ) - j_pre ) ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) = 0)),
  TT && emp 
|--
  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + ((q + 1 ) - j_pre ) ) ) ”
  &&  “ (((q + 1 ) < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + (q + 1 ) )) /\ (((r * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_4_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) = 0)),
  (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + ((q + 1 ) - j_pre ) ) )
.

Definition can_place_entail_wit_4_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) = 0)),
  (((q + 1 ) < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + (q + 1 ) )) /\ (((r * m_pre ) + (q + 1 ) ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_5 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= j_pre) ”
  &&  “ (j_pre <= (j_pre + s_pre )) ”
  &&  “ (((j_pre < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + j_pre )) /\ ((((i_pre + s_pre ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (j_pre - j_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  TT && emp 
|--
  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (j_pre - j_pre ) ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (((j_pre < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + j_pre )) /\ ((((i_pre + s_pre ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((j_pre < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_5_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (j_pre - j_pre ) )
.

Definition can_place_entail_wit_5_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )
.

Definition can_place_entail_wit_5_split_goal_3 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  (((j_pre < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + j_pre )) /\ ((((i_pre + s_pre ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_5_split_goal_4 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid flat )) (PreH20 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre ((r - i_pre ) * s_pre ) )),
  (((j_pre < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + j_pre )) /\ ((((i_pre - 1 ) * m_pre ) + j_pre ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_6_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (j_pre + s_pre )) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_6_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) )
.

Definition can_place_entail_wit_6_1_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_6_2 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (j_pre + s_pre )) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  emp
).

Definition can_place_entail_wit_6_2_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) >= n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) )
.

Definition can_place_entail_wit_6_3 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (j_pre + s_pre )) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_6_3_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) )
.

Definition can_place_entail_wit_6_3_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_6_4 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (j_pre + s_pre )) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) ) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_6_4_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((q + 1 ) - j_pre ) )
.

Definition can_place_entail_wit_6_4_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((((q + 1 ) < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre + s_pre ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_6_4_split_goal_3 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ((((q + 1 ) < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + (q + 1 ) )) /\ ((((i_pre - 1 ) * m_pre ) + (q + 1 ) ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_7 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (j_pre <= q)) (PreH17 : (q <= (j_pre + s_pre ))) (PreH18 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= i_pre) ”
  &&  “ (i_pre <= (i_pre + s_pre )) ”
  &&  “ (((i_pre < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + s_pre )) /\ ((((i_pre * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (i_pre - i_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (j_pre <= q)) (PreH17 : (q <= (j_pre + s_pre ))) (PreH18 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (i_pre - i_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (((i_pre < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + s_pre )) /\ ((((i_pre * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ (((i_pre < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_7_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (j_pre <= q)) (PreH17 : (q <= (j_pre + s_pre ))) (PreH18 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (i_pre - i_pre ) )
.

Definition can_place_entail_wit_7_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (j_pre <= q)) (PreH17 : (q <= (j_pre + s_pre ))) (PreH18 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )
.

Definition can_place_entail_wit_7_split_goal_3 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (j_pre <= q)) (PreH17 : (q <= (j_pre + s_pre ))) (PreH18 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (((i_pre < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((i_pre * m_pre ) + j_pre ) + s_pre )) /\ ((((i_pre * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_7_split_goal_4 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (q >= (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (j_pre <= q)) (PreH17 : (q <= (j_pre + s_pre ))) (PreH18 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (((i_pre < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((i_pre * m_pre ) + j_pre ) - 1 )) /\ ((((i_pre * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_8_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i_pre + s_pre )) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_8_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) )
.

Definition can_place_entail_wit_8_1_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_8_2 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i_pre + s_pre )) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  emp
).

Definition can_place_entail_wit_8_2_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) >= m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) )
.

Definition can_place_entail_wit_8_3 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i_pre + s_pre )) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_8_3_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) )
.

Definition can_place_entail_wit_8_3_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_8_4 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i_pre + s_pre )) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) ) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition can_place_entail_wit_8_4_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre ((r + 1 ) - i_pre ) )
.

Definition can_place_entail_wit_8_4_split_goal_2 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((((r + 1 ) < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) + s_pre )) /\ (((((r + 1 ) * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))
.

Definition can_place_entail_wit_8_4_split_goal_3 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) <> c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ((((r + 1 ) < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= ((((r + 1 ) * m_pre ) + j_pre ) - 1 )) /\ (((((r + 1 ) * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))
.

Definition can_place_return_wit_1 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH19 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH24 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (1 = 1) ”
  &&  “ (CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH19 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH24 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ (CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ) ”
  &&  emp
).

Definition can_place_return_wit_1_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (r >= (i_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r <= (i_pre + s_pre ))) (PreH18 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH19 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid flat )) (PreH22 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH23 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH24 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )
.

Definition can_place_return_wit_2 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_2_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : (j_pre <= 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_3 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_3_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0) = c_pre)) (PreH2 : ((j_pre + s_pre ) < m_pre)) (PreH3 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH4 : (j_pre > 0)) (PreH5 : (r < (i_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (i_pre <= r)) (PreH21 : (r <= (i_pre + s_pre ))) (PreH22 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH23 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH28 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_4 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) = c_pre)) (PreH2 : (j_pre > 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) = c_pre)) (PreH2 : (j_pre > 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_4_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) = c_pre)) (PreH2 : (j_pre > 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_5 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_5_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : (i_pre <= 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_6 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_6_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : ((i_pre + s_pre ) < n_pre)) (PreH3 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH4 : (i_pre > 0)) (PreH5 : (q < (j_pre + s_pre ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i_pre)) (PreH11 : (i_pre < n_pre)) (PreH12 : (0 <= j_pre)) (PreH13 : (j_pre < m_pre)) (PreH14 : (1 <= s_pre)) (PreH15 : (s_pre <= 101)) (PreH16 : (65 <= c_pre)) (PreH17 : (c_pre <= 90)) (PreH18 : ((i_pre + s_pre ) <= n_pre)) (PreH19 : ((j_pre + s_pre ) <= m_pre)) (PreH20 : (j_pre <= q)) (PreH21 : (q <= (j_pre + s_pre ))) (PreH22 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH24 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH25 : (CanonicalGrid flat )) (PreH26 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH27 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_7 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_7_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) = c_pre)) (PreH2 : (i_pre > 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_8 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) <> 0)),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) <> 0)),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_8_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )) (PreH24 : ((Znth ((r * m_pre ) + q ) flat 0) <> 0)),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_9 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((i_pre + s_pre ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((i_pre + s_pre ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_9_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((i_pre + s_pre ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid flat )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_return_wit_10 :=
(
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((j_pre + s_pre ) > m_pre)) (PreH2 : ((i_pre + s_pre ) <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid flat )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 = 0) ”
  &&  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((j_pre + s_pre ) > m_pre)) (PreH2 : ((i_pre + s_pre ) <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid flat )),
  TT && emp 
|--
  “ ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre )) ”
  &&  emp
).

Definition can_place_return_wit_10_split_goal_1 :=
forall (flat: (@list Z)) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (PreH1 : ((j_pre + s_pre ) > m_pre)) (PreH2 : ((i_pre + s_pre ) <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid flat )),
  ~((CanPlace flat n_pre m_pre i_pre j_pre s_pre c_pre ))
.

Definition can_place_partial_solve_wit_1 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (r: Z) (PreH1 : (q < (j_pre + s_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i_pre)) (PreH7 : (i_pre < n_pre)) (PreH8 : (0 <= j_pre)) (PreH9 : (j_pre < m_pre)) (PreH10 : (1 <= s_pre)) (PreH11 : (s_pre <= 101)) (PreH12 : (65 <= c_pre)) (PreH13 : (c_pre <= 90)) (PreH14 : ((i_pre + s_pre ) <= n_pre)) (PreH15 : ((j_pre + s_pre ) <= m_pre)) (PreH16 : (i_pre <= r)) (PreH17 : (r < (i_pre + s_pre ))) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (q < (j_pre + s_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= r) ”
  &&  “ (r < (i_pre + s_pre )) ”
  &&  “ (j_pre <= q) ”
  &&  “ (q <= (j_pre + s_pre )) ”
  &&  “ ((q < (j_pre + s_pre )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (((r - i_pre ) * s_pre ) + (q - j_pre ) ) ) ”
  &&  (((g_pre + (((r * m_pre ) + q ) * sizeof(CHAR)))) # Char  |-> (Znth ((r * m_pre ) + q ) flat 0))
  **  (CharArray.missing_i g_pre ((r * m_pre ) + q ) 0 (n_pre * m_pre ) flat )
.

Definition can_place_partial_solve_wit_2 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : (i_pre > 0)) (PreH2 : (q < (j_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (j_pre <= q)) (PreH18 : (q <= (j_pre + s_pre ))) (PreH19 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (i_pre > 0) ”
  &&  “ (q < (j_pre + s_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= q) ”
  &&  “ (q <= (j_pre + s_pre )) ”
  &&  “ (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) ) ”
  &&  (((g_pre + ((((i_pre - 1 ) * m_pre ) + q ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre - 1 ) * m_pre ) + q ) 0 (n_pre * m_pre ) flat )
.

Definition can_place_partial_solve_wit_3 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre)) (PreH3 : (i_pre > 0)) (PreH4 : (q < (j_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (j_pre <= q)) (PreH20 : (q <= (j_pre + s_pre ))) (PreH21 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + s_pre ) < n_pre) ”
  &&  “ ((Znth (((i_pre - 1 ) * m_pre ) + q ) flat 0) <> c_pre) ”
  &&  “ (i_pre > 0) ”
  &&  “ (q < (j_pre + s_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= q) ”
  &&  “ (q <= (j_pre + s_pre )) ”
  &&  “ (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) ) ”
  &&  (((g_pre + ((((i_pre + s_pre ) * m_pre ) + q ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre + s_pre ) * m_pre ) + q ) 0 (n_pre * m_pre ) flat )
.

Definition can_place_partial_solve_wit_4 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (q: Z) (PreH1 : ((i_pre + s_pre ) < n_pre)) (PreH2 : (i_pre <= 0)) (PreH3 : (q < (j_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (j_pre <= q)) (PreH19 : (q <= (j_pre + s_pre ))) (PreH20 : (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH21 : (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i_pre + s_pre ) < n_pre) ”
  &&  “ (i_pre <= 0) ”
  &&  “ (q < (j_pre + s_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (j_pre <= q) ”
  &&  “ (q <= (j_pre + s_pre )) ”
  &&  “ (((q < (j_pre + s_pre )) /\ (i_pre > 0)) -> ((0 <= (((i_pre - 1 ) * m_pre ) + q )) /\ ((((i_pre - 1 ) * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ (((q < (j_pre + s_pre )) /\ ((i_pre + s_pre ) < n_pre)) -> ((0 <= (((i_pre + s_pre ) * m_pre ) + q )) /\ ((((i_pre + s_pre ) * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (q - j_pre ) ) ”
  &&  (((g_pre + ((((i_pre + s_pre ) * m_pre ) + q ) * sizeof(CHAR)))) # Char  |-> (Znth (((i_pre + s_pre ) * m_pre ) + q ) flat 0))
  **  (CharArray.missing_i g_pre (((i_pre + s_pre ) * m_pre ) + q ) 0 (n_pre * m_pre ) flat )
.

Definition can_place_partial_solve_wit_5 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : (j_pre > 0)) (PreH2 : (r < (i_pre + s_pre ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < n_pre)) (PreH9 : (0 <= j_pre)) (PreH10 : (j_pre < m_pre)) (PreH11 : (1 <= s_pre)) (PreH12 : (s_pre <= 101)) (PreH13 : (65 <= c_pre)) (PreH14 : (c_pre <= 90)) (PreH15 : ((i_pre + s_pre ) <= n_pre)) (PreH16 : ((j_pre + s_pre ) <= m_pre)) (PreH17 : (i_pre <= r)) (PreH18 : (r <= (i_pre + s_pre ))) (PreH19 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH20 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH21 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid flat )) (PreH23 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH24 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH25 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (j_pre > 0) ”
  &&  “ (r < (i_pre + s_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= r) ”
  &&  “ (r <= (i_pre + s_pre )) ”
  &&  “ (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) ) ”
  &&  (((g_pre + ((((r * m_pre ) + j_pre ) - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0))
  **  (CharArray.missing_i g_pre (((r * m_pre ) + j_pre ) - 1 ) 0 (n_pre * m_pre ) flat )
.

Definition can_place_partial_solve_wit_6 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre)) (PreH3 : (j_pre > 0)) (PreH4 : (r < (i_pre + s_pre ))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i_pre)) (PreH10 : (i_pre < n_pre)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre < m_pre)) (PreH13 : (1 <= s_pre)) (PreH14 : (s_pre <= 101)) (PreH15 : (65 <= c_pre)) (PreH16 : (c_pre <= 90)) (PreH17 : ((i_pre + s_pre ) <= n_pre)) (PreH18 : ((j_pre + s_pre ) <= m_pre)) (PreH19 : (i_pre <= r)) (PreH20 : (r <= (i_pre + s_pre ))) (PreH21 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH22 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH23 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH24 : (CanonicalGrid flat )) (PreH25 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH26 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH27 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + s_pre ) < m_pre) ”
  &&  “ ((Znth (((r * m_pre ) + j_pre ) - 1 ) flat 0) <> c_pre) ”
  &&  “ (j_pre > 0) ”
  &&  “ (r < (i_pre + s_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= r) ”
  &&  “ (r <= (i_pre + s_pre )) ”
  &&  “ (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) ) ”
  &&  (((g_pre + ((((r * m_pre ) + j_pre ) + s_pre ) * sizeof(CHAR)))) # Char  |-> (Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0))
  **  (CharArray.missing_i g_pre (((r * m_pre ) + j_pre ) + s_pre ) 0 (n_pre * m_pre ) flat )
.

Definition can_place_partial_solve_wit_7 :=
forall (flat: (@list Z)) (g_pre: Z) (n_pre: Z) (m_pre: Z) (i_pre: Z) (j_pre: Z) (s_pre: Z) (c_pre: Z) (r: Z) (PreH1 : ((j_pre + s_pre ) < m_pre)) (PreH2 : (j_pre <= 0)) (PreH3 : (r < (i_pre + s_pre ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : (0 <= i_pre)) (PreH9 : (i_pre < n_pre)) (PreH10 : (0 <= j_pre)) (PreH11 : (j_pre < m_pre)) (PreH12 : (1 <= s_pre)) (PreH13 : (s_pre <= 101)) (PreH14 : (65 <= c_pre)) (PreH15 : (c_pre <= 90)) (PreH16 : ((i_pre + s_pre ) <= n_pre)) (PreH17 : ((j_pre + s_pre ) <= m_pre)) (PreH18 : (i_pre <= r)) (PreH19 : (r <= (i_pre + s_pre ))) (PreH20 : (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre ))))) (PreH21 : (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre ))))) (PreH22 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid flat )) (PreH24 : (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) )) (PreH25 : (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre )) (PreH26 : (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((j_pre + s_pre ) < m_pre) ”
  &&  “ (j_pre <= 0) ”
  &&  “ (r < (i_pre + s_pre )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < n_pre) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre < m_pre) ”
  &&  “ (1 <= s_pre) ”
  &&  “ (s_pre <= 101) ”
  &&  “ (65 <= c_pre) ”
  &&  “ (c_pre <= 90) ”
  &&  “ ((i_pre + s_pre ) <= n_pre) ”
  &&  “ ((j_pre + s_pre ) <= m_pre) ”
  &&  “ (i_pre <= r) ”
  &&  “ (r <= (i_pre + s_pre )) ”
  &&  “ (((r < (i_pre + s_pre )) /\ (j_pre > 0)) -> ((0 <= (((r * m_pre ) + j_pre ) - 1 )) /\ ((((r * m_pre ) + j_pre ) - 1 ) < (n_pre * m_pre )))) ”
  &&  “ (((r < (i_pre + s_pre )) /\ ((j_pre + s_pre ) < m_pre)) -> ((0 <= (((r * m_pre ) + j_pre ) + s_pre )) /\ ((((r * m_pre ) + j_pre ) + s_pre ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  “ (EmptySquarePrefix flat m_pre i_pre j_pre s_pre (s_pre * s_pre ) ) ”
  &&  “ (HorizontalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre s_pre ) ”
  &&  “ (VerticalBoundaryClearPrefix flat n_pre m_pre i_pre j_pre s_pre c_pre (r - i_pre ) ) ”
  &&  (((g_pre + ((((r * m_pre ) + j_pre ) + s_pre ) * sizeof(CHAR)))) # Char  |-> (Znth (((r * m_pre ) + j_pre ) + s_pre ) flat 0))
  **  (CharArray.missing_i g_pre (((r * m_pre ) + j_pre ) + s_pre ) 0 (n_pre * m_pre ) flat )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  (CharArray.full_shape g_pre (n_pre * m_pre ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat (i * m_pre ) )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat ((i * m_pre ) + j ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat ((i * m_pre ) + j ) )),
  (CharArray.full g_pre (n_pre * m_pre ) (replace_Znth (((i * m_pre ) + j )) (0) (flat)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat ((i * m_pre ) + j ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (((i * m_pre ) + j ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i * m_pre ) + j )) ”
.

Definition solver_safety_wit_6 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat ((i * m_pre ) + j ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ ((i * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i * m_pre )) ”
.

Definition solver_safety_wit_7 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat ((i * m_pre ) + j ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat (i * m_pre ) )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH9 : (CanonicalGrid grid )) (PreH10 : (GreedyPlacementTrace n_pre m_pre (i * m_pre ) grid )),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (((i * m_pre ) + j ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((i * m_pre ) + j )) ”
.

Definition solver_safety_wit_11 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ ((i * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i * m_pre )) ”
.

Definition solver_safety_wit_12 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH14 : ((Znth ((i * m_pre ) + j ) grid 0) = 0)),
  ((( &( "c" ) )) # Char  |->_)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH14 : ((Znth ((i * m_pre ) + j ) grid 0) = 0)),
  ((( &( "t" ) )) # Char  |->_)
  **  ((( &( "c" ) )) # Char  |-> 0)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (65 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 65) ”
.

Definition solver_safety_wit_14 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : (c = 0)) (PreH12 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH13 : (CanonicalGrid grid )) (PreH14 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH15 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH16 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH17 : (65 <= available)) (PreH18 : (available <= 69)) (PreH19 : (CanPlace grid n_pre m_pre i j 1 available )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Char  |-> t)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (90 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 90) ”
.

Definition solver_safety_wit_15 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (PreH1 : (t <= 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t)) (PreH11 : (t <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH17 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid n_pre m_pre i j 1 available )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Char  |-> t)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (CanPlace grid n_pre m_pre i j 1 t )) (PreH3 : (CanonicalGrid grid )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH20 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid n_pre m_pre i j 1 available )) (PreH24 : (retval = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Char  |-> t)
  **  ((( &( "c" ) )) # Char  |-> c)
|--
  “ False ”
.

Definition solver_safety_wit_17 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ~((CanPlace grid n_pre m_pre i j 1 t ))) (PreH3 : (CanonicalGrid grid )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH20 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid n_pre m_pre i j 1 available )) (PreH24 : (retval <> 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Char  |-> t)
  **  ((( &( "c" ) )) # Char  |-> c)
|--
  “ False ”
.

Definition solver_safety_wit_18 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (PreH1 : (t > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t)) (PreH11 : (t <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH17 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid n_pre m_pre i j 1 available )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ False ”
) \/
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (PreH1 : (t > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t)) (PreH11 : (t <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH17 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid n_pre m_pre i j 1 available )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ False ”
).

Definition solver_safety_wit_18_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (PreH1 : (t > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t)) (PreH11 : (t <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH17 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid n_pre m_pre i j 1 available )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ False ”
.

Definition solver_safety_wit_19 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ~((CanPlace grid n_pre m_pre i j 1 t ))) (PreH3 : (CanonicalGrid grid )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH20 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid n_pre m_pre i j 1 available )) (PreH24 : (retval = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Char  |-> t)
  **  ((( &( "c" ) )) # Char  |-> c)
|--
  “ ((t + 1 ) <= 127) ”
  &&  “ ((-128) <= (t + 1 )) ”
.

Definition solver_safety_wit_20_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH15 : (NoPlaceableColorBelow grid n_pre m_pre i j c )) (PreH16 : (CanPlace grid n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid n_pre m_pre i j 0 c )),
  ((( &( "size" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= c)) (PreH10 : (c <= 90)) (PreH11 : (1 <= size)) (PreH12 : (size <= (n_pre - i ))) (PreH13 : (size <= (m_pre - j ))) (PreH14 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid grid )) (PreH16 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH17 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH18 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH19 : (GreedySideState grid n_pre m_pre i j c size )) (PreH20 : (ChosenSquareState grid n_pre m_pre i j c size )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ ((j + size ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + size )) ”
.

Definition solver_safety_wit_22_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH19 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid n_pre m_pre i j c size )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ ((size + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (size + 1 )) ”
.

Definition solver_safety_wit_23_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH19 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid n_pre m_pre i j c size )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (CanPlace grid n_pre m_pre i j (size + 1 ) c )) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
|--
  “ False ”
.

Definition solver_safety_wit_25_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : ~((CanPlace grid n_pre m_pre i j (size + 1 ) c ))) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
|--
  “ False ”
.

Definition solver_safety_wit_26_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (CanPlace grid n_pre m_pre i j (size + 1 ) c )) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
|--
  “ ((j + size ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + size )) ”
.

Definition solver_safety_wit_27_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > c)) (PreH2 : (LeastLegalColor grid n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH26 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
|--
  “ ((size + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (size + 1 )) ”
.

Definition solver_safety_wit_28_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= c)) (PreH10 : (c <= 90)) (PreH11 : (1 <= size)) (PreH12 : (size <= (n_pre - i ))) (PreH13 : (size <= (m_pre - j ))) (PreH14 : (i <= r)) (PreH15 : (r <= (i + size ))) (PreH16 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH17 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH18 : (CanonicalGrid before )) (PreH19 : (CanonicalGrid current )) (PreH20 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH21 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH22 : (SettledSquareState before n_pre m_pre i j c size )) (PreH23 : (PaintRectanglePrefix before current m_pre i j size c ((r - i ) * size ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  “ ((i + size ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + size )) ”
.

Definition solver_safety_wit_29_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= c)) (PreH10 : (c <= 90)) (PreH11 : (1 <= size)) (PreH12 : (size <= (n_pre - i ))) (PreH13 : (size <= (m_pre - j ))) (PreH14 : (i <= r)) (PreH15 : (r < (i + size ))) (PreH16 : (j <= q)) (PreH17 : (q <= (j + size ))) (PreH18 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH19 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH20 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH21 : (CanonicalGrid before )) (PreH22 : (CanonicalGrid current )) (PreH23 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH24 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH25 : (SettledSquareState before n_pre m_pre i j c size )) (PreH26 : (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  “ ((j + size ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + size )) ”
.

Definition solver_safety_wit_30_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q >= (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before )) (PreH23 : (CanonicalGrid current )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH26 : (SettledSquareState before n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_31_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q < (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before )) (PreH23 : (CanonicalGrid current )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH26 : (SettledSquareState before n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  (CharArray.full g_pre (n_pre * m_pre ) (replace_Znth (((r * m_pre ) + q )) (c) (current)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_32_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q < (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before )) (PreH23 : (CanonicalGrid current )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH26 : (SettledSquareState before n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  “ (((r * m_pre ) + q ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((r * m_pre ) + q )) ”
.

Definition solver_safety_wit_33_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q < (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before )) (PreH23 : (CanonicalGrid current )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH26 : (SettledSquareState before n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  “ ((r * m_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r * m_pre )) ”
.

Definition solver_safety_wit_34 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_35_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (r >= (i + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r <= (i + size ))) (PreH17 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH18 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid before )) (PreH20 : (CanonicalGrid current )) (PreH21 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH23 : (SettledSquareState before n_pre m_pre i j c size )) (PreH24 : (PaintRectanglePrefix before current m_pre i j size c ((r - i ) * size ) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH10 : (CanonicalGrid grid )) (PreH11 : (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)),
  (CharArray.full_shape g_pre (n_pre * m_pre ) )
|--
  EX (flat: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (ZeroPrefix flat (0 * m_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)),
  (CharArray.full_shape g_pre (n_pre * m_pre ) )
|--
  EX (flat: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (ZeroPrefix flat (0 * m_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
).

Definition solver_entail_wit_2 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat_2 (i * m_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat_2 )
|--
  EX (flat: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ ((0 < m_pre) -> ((0 <= ((i * m_pre ) + 0 )) /\ (((i * m_pre ) + 0 ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (ZeroPrefix flat ((i * m_pre ) + 0 ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat_2 (i * m_pre ) )),
  TT && emp 
|--
  “ (ZeroPrefix flat_2 ((i * m_pre ) + 0 ) ) ”
  &&  “ ((0 < m_pre) -> ((0 <= ((i * m_pre ) + 0 )) /\ (((i * m_pre ) + 0 ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat_2 (i * m_pre ) )),
  (ZeroPrefix flat_2 ((i * m_pre ) + 0 ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat_2 (i * m_pre ) )),
  ((0 < m_pre) -> ((0 <= ((i * m_pre ) + 0 )) /\ (((i * m_pre ) + 0 ) < (n_pre * m_pre ))))
.

Definition solver_entail_wit_3 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat_2 )
|--
  EX (flat: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (ZeroPrefix flat ((i + 1 ) * m_pre ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  TT && emp 
|--
  “ (ZeroPrefix flat_2 ((i + 1 ) * m_pre ) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  (ZeroPrefix flat_2 ((i + 1 ) * m_pre ) )
.

Definition solver_entail_wit_4 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  (CharArray.full g_pre (n_pre * m_pre ) (replace_Znth (((i * m_pre ) + j )) (0) (flat_2)) )
|--
  EX (flat: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= m_pre) ”
  &&  “ (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (ZeroPrefix flat ((i * m_pre ) + (j + 1 ) ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) flat )
) \/
(
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  TT && emp 
|--
  “ (ZeroPrefix (replace_Znth (((i * m_pre ) + j )) (0) (flat_2)) ((i * m_pre ) + (j + 1 ) ) ) ”
  &&  “ ((Zlength ((replace_Znth (((i * m_pre ) + j )) (0) (flat_2)))) = (n_pre * m_pre )) ”
  &&  “ (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  (ZeroPrefix (replace_Znth (((i * m_pre ) + j )) (0) (flat_2)) ((i * m_pre ) + (j + 1 ) ) )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  ((Zlength ((replace_Znth (((i * m_pre ) + j )) (0) (flat_2)))) = (n_pre * m_pre ))
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (n_pre: Z) (m_pre: Z) (flat_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat_2)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat_2 ((i * m_pre ) + j ) )),
  (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre ))))
.

Definition solver_entail_wit_5 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat (i * m_pre ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre (0 * m_pre ) grid ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (flat: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat (i * m_pre ) )),
  TT && emp 
|--
  “ (GreedyPlacementTrace n_pre m_pre (0 * m_pre ) flat ) ”
  &&  “ (CanonicalGrid flat ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (flat: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat (i * m_pre ) )),
  (GreedyPlacementTrace n_pre m_pre (0 * m_pre ) flat )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (flat: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH9 : (ZeroPrefix flat (i * m_pre ) )),
  (CanonicalGrid flat )
.

Definition solver_entail_wit_6 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH9 : (CanonicalGrid grid_2 )) (PreH10 : (GreedyPlacementTrace n_pre m_pre (i * m_pre ) grid_2 )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ ((0 < m_pre) -> ((0 <= ((i * m_pre ) + 0 )) /\ (((i * m_pre ) + 0 ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + 0 ) grid ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH9 : (CanonicalGrid grid_2 )) (PreH10 : (GreedyPlacementTrace n_pre m_pre (i * m_pre ) grid_2 )),
  TT && emp 
|--
  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + 0 ) grid_2 ) ”
  &&  “ ((0 < m_pre) -> ((0 <= ((i * m_pre ) + 0 )) /\ (((i * m_pre ) + 0 ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH9 : (CanonicalGrid grid_2 )) (PreH10 : (GreedyPlacementTrace n_pre m_pre (i * m_pre ) grid_2 )),
  (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + 0 ) grid_2 )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH9 : (CanonicalGrid grid_2 )) (PreH10 : (GreedyPlacementTrace n_pre m_pre (i * m_pre ) grid_2 )),
  ((0 < m_pre) -> ((0 <= ((i * m_pre ) + 0 )) /\ (((i * m_pre ) + 0 ) < (n_pre * m_pre ))))
.

Definition solver_entail_wit_7 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH14 : ((Znth ((i * m_pre ) + j ) grid_2 0) <> 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH14 : ((Znth ((i * m_pre ) + j ) grid_2 0) <> 0)),
  TT && emp 
|--
  “ (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid_2 ) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH14 : ((Znth ((i * m_pre ) + j ) grid_2 0) <> 0)),
  (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid_2 )
.

Definition solver_entail_wit_8 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH14 : ((Znth ((i * m_pre ) + j ) grid_2 0) = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (available: Z) (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= 65) ”
  &&  “ (65 <= 91) ”
  &&  “ (0 = 0) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j 65 ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 available ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH14 : ((Znth ((i * m_pre ) + j ) grid_2 0) = 0)),
  TT && emp 
|--
  EX (available: Z),
  “ (65 <= 65) ”
  &&  “ (65 <= 91) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0) ”
  &&  “ (NoPlaceableColorBelow grid_2 n_pre m_pre i j 65 ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid_2 n_pre m_pre i j 1 available ) ”
  &&  emp
).

Definition solver_entail_wit_9_1 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (CanPlace grid n_pre m_pre i j 1 t )) (PreH3 : (CanonicalGrid grid )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH20 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid n_pre m_pre i j 1 available )) (PreH24 : (retval_2 = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  EX (retval: Z),
  “ (retval = 0) ”
  &&  “ ~((CanPlace grid n_pre m_pre i j 1 t )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (t <= 90) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ (c = 0) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j t ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 available ) ”
  &&  “ (retval = 0) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_9_2 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ~((CanPlace grid n_pre m_pre i j 1 t ))) (PreH3 : (CanonicalGrid grid )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH20 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid n_pre m_pre i j 1 available )) (PreH24 : (retval = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (retval = 0) ”
  &&  “ ~((CanPlace grid n_pre m_pre i j 1 t )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (t <= 90) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ (c = 0) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j t ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 available ) ”
  &&  “ (retval = 0) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_10_1 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (CanPlace grid n_pre m_pre i j 1 t )) (PreH3 : (CanonicalGrid grid )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH20 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid n_pre m_pre i j 1 available )) (PreH24 : (retval <> 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (retval = 1) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 t ) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (t <= 90) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ (c = 0) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j t ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 available ) ”
  &&  “ (retval <> 0) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_10_2 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : ~((CanPlace grid n_pre m_pre i j 1 t ))) (PreH3 : (CanonicalGrid grid )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH20 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid n_pre m_pre i j 1 available )) (PreH24 : (retval_2 <> 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  EX (retval: Z),
  “ (retval = 1) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 t ) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (t <= 90) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ (c = 0) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j t ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 available ) ”
  &&  “ (retval <> 0) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_11 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid_2: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (CanPlace grid_2 n_pre m_pre i j 1 t )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid_2 )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH20 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid_2 n_pre m_pre i j 1 available )) (PreH24 : (retval <> 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j t ) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 t ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 t ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (available: Z) (grid_2: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (CanPlace grid_2 n_pre m_pre i j 1 t )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid_2 )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH20 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid_2 n_pre m_pre i j 1 available )) (PreH24 : (retval <> 0)),
  TT && emp 
|--
  “ (LeastLegalColor grid_2 n_pre m_pre i j 0 t ) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (available: Z) (grid_2: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (CanPlace grid_2 n_pre m_pre i j 1 t )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid_2 )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH20 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j t )) (PreH21 : (65 <= available)) (PreH22 : (available <= 69)) (PreH23 : (CanPlace grid_2 n_pre m_pre i j 1 available )) (PreH24 : (retval <> 0)),
  (LeastLegalColor grid_2 n_pre m_pre i j 0 t )
.

Definition solver_entail_wit_12_1 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid_2: (@list Z)) (c: Z) (t_2: Z) (j: Z) (i: Z) (PreH1 : (t_2 > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t_2)) (PreH11 : (t_2 <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid_2 )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH17 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j t_2 )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid_2 n_pre m_pre i j 1 available )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)) (t: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j c ) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 c ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (available: Z) (grid_2: (@list Z)) (c: Z) (t_2: Z) (j: Z) (i: Z) (PreH1 : (t_2 > 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t_2)) (PreH11 : (t_2 <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid_2 )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH17 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j t_2 )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid_2 n_pre m_pre i j 1 available )),
  TT && emp 
|--
  EX (t: Z),
  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ (NoPlaceableColorBelow grid_2 n_pre m_pre i j 0 ) ”
  &&  “ (CanPlace grid_2 n_pre m_pre i j 1 0 ) ”
  &&  “ (LeastLegalColor grid_2 n_pre m_pre i j 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_12_2_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH15 : (NoPlaceableColorBelow grid n_pre m_pre i j c )) (PreH16 : (CanPlace grid n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid n_pre m_pre i j 0 c )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j c ) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 c ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_13 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available_2: Z) (grid_2: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ~((CanPlace grid_2 n_pre m_pre i j 1 t ))) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid_2 )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH20 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j t )) (PreH21 : (65 <= available_2)) (PreH22 : (available_2 <= 69)) (PreH23 : (CanPlace grid_2 n_pre m_pre i j 1 available_2 )) (PreH24 : (retval = 0)),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (available: Z) (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= (t + 1 )) ”
  &&  “ ((t + 1 ) <= 91) ”
  &&  “ (c = 0) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j (t + 1 ) ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 available ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (available_2: Z) (grid_2: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ~((CanPlace grid_2 n_pre m_pre i j 1 t ))) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (t <= 90)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < m_pre)) (PreH13 : (65 <= t)) (PreH14 : (t <= 91)) (PreH15 : (c = 0)) (PreH16 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH17 : (CanonicalGrid grid_2 )) (PreH18 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH19 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH20 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j t )) (PreH21 : (65 <= available_2)) (PreH22 : (available_2 <= 69)) (PreH23 : (CanPlace grid_2 n_pre m_pre i j 1 available_2 )) (PreH24 : (retval = 0)),
  TT && emp 
|--
  EX (available: Z),
  “ (65 <= (t + 1 )) ”
  &&  “ ((t + 1 ) <= 91) ”
  &&  “ (CanonicalGrid grid_2 ) ”
  &&  “ (NoPlaceableColorBelow grid_2 n_pre m_pre i j (t + 1 ) ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid_2 n_pre m_pre i j 1 available ) ”
  &&  emp
).

Definition solver_entail_wit_14_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH15 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j c )) (PreH16 : (CanPlace grid_2 n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre - i )) ”
  &&  “ (1 <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c 1 ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c 1 ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH15 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j c )) (PreH16 : (CanPlace grid_2 n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )),
  TT && emp 
|--
  “ (ChosenSquareState grid_2 n_pre m_pre i j c 1 ) ”
  &&  “ (GreedySideState grid_2 n_pre m_pre i j c 1 ) ”
  &&  “ (c <= 90) ”
  &&  “ (65 <= c) ”
  &&  emp
).

Definition solver_entail_wit_14_colour_found_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH15 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j c )) (PreH16 : (CanPlace grid_2 n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )),
  (ChosenSquareState grid_2 n_pre m_pre i j c 1 )
.

Definition solver_entail_wit_14_colour_found_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH15 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j c )) (PreH16 : (CanPlace grid_2 n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )),
  (GreedySideState grid_2 n_pre m_pre i j c 1 )
.

Definition solver_entail_wit_14_colour_found_split_goal_3 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH15 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j c )) (PreH16 : (CanPlace grid_2 n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )),
  (c <= 90)
.

Definition solver_entail_wit_14_colour_found_split_goal_4 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (t: Z) (c: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= t)) (PreH10 : (t <= 91)) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH14 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH15 : (NoPlaceableColorBelow grid_2 n_pre m_pre i j c )) (PreH16 : (CanPlace grid_2 n_pre m_pre i j 1 c )) (PreH17 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )),
  (65 <= c)
.

Definition solver_entail_wit_15_1_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH19 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ ((j + size ) >= m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_15_2_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ~((CanPlace grid n_pre m_pre i j (size + 1 ) c ))) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (retval = 0) ”
  &&  “ (retval = 0) ”
  &&  “ ~((CanPlace grid n_pre m_pre i j (size + 1 ) c )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_15_3_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = 1)) (PreH3 : (CanPlace grid n_pre m_pre i j (size + 1 ) c )) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  (“ ((j + size ) >= m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid ))
  ||
  (EX (retval: Z),
  “ (retval = 0) ”
  &&  “ (retval = 0) ”
  &&  “ ~((CanPlace grid n_pre m_pre i j (size + 1 ) c )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid ))
.

Definition solver_entail_wit_16_1_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : ~((CanPlace grid n_pre m_pre i j (size + 1 ) c ))) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  EX (retval: Z),
  “ (retval <> 0) ”
  &&  “ (retval = 1) ”
  &&  “ (CanPlace grid n_pre m_pre i j (size + 1 ) c ) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_16_2_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (CanPlace grid n_pre m_pre i j (size + 1 ) c )) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (retval <> 0) ”
  &&  “ (retval = 1) ”
  &&  “ (CanPlace grid n_pre m_pre i j (size + 1 ) c ) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_entail_wit_17_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= (size + 1 )) ”
  &&  “ ((size + 1 ) <= (n_pre - i )) ”
  &&  “ ((size + 1 ) <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c (size + 1 ) ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c (size + 1 ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  TT && emp 
|--
  “ (ChosenSquareState grid_2 n_pre m_pre i j c (size + 1 ) ) ”
  &&  “ (GreedySideState grid_2 n_pre m_pre i j c (size + 1 ) ) ”
  &&  “ ((size + 1 ) <= (n_pre - i )) ”
  &&  emp
).

Definition solver_entail_wit_17_colour_found_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (ChosenSquareState grid_2 n_pre m_pre i j c (size + 1 ) )
.

Definition solver_entail_wit_17_colour_found_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (GreedySideState grid_2 n_pre m_pre i j c (size + 1 ) )
.

Definition solver_entail_wit_17_colour_found_split_goal_3 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  ((size + 1 ) <= (n_pre - i ))
.

Definition solver_entail_wit_18_1_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid_2 )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH19 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (SettledSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid_2 )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH19 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  TT && emp 
|--
  “ (SettledSquareState grid_2 n_pre m_pre i j c size ) ”
  &&  emp
).

Definition solver_entail_wit_18_1_colour_found_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid_2 )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH19 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (SettledSquareState grid_2 n_pre m_pre i j c size )
.

Definition solver_entail_wit_18_2_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ~((CanPlace grid_2 n_pre m_pre i j (size + 1 ) c ))) (PreH4 : (CanonicalGrid grid_2 )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid_2 )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH23 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (SettledSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ~((CanPlace grid_2 n_pre m_pre i j (size + 1 ) c ))) (PreH4 : (CanonicalGrid grid_2 )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid_2 )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH23 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  TT && emp 
|--
  “ (SettledSquareState grid_2 n_pre m_pre i j c size ) ”
  &&  emp
).

Definition solver_entail_wit_18_2_colour_found_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ~((CanPlace grid_2 n_pre m_pre i j (size + 1 ) c ))) (PreH4 : (CanonicalGrid grid_2 )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid_2 )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH23 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (SettledSquareState grid_2 n_pre m_pre i j c size )
.

Definition solver_entail_wit_18_3_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <= c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (SettledSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <= c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  TT && emp 
|--
  “ (SettledSquareState grid_2 n_pre m_pre i j c size ) ”
  &&  emp
).

Definition solver_entail_wit_18_3_colour_found_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <= c)) (PreH2 : (LeastLegalColor grid_2 n_pre m_pre i (j + size ) c retval_2 )) (PreH3 : (CanonicalGrid grid_2 )) (PreH4 : (retval <> 0)) (PreH5 : (retval = 1)) (PreH6 : (CanPlace grid_2 n_pre m_pre i j (size + 1 ) c )) (PreH7 : (CanonicalGrid grid_2 )) (PreH8 : ((j + size ) < m_pre)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (65 <= c)) (PreH18 : (c <= 90)) (PreH19 : (1 <= size)) (PreH20 : (size <= (n_pre - i ))) (PreH21 : (size <= (m_pre - j ))) (PreH22 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH23 : (CanonicalGrid grid_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (grid_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )) (PreH26 : (LeastLegalColor grid_2 n_pre m_pre i j 0 c )) (PreH27 : (GreedySideState grid_2 n_pre m_pre i j c size )) (PreH28 : (ChosenSquareState grid_2 n_pre m_pre i j c size )),
  (SettledSquareState grid_2 n_pre m_pre i j c size )
.

Definition solver_entail_wit_19_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (i: Z) (j: Z) (c: Z) (size: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= c)) (PreH10 : (c <= 90)) (PreH11 : (1 <= size)) (PreH12 : (size <= (n_pre - i ))) (PreH13 : (size <= (m_pre - j ))) (PreH14 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid grid )) (PreH16 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH17 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH18 : (SettledSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  EX (current: (@list Z)) (before: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ (i <= i) ”
  &&  “ (i <= (i + size )) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ ((Zlength (current)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ (CanonicalGrid current ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before current m_pre i j size c ((i - i ) * size ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) current )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid: (@list Z)) (i: Z) (j: Z) (c: Z) (size: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : (65 <= c)) (PreH10 : (c <= 90)) (PreH11 : (1 <= size)) (PreH12 : (size <= (n_pre - i ))) (PreH13 : (size <= (m_pre - j ))) (PreH14 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH15 : (CanonicalGrid grid )) (PreH16 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH17 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH18 : (SettledSquareState grid n_pre m_pre i j c size )),
  TT && emp 
|--
  EX (before: (@list Z)),
  “ (i <= i) ”
  &&  “ (i <= (i + size )) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before grid m_pre i j size c ((i - i ) * size ) ) ”
  &&  emp
).

Definition solver_entail_wit_20_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current_2: (@list Z)) (before_2: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (r < (i + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r <= (i + size ))) (PreH17 : ((Zlength (before_2)) = (n_pre * m_pre ))) (PreH18 : ((Zlength (current_2)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid before_2 )) (PreH20 : (CanonicalGrid current_2 )) (PreH21 : ((Znth (((i * m_pre ) + j )) (before_2) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before_2 )) (PreH23 : (SettledSquareState before_2 n_pre m_pre i j c size )) (PreH24 : (PaintRectanglePrefix before_2 current_2 m_pre i j size c ((r - i ) * size ) )),
  (CharArray.full g_pre (n_pre * m_pre ) current_2 )
|--
  EX (current: (@list Z)) (before: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ (i <= r) ”
  &&  “ (r < (i + size )) ”
  &&  “ (j <= j) ”
  &&  “ (j <= (j + size )) ”
  &&  “ ((j < (j + size )) -> ((0 <= ((r * m_pre ) + j )) /\ (((r * m_pre ) + j ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ ((Zlength (current)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ (CanonicalGrid current ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (j - j ) ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) current )
) \/
(
forall (n_pre: Z) (m_pre: Z) (current_2: (@list Z)) (before_2: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (r < (i + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r <= (i + size ))) (PreH17 : ((Zlength (before_2)) = (n_pre * m_pre ))) (PreH18 : ((Zlength (current_2)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid before_2 )) (PreH20 : (CanonicalGrid current_2 )) (PreH21 : ((Znth (((i * m_pre ) + j )) (before_2) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before_2 )) (PreH23 : (SettledSquareState before_2 n_pre m_pre i j c size )) (PreH24 : (PaintRectanglePrefix before_2 current_2 m_pre i j size c ((r - i ) * size ) )),
  TT && emp 
|--
  EX (before: (@list Z)),
  “ (j <= j) ”
  &&  “ (j <= (j + size )) ”
  &&  “ ((j < (j + size )) -> ((0 <= ((r * m_pre ) + j )) /\ (((r * m_pre ) + j ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before current_2 m_pre i j size c (((r - i ) * size ) + (j - j ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_21_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current_2: (@list Z)) (before_2: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q >= (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before_2)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current_2)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before_2 )) (PreH23 : (CanonicalGrid current_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before_2 )) (PreH26 : (SettledSquareState before_2 n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before_2 current_2 m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  (CharArray.full g_pre (n_pre * m_pre ) current_2 )
|--
  EX (current: (@list Z)) (before: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ (i <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + size )) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ ((Zlength (current)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ (CanonicalGrid current ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before current m_pre i j size c (((r + 1 ) - i ) * size ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) current )
) \/
(
forall (n_pre: Z) (m_pre: Z) (current_2: (@list Z)) (before_2: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q >= (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before_2)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current_2)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before_2 )) (PreH23 : (CanonicalGrid current_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before_2 )) (PreH26 : (SettledSquareState before_2 n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before_2 current_2 m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  TT && emp 
|--
  EX (before: (@list Z)),
  “ (i <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + size )) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before current_2 m_pre i j size c (((r + 1 ) - i ) * size ) ) ”
  &&  emp
).

Definition solver_entail_wit_22_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current_2: (@list Z)) (before_2: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q < (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before_2)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current_2)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before_2 )) (PreH23 : (CanonicalGrid current_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before_2 )) (PreH26 : (SettledSquareState before_2 n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before_2 current_2 m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  (CharArray.full g_pre (n_pre * m_pre ) (replace_Znth (((r * m_pre ) + q )) (c) (current_2)) )
|--
  EX (current: (@list Z)) (before: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ (i <= r) ”
  &&  “ (r < (i + size )) ”
  &&  “ (j <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (j + size )) ”
  &&  “ (((q + 1 ) < (j + size )) -> ((0 <= ((r * m_pre ) + (q + 1 ) )) /\ (((r * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ ((Zlength (current)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ (CanonicalGrid current ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + ((q + 1 ) - j ) ) ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) current )
) \/
(
forall (n_pre: Z) (m_pre: Z) (current_2: (@list Z)) (before_2: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q < (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before_2)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current_2)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before_2 )) (PreH23 : (CanonicalGrid current_2 )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before_2) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before_2 )) (PreH26 : (SettledSquareState before_2 n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before_2 current_2 m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  TT && emp 
|--
  EX (before: (@list Z)),
  “ (j <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= (j + size )) ”
  &&  “ (((q + 1 ) < (j + size )) -> ((0 <= ((r * m_pre ) + (q + 1 ) )) /\ (((r * m_pre ) + (q + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ ((Zlength ((replace_Znth (((r * m_pre ) + q )) (c) (current_2)))) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ (CanonicalGrid (replace_Znth (((r * m_pre ) + q )) (c) (current_2)) ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before (replace_Znth (((r * m_pre ) + q )) (c) (current_2)) m_pre i j size c (((r - i ) * size ) + ((q + 1 ) - j ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_23 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i + 1 ) * m_pre ) grid ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )),
  TT && emp 
|--
  “ (GreedyPlacementTrace n_pre m_pre ((i + 1 ) * m_pre ) grid_2 ) ”
  &&  emp
).

Definition solver_entail_wit_23_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid_2 )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid_2 )),
  (GreedyPlacementTrace n_pre m_pre ((i + 1 ) * m_pre ) grid_2 )
.

Definition solver_entail_wit_24_colour_found :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (r >= (i + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r <= (i + size ))) (PreH17 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH18 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid before )) (PreH20 : (CanonicalGrid current )) (PreH21 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH23 : (SettledSquareState before n_pre m_pre i j c size )) (PreH24 : (PaintRectanglePrefix before current m_pre i j size c ((r - i ) * size ) )),
  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= m_pre) ”
  &&  “ (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + (j + 1 ) ) grid ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (current: (@list Z)) (before: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (r >= (i + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r <= (i + size ))) (PreH17 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH18 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid before )) (PreH20 : (CanonicalGrid current )) (PreH21 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH23 : (SettledSquareState before n_pre m_pre i j c size )) (PreH24 : (PaintRectanglePrefix before current m_pre i j size c ((r - i ) * size ) )),
  TT && emp 
|--
  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + (j + 1 ) ) current ) ”
  &&  “ (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_24_colour_found_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (current: (@list Z)) (before: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (r >= (i + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r <= (i + size ))) (PreH17 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH18 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid before )) (PreH20 : (CanonicalGrid current )) (PreH21 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH23 : (SettledSquareState before n_pre m_pre i j c size )) (PreH24 : (PaintRectanglePrefix before current m_pre i j size c ((r - i ) * size ) )),
  (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + (j + 1 ) ) current )
.

Definition solver_entail_wit_24_colour_found_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (current: (@list Z)) (before: (@list Z)) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (r >= (i + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r <= (i + size ))) (PreH17 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH18 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH19 : (CanonicalGrid before )) (PreH20 : (CanonicalGrid current )) (PreH21 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH23 : (SettledSquareState before n_pre m_pre i j c size )) (PreH24 : (PaintRectanglePrefix before current m_pre i j size c ((r - i ) * size ) )),
  (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre ))))
.

Definition solver_entail_wit_25 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH10 : (CanonicalGrid grid_2 )) (PreH11 : (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid_2 )),
  (CharArray.full g_pre (n_pre * m_pre ) grid_2 )
|--
  EX (grid: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= m_pre) ”
  &&  “ (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + (j + 1 ) ) grid ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH10 : (CanonicalGrid grid_2 )) (PreH11 : (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid_2 )),
  TT && emp 
|--
  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + (j + 1 ) ) grid_2 ) ”
  &&  “ (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre )))) ”
  &&  emp
).

Definition solver_entail_wit_25_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH10 : (CanonicalGrid grid_2 )) (PreH11 : (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid_2 )),
  (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + (j + 1 ) ) grid_2 )
.

Definition solver_entail_wit_25_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (grid_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j < m_pre)) (PreH9 : ((Zlength (grid_2)) = (n_pre * m_pre ))) (PreH10 : (CanonicalGrid grid_2 )) (PreH11 : (GreedyPlacementTrace n_pre m_pre (((i * m_pre ) + j ) + 1 ) grid_2 )),
  (((j + 1 ) < m_pre) -> ((0 <= ((i * m_pre ) + (j + 1 ) )) /\ (((i * m_pre ) + (j + 1 ) ) < (n_pre * m_pre ))))
.

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH9 : (CanonicalGrid grid )) (PreH10 : (GreedyPlacementTrace n_pre m_pre (i * m_pre ) grid )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  EX (out: (@list (@list Z))),
  “ (Spec n_pre m_pre out ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) (concat (out)) )
) \/
(
forall (n_pre: Z) (m_pre: Z) (grid: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH9 : (CanonicalGrid grid )) (PreH10 : (GreedyPlacementTrace n_pre m_pre (i * m_pre ) grid )),
  TT && emp 
|--
  EX (out: (@list (@list Z))),
  “ (grid = (concat (out))) ”
  &&  “ (Spec n_pre m_pre out ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (flat: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (flat)) = (n_pre * m_pre ))) (PreH12 : (ZeroPrefix flat ((i * m_pre ) + j ) )),
  (CharArray.full g_pre (n_pre * m_pre ) flat )
|--
  “ (j < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= m_pre) ”
  &&  “ ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (flat)) = (n_pre * m_pre )) ”
  &&  “ (ZeroPrefix flat ((i * m_pre ) + j ) ) ”
  &&  (((g_pre + (((i * m_pre ) + j ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i g_pre ((i * m_pre ) + j ) 0 (n_pre * m_pre ) flat )
.

Definition solver_partial_solve_wit_2 :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= m_pre)) (PreH10 : ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre ))))) (PreH11 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH12 : (CanonicalGrid grid )) (PreH13 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (j < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= m_pre) ”
  &&  “ ((j < m_pre) -> ((0 <= ((i * m_pre ) + j )) /\ (((i * m_pre ) + j ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  (((g_pre + (((i * m_pre ) + j ) * sizeof(CHAR)))) # Char  |-> (Znth ((i * m_pre ) + j ) grid 0))
  **  (CharArray.missing_i g_pre ((i * m_pre ) + j ) 0 (n_pre * m_pre ) grid )
.

Definition solver_partial_solve_wit_3_pure :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (PreH1 : (t <= 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t)) (PreH11 : (t <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH17 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid n_pre m_pre i j 1 available )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Char  |-> t)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 101) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 90) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
.

Definition solver_partial_solve_wit_3_aux :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (available: Z) (grid: (@list Z)) (c: Z) (t: Z) (j: Z) (i: Z) (PreH1 : (t <= 90)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= t)) (PreH11 : (t <= 91)) (PreH12 : (c = 0)) (PreH13 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH14 : (CanonicalGrid grid )) (PreH15 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH16 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH17 : (NoPlaceableColorBelow grid n_pre m_pre i j t )) (PreH18 : (65 <= available)) (PreH19 : (available <= 69)) (PreH20 : (CanPlace grid n_pre m_pre i j 1 available )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 101) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 90) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (t <= 90) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= t) ”
  &&  “ (t <= 91) ”
  &&  “ (c = 0) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (NoPlaceableColorBelow grid n_pre m_pre i j t ) ”
  &&  “ (65 <= available) ”
  &&  “ (available <= 69) ”
  &&  “ (CanPlace grid n_pre m_pre i j 1 available ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4_colour_found_pure :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH19 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid n_pre m_pre i j c size )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (1 <= (size + 1 )) ”
  &&  “ ((size + 1 ) <= 101) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
.

Definition solver_partial_solve_wit_4_colour_found_aux :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : ((j + size ) < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH16 : (CanonicalGrid grid )) (PreH17 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH18 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH19 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH20 : (GreedySideState grid n_pre m_pre i j c size )) (PreH21 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (1 <= (size + 1 )) ”
  &&  “ ((size + 1 ) <= 101) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_partial_solve_wit_4_colour_found := solver_partial_solve_wit_4_colour_found_pure -> solver_partial_solve_wit_4_colour_found_aux.

Definition solver_partial_solve_wit_5_colour_found_pure :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (CanPlace grid n_pre m_pre i j (size + 1 ) c )) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Char  |-> c)
  **  ((( &( "size" ) )) # Int  |-> size)
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= (j + size )) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
.

Definition solver_partial_solve_wit_5_colour_found_aux :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (grid: (@list Z)) (size: Z) (c: Z) (j: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (CanPlace grid n_pre m_pre i j (size + 1 ) c )) (PreH4 : (CanonicalGrid grid )) (PreH5 : ((j + size ) < m_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < m_pre)) (PreH14 : (65 <= c)) (PreH15 : (c <= 90)) (PreH16 : (1 <= size)) (PreH17 : (size <= (n_pre - i ))) (PreH18 : (size <= (m_pre - j ))) (PreH19 : ((Zlength (grid)) = (n_pre * m_pre ))) (PreH20 : (CanonicalGrid grid )) (PreH21 : ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0)) (PreH22 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid )) (PreH23 : (LeastLegalColor grid n_pre m_pre i j 0 c )) (PreH24 : (GreedySideState grid n_pre m_pre i j c size )) (PreH25 : (ChosenSquareState grid n_pre m_pre i j c size )),
  (CharArray.full g_pre (n_pre * m_pre ) grid )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= (j + size )) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = 1) ”
  &&  “ (CanPlace grid n_pre m_pre i j (size + 1 ) c ) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((j + size ) < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ ((Zlength (grid)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid grid ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (grid) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) grid ) ”
  &&  “ (LeastLegalColor grid n_pre m_pre i j 0 c ) ”
  &&  “ (GreedySideState grid n_pre m_pre i j c size ) ”
  &&  “ (ChosenSquareState grid n_pre m_pre i j c size ) ”
  &&  (CharArray.full g_pre (n_pre * m_pre ) grid )
.

Definition solver_partial_solve_wit_5_colour_found := solver_partial_solve_wit_5_colour_found_pure -> solver_partial_solve_wit_5_colour_found_aux.

Definition solver_partial_solve_wit_6_colour_found :=
forall (n_pre: Z) (m_pre: Z) (g_pre: Z) (current: (@list Z)) (before: (@list Z)) (q: Z) (r: Z) (size: Z) (c: Z) (j: Z) (i: Z) (PreH1 : (q < (j + size ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j < m_pre)) (PreH10 : (65 <= c)) (PreH11 : (c <= 90)) (PreH12 : (1 <= size)) (PreH13 : (size <= (n_pre - i ))) (PreH14 : (size <= (m_pre - j ))) (PreH15 : (i <= r)) (PreH16 : (r < (i + size ))) (PreH17 : (j <= q)) (PreH18 : (q <= (j + size ))) (PreH19 : ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre ))))) (PreH20 : ((Zlength (before)) = (n_pre * m_pre ))) (PreH21 : ((Zlength (current)) = (n_pre * m_pre ))) (PreH22 : (CanonicalGrid before )) (PreH23 : (CanonicalGrid current )) (PreH24 : ((Znth (((i * m_pre ) + j )) (before) (0)) = 0)) (PreH25 : (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before )) (PreH26 : (SettledSquareState before n_pre m_pre i j c size )) (PreH27 : (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (q - j ) ) )),
  (CharArray.full g_pre (n_pre * m_pre ) current )
|--
  “ (q < (j + size )) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 100) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j < m_pre) ”
  &&  “ (65 <= c) ”
  &&  “ (c <= 90) ”
  &&  “ (1 <= size) ”
  &&  “ (size <= (n_pre - i )) ”
  &&  “ (size <= (m_pre - j )) ”
  &&  “ (i <= r) ”
  &&  “ (r < (i + size )) ”
  &&  “ (j <= q) ”
  &&  “ (q <= (j + size )) ”
  &&  “ ((q < (j + size )) -> ((0 <= ((r * m_pre ) + q )) /\ (((r * m_pre ) + q ) < (n_pre * m_pre )))) ”
  &&  “ ((Zlength (before)) = (n_pre * m_pre )) ”
  &&  “ ((Zlength (current)) = (n_pre * m_pre )) ”
  &&  “ (CanonicalGrid before ) ”
  &&  “ (CanonicalGrid current ) ”
  &&  “ ((Znth (((i * m_pre ) + j )) (before) (0)) = 0) ”
  &&  “ (GreedyPlacementTrace n_pre m_pre ((i * m_pre ) + j ) before ) ”
  &&  “ (SettledSquareState before n_pre m_pre i j c size ) ”
  &&  “ (PaintRectanglePrefix before current m_pre i j size c (((r - i ) * size ) + (q - j ) ) ) ”
  &&  (((g_pre + (((r * m_pre ) + q ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i g_pre ((r * m_pre ) + q ) 0 (n_pre * m_pre ) current )
.

Module Type VC_Correct.


Axiom proof_of_conflicts_safety_wit_1 : conflicts_safety_wit_1.
Axiom proof_of_conflicts_safety_wit_2 : conflicts_safety_wit_2.
Axiom proof_of_conflicts_safety_wit_3 : conflicts_safety_wit_3.
Axiom proof_of_conflicts_safety_wit_4 : conflicts_safety_wit_4.
Axiom proof_of_conflicts_safety_wit_5 : conflicts_safety_wit_5.
Axiom proof_of_conflicts_safety_wit_6 : conflicts_safety_wit_6.
Axiom proof_of_conflicts_safety_wit_7 : conflicts_safety_wit_7.
Axiom proof_of_conflicts_safety_wit_8 : conflicts_safety_wit_8.
Axiom proof_of_conflicts_safety_wit_9 : conflicts_safety_wit_9.
Axiom proof_of_conflicts_safety_wit_10 : conflicts_safety_wit_10.
Axiom proof_of_conflicts_safety_wit_11 : conflicts_safety_wit_11.
Axiom proof_of_conflicts_safety_wit_12 : conflicts_safety_wit_12.
Axiom proof_of_conflicts_safety_wit_13 : conflicts_safety_wit_13.
Axiom proof_of_conflicts_safety_wit_14 : conflicts_safety_wit_14.
Axiom proof_of_conflicts_safety_wit_15 : conflicts_safety_wit_15.
Axiom proof_of_conflicts_safety_wit_16 : conflicts_safety_wit_16.
Axiom proof_of_conflicts_safety_wit_17 : conflicts_safety_wit_17.
Axiom proof_of_conflicts_safety_wit_18 : conflicts_safety_wit_18.
Axiom proof_of_conflicts_safety_wit_19 : conflicts_safety_wit_19.
Axiom proof_of_conflicts_safety_wit_20 : conflicts_safety_wit_20.
Axiom proof_of_conflicts_safety_wit_21 : conflicts_safety_wit_21.
Axiom proof_of_conflicts_safety_wit_22 : conflicts_safety_wit_22.
Axiom proof_of_conflicts_safety_wit_23 : conflicts_safety_wit_23.
Axiom proof_of_conflicts_safety_wit_24 : conflicts_safety_wit_24.
Axiom proof_of_conflicts_safety_wit_25 : conflicts_safety_wit_25.
Axiom proof_of_conflicts_safety_wit_26 : conflicts_safety_wit_26.
Axiom proof_of_conflicts_safety_wit_27 : conflicts_safety_wit_27.
Axiom proof_of_conflicts_safety_wit_28 : conflicts_safety_wit_28.
Axiom proof_of_conflicts_safety_wit_29 : conflicts_safety_wit_29.
Axiom proof_of_conflicts_safety_wit_30 : conflicts_safety_wit_30.
Axiom proof_of_conflicts_safety_wit_31 : conflicts_safety_wit_31.
Axiom proof_of_conflicts_safety_wit_32 : conflicts_safety_wit_32.
Axiom proof_of_conflicts_safety_wit_33 : conflicts_safety_wit_33.
Axiom proof_of_conflicts_safety_wit_34 : conflicts_safety_wit_34.
Axiom proof_of_conflicts_safety_wit_35 : conflicts_safety_wit_35.
Axiom proof_of_conflicts_safety_wit_36 : conflicts_safety_wit_36.
Axiom proof_of_conflicts_safety_wit_37 : conflicts_safety_wit_37.
Axiom proof_of_conflicts_safety_wit_38 : conflicts_safety_wit_38.
Axiom proof_of_conflicts_safety_wit_39 : conflicts_safety_wit_39.
Axiom proof_of_conflicts_safety_wit_40 : conflicts_safety_wit_40.
Axiom proof_of_conflicts_safety_wit_41 : conflicts_safety_wit_41.
Axiom proof_of_conflicts_safety_wit_42 : conflicts_safety_wit_42.
Axiom proof_of_conflicts_safety_wit_43 : conflicts_safety_wit_43.
Axiom proof_of_conflicts_safety_wit_44 : conflicts_safety_wit_44.
Axiom proof_of_conflicts_safety_wit_45 : conflicts_safety_wit_45.
Axiom proof_of_conflicts_safety_wit_46 : conflicts_safety_wit_46.
Axiom proof_of_conflicts_safety_wit_47 : conflicts_safety_wit_47.
Axiom proof_of_conflicts_safety_wit_48 : conflicts_safety_wit_48.
Axiom proof_of_conflicts_safety_wit_49 : conflicts_safety_wit_49.
Axiom proof_of_conflicts_safety_wit_50 : conflicts_safety_wit_50.
Axiom proof_of_conflicts_safety_wit_51 : conflicts_safety_wit_51.
Axiom proof_of_conflicts_safety_wit_52 : conflicts_safety_wit_52.
Axiom proof_of_conflicts_safety_wit_53 : conflicts_safety_wit_53.
Axiom proof_of_conflicts_safety_wit_54 : conflicts_safety_wit_54.
Axiom proof_of_conflicts_safety_wit_55 : conflicts_safety_wit_55.
Axiom proof_of_conflicts_safety_wit_56 : conflicts_safety_wit_56.
Axiom proof_of_conflicts_safety_wit_57 : conflicts_safety_wit_57.
Axiom proof_of_conflicts_safety_wit_58 : conflicts_safety_wit_58.
Axiom proof_of_conflicts_safety_wit_59 : conflicts_safety_wit_59.
Axiom proof_of_conflicts_safety_wit_60 : conflicts_safety_wit_60.
Axiom proof_of_conflicts_safety_wit_61 : conflicts_safety_wit_61.
Axiom proof_of_conflicts_safety_wit_62 : conflicts_safety_wit_62.
Axiom proof_of_conflicts_safety_wit_63 : conflicts_safety_wit_63.
Axiom proof_of_conflicts_safety_wit_64 : conflicts_safety_wit_64.
Axiom proof_of_conflicts_safety_wit_65 : conflicts_safety_wit_65.
Axiom proof_of_conflicts_safety_wit_66 : conflicts_safety_wit_66.
Axiom proof_of_conflicts_safety_wit_67 : conflicts_safety_wit_67.
Axiom proof_of_conflicts_safety_wit_68 : conflicts_safety_wit_68.
Axiom proof_of_conflicts_safety_wit_69 : conflicts_safety_wit_69.
Axiom proof_of_conflicts_safety_wit_70 : conflicts_safety_wit_70.
Axiom proof_of_conflicts_safety_wit_71 : conflicts_safety_wit_71.
Axiom proof_of_conflicts_safety_wit_72 : conflicts_safety_wit_72.
Axiom proof_of_conflicts_safety_wit_73 : conflicts_safety_wit_73.
Axiom proof_of_conflicts_safety_wit_74 : conflicts_safety_wit_74.
Axiom proof_of_conflicts_safety_wit_75 : conflicts_safety_wit_75.
Axiom proof_of_conflicts_safety_wit_76 : conflicts_safety_wit_76.
Axiom proof_of_conflicts_safety_wit_77 : conflicts_safety_wit_77.
Axiom proof_of_conflicts_safety_wit_78 : conflicts_safety_wit_78.
Axiom proof_of_conflicts_safety_wit_79 : conflicts_safety_wit_79.
Axiom proof_of_conflicts_safety_wit_80 : conflicts_safety_wit_80.
Axiom proof_of_conflicts_safety_wit_81 : conflicts_safety_wit_81.
Axiom proof_of_conflicts_safety_wit_82 : conflicts_safety_wit_82.
Axiom proof_of_conflicts_safety_wit_83 : conflicts_safety_wit_83.
Axiom proof_of_conflicts_safety_wit_84 : conflicts_safety_wit_84.
Axiom proof_of_conflicts_safety_wit_85 : conflicts_safety_wit_85.
Axiom proof_of_conflicts_safety_wit_86 : conflicts_safety_wit_86.
Axiom proof_of_conflicts_safety_wit_87 : conflicts_safety_wit_87.
Axiom proof_of_conflicts_safety_wit_88 : conflicts_safety_wit_88.
Axiom proof_of_conflicts_safety_wit_89 : conflicts_safety_wit_89.
Axiom proof_of_conflicts_safety_wit_90 : conflicts_safety_wit_90.
Axiom proof_of_conflicts_safety_wit_91 : conflicts_safety_wit_91.
Axiom proof_of_conflicts_safety_wit_92 : conflicts_safety_wit_92.
Axiom proof_of_conflicts_safety_wit_93 : conflicts_safety_wit_93.
Axiom proof_of_conflicts_safety_wit_94 : conflicts_safety_wit_94.
Axiom proof_of_conflicts_safety_wit_95 : conflicts_safety_wit_95.
Axiom proof_of_conflicts_safety_wit_96 : conflicts_safety_wit_96.
Axiom proof_of_conflicts_safety_wit_97 : conflicts_safety_wit_97.
Axiom proof_of_conflicts_safety_wit_98 : conflicts_safety_wit_98.
Axiom proof_of_conflicts_safety_wit_99 : conflicts_safety_wit_99.
Axiom proof_of_conflicts_safety_wit_100 : conflicts_safety_wit_100.
Axiom proof_of_conflicts_safety_wit_101 : conflicts_safety_wit_101.
Axiom proof_of_conflicts_safety_wit_102 : conflicts_safety_wit_102.
Axiom proof_of_conflicts_safety_wit_103 : conflicts_safety_wit_103.
Axiom proof_of_conflicts_safety_wit_104 : conflicts_safety_wit_104.
Axiom proof_of_conflicts_safety_wit_105 : conflicts_safety_wit_105.
Axiom proof_of_conflicts_safety_wit_106 : conflicts_safety_wit_106.
Axiom proof_of_conflicts_safety_wit_107 : conflicts_safety_wit_107.
Axiom proof_of_conflicts_safety_wit_108 : conflicts_safety_wit_108.
Axiom proof_of_conflicts_safety_wit_109 : conflicts_safety_wit_109.
Axiom proof_of_conflicts_safety_wit_110 : conflicts_safety_wit_110.
Axiom proof_of_conflicts_safety_wit_111 : conflicts_safety_wit_111.
Axiom proof_of_conflicts_safety_wit_112 : conflicts_safety_wit_112.
Axiom proof_of_conflicts_safety_wit_113 : conflicts_safety_wit_113.
Axiom proof_of_conflicts_safety_wit_114 : conflicts_safety_wit_114.
Axiom proof_of_conflicts_safety_wit_115 : conflicts_safety_wit_115.
Axiom proof_of_conflicts_safety_wit_116 : conflicts_safety_wit_116.
Axiom proof_of_conflicts_safety_wit_117 : conflicts_safety_wit_117.
Axiom proof_of_conflicts_safety_wit_118 : conflicts_safety_wit_118.
Axiom proof_of_conflicts_safety_wit_119 : conflicts_safety_wit_119.
Axiom proof_of_conflicts_safety_wit_120 : conflicts_safety_wit_120.
Axiom proof_of_conflicts_safety_wit_121 : conflicts_safety_wit_121.
Axiom proof_of_conflicts_safety_wit_122 : conflicts_safety_wit_122.
Axiom proof_of_conflicts_safety_wit_123 : conflicts_safety_wit_123.
Axiom proof_of_conflicts_safety_wit_124 : conflicts_safety_wit_124.
Axiom proof_of_conflicts_safety_wit_125 : conflicts_safety_wit_125.
Axiom proof_of_conflicts_safety_wit_126 : conflicts_safety_wit_126.
Axiom proof_of_conflicts_safety_wit_127 : conflicts_safety_wit_127.
Axiom proof_of_conflicts_safety_wit_128 : conflicts_safety_wit_128.
Axiom proof_of_conflicts_safety_wit_129 : conflicts_safety_wit_129.
Axiom proof_of_conflicts_safety_wit_130 : conflicts_safety_wit_130.
Axiom proof_of_conflicts_safety_wit_131 : conflicts_safety_wit_131.
Axiom proof_of_conflicts_safety_wit_132 : conflicts_safety_wit_132.
Axiom proof_of_conflicts_safety_wit_133 : conflicts_safety_wit_133.
Axiom proof_of_conflicts_safety_wit_134 : conflicts_safety_wit_134.
Axiom proof_of_conflicts_safety_wit_135 : conflicts_safety_wit_135.
Axiom proof_of_conflicts_safety_wit_136 : conflicts_safety_wit_136.
Axiom proof_of_conflicts_entail_wit_1 : conflicts_entail_wit_1.
Axiom proof_of_conflicts_return_wit_1 : conflicts_return_wit_1.
Axiom proof_of_conflicts_return_wit_2 : conflicts_return_wit_2.
Axiom proof_of_conflicts_return_wit_3 : conflicts_return_wit_3.
Axiom proof_of_conflicts_return_wit_4 : conflicts_return_wit_4.
Axiom proof_of_conflicts_return_wit_5 : conflicts_return_wit_5.
Axiom proof_of_conflicts_return_wit_6 : conflicts_return_wit_6.
Axiom proof_of_conflicts_return_wit_7 : conflicts_return_wit_7.
Axiom proof_of_conflicts_return_wit_8 : conflicts_return_wit_8.
Axiom proof_of_conflicts_return_wit_9 : conflicts_return_wit_9.
Axiom proof_of_conflicts_return_wit_10 : conflicts_return_wit_10.
Axiom proof_of_conflicts_return_wit_11 : conflicts_return_wit_11.
Axiom proof_of_conflicts_return_wit_12 : conflicts_return_wit_12.
Axiom proof_of_conflicts_return_wit_13 : conflicts_return_wit_13.
Axiom proof_of_conflicts_return_wit_14 : conflicts_return_wit_14.
Axiom proof_of_conflicts_return_wit_15 : conflicts_return_wit_15.
Axiom proof_of_conflicts_return_wit_16 : conflicts_return_wit_16.
Axiom proof_of_conflicts_return_wit_17 : conflicts_return_wit_17.
Axiom proof_of_conflicts_return_wit_18 : conflicts_return_wit_18.
Axiom proof_of_conflicts_return_wit_19 : conflicts_return_wit_19.
Axiom proof_of_conflicts_return_wit_20 : conflicts_return_wit_20.
Axiom proof_of_conflicts_return_wit_21 : conflicts_return_wit_21.
Axiom proof_of_conflicts_return_wit_22 : conflicts_return_wit_22.
Axiom proof_of_conflicts_return_wit_23 : conflicts_return_wit_23.
Axiom proof_of_conflicts_return_wit_24 : conflicts_return_wit_24.
Axiom proof_of_conflicts_return_wit_25 : conflicts_return_wit_25.
Axiom proof_of_conflicts_return_wit_26 : conflicts_return_wit_26.
Axiom proof_of_conflicts_return_wit_27 : conflicts_return_wit_27.
Axiom proof_of_conflicts_return_wit_28 : conflicts_return_wit_28.
Axiom proof_of_conflicts_return_wit_29 : conflicts_return_wit_29.
Axiom proof_of_conflicts_return_wit_30 : conflicts_return_wit_30.
Axiom proof_of_conflicts_return_wit_31 : conflicts_return_wit_31.
Axiom proof_of_conflicts_return_wit_32 : conflicts_return_wit_32.
Axiom proof_of_conflicts_return_wit_33 : conflicts_return_wit_33.
Axiom proof_of_conflicts_return_wit_34 : conflicts_return_wit_34.
Axiom proof_of_conflicts_return_wit_35 : conflicts_return_wit_35.
Axiom proof_of_conflicts_return_wit_36 : conflicts_return_wit_36.
Axiom proof_of_conflicts_return_wit_37 : conflicts_return_wit_37.
Axiom proof_of_conflicts_return_wit_38 : conflicts_return_wit_38.
Axiom proof_of_conflicts_return_wit_39 : conflicts_return_wit_39.
Axiom proof_of_conflicts_return_wit_40 : conflicts_return_wit_40.
Axiom proof_of_conflicts_return_wit_41 : conflicts_return_wit_41.
Axiom proof_of_conflicts_return_wit_42 : conflicts_return_wit_42.
Axiom proof_of_conflicts_return_wit_43 : conflicts_return_wit_43.
Axiom proof_of_conflicts_return_wit_44 : conflicts_return_wit_44.
Axiom proof_of_conflicts_return_wit_45 : conflicts_return_wit_45.
Axiom proof_of_conflicts_return_wit_46 : conflicts_return_wit_46.
Axiom proof_of_conflicts_return_wit_47 : conflicts_return_wit_47.
Axiom proof_of_conflicts_return_wit_48 : conflicts_return_wit_48.
Axiom proof_of_conflicts_return_wit_49 : conflicts_return_wit_49.
Axiom proof_of_conflicts_return_wit_50 : conflicts_return_wit_50.
Axiom proof_of_conflicts_return_wit_51 : conflicts_return_wit_51.
Axiom proof_of_conflicts_return_wit_52 : conflicts_return_wit_52.
Axiom proof_of_conflicts_return_wit_53 : conflicts_return_wit_53.
Axiom proof_of_conflicts_return_wit_54 : conflicts_return_wit_54.
Axiom proof_of_conflicts_return_wit_55 : conflicts_return_wit_55.
Axiom proof_of_conflicts_partial_solve_wit_1 : conflicts_partial_solve_wit_1.
Axiom proof_of_conflicts_partial_solve_wit_2 : conflicts_partial_solve_wit_2.
Axiom proof_of_conflicts_partial_solve_wit_3 : conflicts_partial_solve_wit_3.
Axiom proof_of_conflicts_partial_solve_wit_4 : conflicts_partial_solve_wit_4.
Axiom proof_of_conflicts_partial_solve_wit_5 : conflicts_partial_solve_wit_5.
Axiom proof_of_conflicts_partial_solve_wit_6 : conflicts_partial_solve_wit_6.
Axiom proof_of_conflicts_partial_solve_wit_7 : conflicts_partial_solve_wit_7.
Axiom proof_of_conflicts_partial_solve_wit_8 : conflicts_partial_solve_wit_8.
Axiom proof_of_conflicts_partial_solve_wit_9 : conflicts_partial_solve_wit_9.
Axiom proof_of_conflicts_partial_solve_wit_10 : conflicts_partial_solve_wit_10.
Axiom proof_of_conflicts_partial_solve_wit_11 : conflicts_partial_solve_wit_11.
Axiom proof_of_conflicts_partial_solve_wit_12 : conflicts_partial_solve_wit_12.
Axiom proof_of_conflicts_partial_solve_wit_13 : conflicts_partial_solve_wit_13.
Axiom proof_of_conflicts_partial_solve_wit_14 : conflicts_partial_solve_wit_14.
Axiom proof_of_conflicts_partial_solve_wit_15 : conflicts_partial_solve_wit_15.
Axiom proof_of_cell_colour_safety_wit_1 : cell_colour_safety_wit_1.
Axiom proof_of_cell_colour_safety_wit_2 : cell_colour_safety_wit_2.
Axiom proof_of_cell_colour_safety_wit_3 : cell_colour_safety_wit_3.
Axiom proof_of_cell_colour_safety_wit_4 : cell_colour_safety_wit_4.
Axiom proof_of_cell_colour_safety_wit_5 : cell_colour_safety_wit_5.
Axiom proof_of_cell_colour_safety_wit_6 : cell_colour_safety_wit_6.
Axiom proof_of_cell_colour_entail_wit_1 : cell_colour_entail_wit_1.
Axiom proof_of_cell_colour_entail_wit_2 : cell_colour_entail_wit_2.
Axiom proof_of_cell_colour_return_wit_1 : cell_colour_return_wit_1.
Axiom proof_of_cell_colour_return_wit_2 : cell_colour_return_wit_2.
Axiom proof_of_cell_colour_partial_solve_wit_1_pure : cell_colour_partial_solve_wit_1_pure.
Axiom proof_of_cell_colour_partial_solve_wit_1 : cell_colour_partial_solve_wit_1.
Axiom proof_of_can_place_safety_wit_1 : can_place_safety_wit_1.
Axiom proof_of_can_place_safety_wit_2 : can_place_safety_wit_2.
Axiom proof_of_can_place_safety_wit_3 : can_place_safety_wit_3.
Axiom proof_of_can_place_safety_wit_4 : can_place_safety_wit_4.
Axiom proof_of_can_place_safety_wit_5 : can_place_safety_wit_5.
Axiom proof_of_can_place_safety_wit_6 : can_place_safety_wit_6.
Axiom proof_of_can_place_safety_wit_7 : can_place_safety_wit_7.
Axiom proof_of_can_place_safety_wit_8 : can_place_safety_wit_8.
Axiom proof_of_can_place_safety_wit_9 : can_place_safety_wit_9.
Axiom proof_of_can_place_safety_wit_10 : can_place_safety_wit_10.
Axiom proof_of_can_place_safety_wit_11 : can_place_safety_wit_11.
Axiom proof_of_can_place_safety_wit_12 : can_place_safety_wit_12.
Axiom proof_of_can_place_safety_wit_13 : can_place_safety_wit_13.
Axiom proof_of_can_place_safety_wit_14 : can_place_safety_wit_14.
Axiom proof_of_can_place_safety_wit_15 : can_place_safety_wit_15.
Axiom proof_of_can_place_safety_wit_16 : can_place_safety_wit_16.
Axiom proof_of_can_place_safety_wit_17 : can_place_safety_wit_17.
Axiom proof_of_can_place_safety_wit_18 : can_place_safety_wit_18.
Axiom proof_of_can_place_safety_wit_19 : can_place_safety_wit_19.
Axiom proof_of_can_place_safety_wit_20 : can_place_safety_wit_20.
Axiom proof_of_can_place_safety_wit_21 : can_place_safety_wit_21.
Axiom proof_of_can_place_safety_wit_22 : can_place_safety_wit_22.
Axiom proof_of_can_place_safety_wit_23 : can_place_safety_wit_23.
Axiom proof_of_can_place_safety_wit_24 : can_place_safety_wit_24.
Axiom proof_of_can_place_safety_wit_25 : can_place_safety_wit_25.
Axiom proof_of_can_place_safety_wit_26 : can_place_safety_wit_26.
Axiom proof_of_can_place_safety_wit_27 : can_place_safety_wit_27.
Axiom proof_of_can_place_safety_wit_28 : can_place_safety_wit_28.
Axiom proof_of_can_place_safety_wit_29 : can_place_safety_wit_29.
Axiom proof_of_can_place_safety_wit_30 : can_place_safety_wit_30.
Axiom proof_of_can_place_safety_wit_31 : can_place_safety_wit_31.
Axiom proof_of_can_place_safety_wit_32 : can_place_safety_wit_32.
Axiom proof_of_can_place_safety_wit_33 : can_place_safety_wit_33.
Axiom proof_of_can_place_safety_wit_34 : can_place_safety_wit_34.
Axiom proof_of_can_place_safety_wit_35 : can_place_safety_wit_35.
Axiom proof_of_can_place_safety_wit_36 : can_place_safety_wit_36.
Axiom proof_of_can_place_safety_wit_37 : can_place_safety_wit_37.
Axiom proof_of_can_place_safety_wit_38 : can_place_safety_wit_38.
Axiom proof_of_can_place_safety_wit_39 : can_place_safety_wit_39.
Axiom proof_of_can_place_safety_wit_40 : can_place_safety_wit_40.
Axiom proof_of_can_place_safety_wit_41 : can_place_safety_wit_41.
Axiom proof_of_can_place_safety_wit_42 : can_place_safety_wit_42.
Axiom proof_of_can_place_safety_wit_43 : can_place_safety_wit_43.
Axiom proof_of_can_place_safety_wit_44 : can_place_safety_wit_44.
Axiom proof_of_can_place_safety_wit_45 : can_place_safety_wit_45.
Axiom proof_of_can_place_safety_wit_46 : can_place_safety_wit_46.
Axiom proof_of_can_place_safety_wit_47 : can_place_safety_wit_47.
Axiom proof_of_can_place_safety_wit_48 : can_place_safety_wit_48.
Axiom proof_of_can_place_safety_wit_49 : can_place_safety_wit_49.
Axiom proof_of_can_place_safety_wit_50 : can_place_safety_wit_50.
Axiom proof_of_can_place_safety_wit_51 : can_place_safety_wit_51.
Axiom proof_of_can_place_safety_wit_52 : can_place_safety_wit_52.
Axiom proof_of_can_place_safety_wit_53 : can_place_safety_wit_53.
Axiom proof_of_can_place_safety_wit_54 : can_place_safety_wit_54.
Axiom proof_of_can_place_entail_wit_1 : can_place_entail_wit_1.
Axiom proof_of_can_place_entail_wit_2 : can_place_entail_wit_2.
Axiom proof_of_can_place_entail_wit_3 : can_place_entail_wit_3.
Axiom proof_of_can_place_entail_wit_4 : can_place_entail_wit_4.
Axiom proof_of_can_place_entail_wit_5 : can_place_entail_wit_5.
Axiom proof_of_can_place_entail_wit_6_1 : can_place_entail_wit_6_1.
Axiom proof_of_can_place_entail_wit_6_2 : can_place_entail_wit_6_2.
Axiom proof_of_can_place_entail_wit_6_3 : can_place_entail_wit_6_3.
Axiom proof_of_can_place_entail_wit_6_4 : can_place_entail_wit_6_4.
Axiom proof_of_can_place_entail_wit_7 : can_place_entail_wit_7.
Axiom proof_of_can_place_entail_wit_8_1 : can_place_entail_wit_8_1.
Axiom proof_of_can_place_entail_wit_8_2 : can_place_entail_wit_8_2.
Axiom proof_of_can_place_entail_wit_8_3 : can_place_entail_wit_8_3.
Axiom proof_of_can_place_entail_wit_8_4 : can_place_entail_wit_8_4.
Axiom proof_of_can_place_return_wit_1 : can_place_return_wit_1.
Axiom proof_of_can_place_return_wit_2 : can_place_return_wit_2.
Axiom proof_of_can_place_return_wit_3 : can_place_return_wit_3.
Axiom proof_of_can_place_return_wit_4 : can_place_return_wit_4.
Axiom proof_of_can_place_return_wit_5 : can_place_return_wit_5.
Axiom proof_of_can_place_return_wit_6 : can_place_return_wit_6.
Axiom proof_of_can_place_return_wit_7 : can_place_return_wit_7.
Axiom proof_of_can_place_return_wit_8 : can_place_return_wit_8.
Axiom proof_of_can_place_return_wit_9 : can_place_return_wit_9.
Axiom proof_of_can_place_return_wit_10 : can_place_return_wit_10.
Axiom proof_of_can_place_partial_solve_wit_1 : can_place_partial_solve_wit_1.
Axiom proof_of_can_place_partial_solve_wit_2 : can_place_partial_solve_wit_2.
Axiom proof_of_can_place_partial_solve_wit_3 : can_place_partial_solve_wit_3.
Axiom proof_of_can_place_partial_solve_wit_4 : can_place_partial_solve_wit_4.
Axiom proof_of_can_place_partial_solve_wit_5 : can_place_partial_solve_wit_5.
Axiom proof_of_can_place_partial_solve_wit_6 : can_place_partial_solve_wit_6.
Axiom proof_of_can_place_partial_solve_wit_7 : can_place_partial_solve_wit_7.
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
Axiom proof_of_solver_safety_wit_20_colour_found : solver_safety_wit_20_colour_found.
Axiom proof_of_solver_safety_wit_21_colour_found : solver_safety_wit_21_colour_found.
Axiom proof_of_solver_safety_wit_22_colour_found : solver_safety_wit_22_colour_found.
Axiom proof_of_solver_safety_wit_23_colour_found : solver_safety_wit_23_colour_found.
Axiom proof_of_solver_safety_wit_24_colour_found : solver_safety_wit_24_colour_found.
Axiom proof_of_solver_safety_wit_25_colour_found : solver_safety_wit_25_colour_found.
Axiom proof_of_solver_safety_wit_26_colour_found : solver_safety_wit_26_colour_found.
Axiom proof_of_solver_safety_wit_27_colour_found : solver_safety_wit_27_colour_found.
Axiom proof_of_solver_safety_wit_28_colour_found : solver_safety_wit_28_colour_found.
Axiom proof_of_solver_safety_wit_29_colour_found : solver_safety_wit_29_colour_found.
Axiom proof_of_solver_safety_wit_30_colour_found : solver_safety_wit_30_colour_found.
Axiom proof_of_solver_safety_wit_31_colour_found : solver_safety_wit_31_colour_found.
Axiom proof_of_solver_safety_wit_32_colour_found : solver_safety_wit_32_colour_found.
Axiom proof_of_solver_safety_wit_33_colour_found : solver_safety_wit_33_colour_found.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35_colour_found : solver_safety_wit_35_colour_found.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2_colour_found : solver_entail_wit_12_2_colour_found.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_colour_found : solver_entail_wit_14_colour_found.
Axiom proof_of_solver_entail_wit_15_1_colour_found : solver_entail_wit_15_1_colour_found.
Axiom proof_of_solver_entail_wit_15_2_colour_found : solver_entail_wit_15_2_colour_found.
Axiom proof_of_solver_entail_wit_15_3_colour_found : solver_entail_wit_15_3_colour_found.
Axiom proof_of_solver_entail_wit_16_1_colour_found : solver_entail_wit_16_1_colour_found.
Axiom proof_of_solver_entail_wit_16_2_colour_found : solver_entail_wit_16_2_colour_found.
Axiom proof_of_solver_entail_wit_17_colour_found : solver_entail_wit_17_colour_found.
Axiom proof_of_solver_entail_wit_18_1_colour_found : solver_entail_wit_18_1_colour_found.
Axiom proof_of_solver_entail_wit_18_2_colour_found : solver_entail_wit_18_2_colour_found.
Axiom proof_of_solver_entail_wit_18_3_colour_found : solver_entail_wit_18_3_colour_found.
Axiom proof_of_solver_entail_wit_19_colour_found : solver_entail_wit_19_colour_found.
Axiom proof_of_solver_entail_wit_20_colour_found : solver_entail_wit_20_colour_found.
Axiom proof_of_solver_entail_wit_21_colour_found : solver_entail_wit_21_colour_found.
Axiom proof_of_solver_entail_wit_22_colour_found : solver_entail_wit_22_colour_found.
Axiom proof_of_solver_entail_wit_23 : solver_entail_wit_23.
Axiom proof_of_solver_entail_wit_24_colour_found : solver_entail_wit_24_colour_found.
Axiom proof_of_solver_entail_wit_25 : solver_entail_wit_25.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_colour_found_pure : solver_partial_solve_wit_4_colour_found_pure.
Axiom proof_of_solver_partial_solve_wit_4_colour_found : solver_partial_solve_wit_4_colour_found.
Axiom proof_of_solver_partial_solve_wit_5_colour_found_pure : solver_partial_solve_wit_5_colour_found_pure.
Axiom proof_of_solver_partial_solve_wit_5_colour_found : solver_partial_solve_wit_5_colour_found.
Axiom proof_of_solver_partial_solve_wit_6_colour_found : solver_partial_solve_wit_6_colour_found.

End VC_Correct.
