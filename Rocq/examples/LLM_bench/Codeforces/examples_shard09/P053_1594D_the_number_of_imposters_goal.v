From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (m_pre <= 500000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> ((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))))) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((((Znth i_2 comment_sources 0) = (fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 comment_targets 0) = (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 comment_kinds 0) = (snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))),
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs v )),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth (v) ((-1)) (hs)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((v + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs v )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_4 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs v )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs v )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  ((( &( "e" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((2 * i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition solver_safety_wit_7 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  ((( &( "e" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_8 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  ((( &( "v" ) )) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "u" ) )) # Int  |-> (Znth i comment_sources 0))
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_targets 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)))) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)))) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH15 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs v )),
  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (v) ((-1)) (cs)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((v + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH15 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs v )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_20 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH15 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs v )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH15 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs v )),
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_22 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH15 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs v )),
  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_23 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (s <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1 ))) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH16 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH17 : (ColourValues n_pre cs )) (PreH18 : (ParityRespected comments cs )) (PreH19 : (ColouredClosed comments cs )) (PreH20 : (MaxImpostersOn n_pre comments cs total )) (PreH21 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  ((( &( "top" ) )) # Int  |->_)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  ((( &( "top" ) )) # Int  |-> 0)
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_26 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (0) (s) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (s) (0) (cs)) )
  **  ((( &( "top" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ ((0 + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition solver_safety_wit_27 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  ((( &( "c1" ) )) # Int  |->_)
  **  ((( &( "c0" ) )) # Int  |-> 0)
  **  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (0) (s) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (s) (0) (cs)) )
  **  ((( &( "top" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  ((( &( "c0" ) )) # Int  |->_)
  **  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (0) (s) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (s) (0) (cs)) )
  **  ((( &( "top" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_29 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (0 <= top)) (PreH15 : (top <= n_pre)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1 ))) (PreH21 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH22 : (ColourValues n_pre before )) (PreH23 : (ParityRespected comments before )) (PreH24 : (ColouredClosed comments before )) (PreH25 : (MaxImpostersOn n_pre comments before total )) (PreH26 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH27 : ((Znth s before 0) = (-1))) (PreH28 : ((Znth s cs 0) <> (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH32 : (top <> 0)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((top - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition solver_safety_wit_30 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (0 <= top)) (PreH15 : (top <= n_pre)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1 ))) (PreH21 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH22 : (ColourValues n_pre before )) (PreH23 : (ParityRespected comments before )) (PreH24 : (ColouredClosed comments before )) (PreH25 : (MaxImpostersOn n_pre comments before total )) (PreH26 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH27 : ((Znth s before 0) = (-1))) (PreH28 : ((Znth s cs 0) <> (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH32 : (top <> 0)),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  ((( &( "u" ) )) # Int  |-> (Znth (top - 1 ) ks 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> (top - 1 ))
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth (top - 1 ) ks 0) cs 0) = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (0 <= top)) (PreH16 : (top <= n_pre)) (PreH17 : (0 <= c0)) (PreH18 : (0 <= c1)) (PreH19 : ((c0 + c1 ) <= n_pre)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1 ))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH23 : (ColourValues n_pre before )) (PreH24 : (ParityRespected comments before )) (PreH25 : (ColouredClosed comments before )) (PreH26 : (MaxImpostersOn n_pre comments before total )) (PreH27 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH28 : ((Znth s before 0) = (-1))) (PreH29 : ((Znth s cs 0) <> (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH33 : (top <> 0)),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  ((( &( "u" ) )) # Int  |-> (Znth (top - 1 ) ks 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> (top - 1 ))
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ ((c0 + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c0 + 1 )) ”
.

Definition solver_safety_wit_32 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth (top - 1 ) ks 0) cs 0) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (0 <= top)) (PreH16 : (top <= n_pre)) (PreH17 : (0 <= c0)) (PreH18 : (0 <= c1)) (PreH19 : ((c0 + c1 ) <= n_pre)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1 ))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH23 : (ColourValues n_pre before )) (PreH24 : (ParityRespected comments before )) (PreH25 : (ColouredClosed comments before )) (PreH26 : (MaxImpostersOn n_pre comments before total )) (PreH27 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH28 : ((Znth s before 0) = (-1))) (PreH29 : ((Znth s cs 0) <> (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH33 : (top <> 0)),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  ((( &( "u" ) )) # Int  |-> (Znth (top - 1 ) ks 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> (top - 1 ))
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ ((c1 + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c1 + 1 )) ”
.

Definition solver_safety_wit_33 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs 0) = 1)) (PreH17 : (0 <= top)) (PreH18 : (top <= n_pre)) (PreH19 : (0 <= c0)) (PreH20 : (0 <= c1)) (PreH21 : ((c0 + c1 ) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre ))) (PreH24 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH25 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH26 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1 ))) (PreH28 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH29 : (ColourValues n_pre before )) (PreH30 : (ParityRespected comments before )) (PreH31 : (ColouredClosed comments before )) (PreH32 : (MaxImpostersOn n_pre comments before total )) (PreH33 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH34 : ((Znth s before 0) = (-1))) (PreH35 : ((Znth s cs 0) <> (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_34 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs 0) = 0)) (PreH17 : (0 <= top)) (PreH18 : (top <= n_pre)) (PreH19 : (0 <= c0)) (PreH20 : (0 <= c1)) (PreH21 : ((c0 + c1 ) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre ))) (PreH24 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH25 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH26 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1 ))) (PreH28 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH29 : (ColourValues n_pre before )) (PreH30 : (ParityRespected comments before )) (PreH31 : (ColouredClosed comments before )) (PreH32 : (MaxImpostersOn n_pre comments before total )) (PreH33 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH34 : ((Znth s before 0) = (-1))) (PreH35 : ((Znth s cs 0) <> (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_35 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs 0) = 0)) (PreH17 : (0 <= top)) (PreH18 : (top <= n_pre)) (PreH19 : (0 <= c0)) (PreH20 : (0 <= c1)) (PreH21 : ((c0 + c1 ) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre ))) (PreH24 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH25 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH26 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1 ))) (PreH28 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH29 : (ColourValues n_pre before )) (PreH30 : (ParityRespected comments before )) (PreH31 : (ColouredClosed comments before )) (PreH32 : (MaxImpostersOn n_pre comments before total )) (PreH33 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH34 : ((Znth s before 0) = (-1))) (PreH35 : ((Znth s cs 0) <> (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs 0) = 1)) (PreH17 : (0 <= top)) (PreH18 : (top <= n_pre)) (PreH19 : (0 <= c0)) (PreH20 : (0 <= c1)) (PreH21 : ((c0 + c1 ) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre ))) (PreH24 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH25 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH26 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1 ))) (PreH28 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH29 : (ColourValues n_pre before )) (PreH30 : (ParityRespected comments before )) (PreH31 : (ColouredClosed comments before )) (PreH32 : (MaxImpostersOn n_pre comments before total )) (PreH33 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH34 : ((Znth s before 0) = (-1))) (PreH35 : ((Znth s cs 0) <> (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_37 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 0)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  ((( &( "want" ) )) # Int  |-> (Z.lxor (Znth u cs 0) (Znth e ws 0)))
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  ((( &( "v" ) )) # Int  |-> (Znth e ts 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_38 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 1)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  ((( &( "want" ) )) # Int  |-> (Z.lxor (Znth u cs 0) (Znth e ws 0)))
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  ((( &( "v" ) )) # Int  |-> (Znth e ts 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_39 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 0)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts 0)) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  ((( &( "want" ) )) # Int  |-> (Z.lxor (Znth u cs 0) (Znth e ws 0)))
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  ((( &( "v" ) )) # Int  |-> (Znth e ts 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
|--
  “ ((top + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 1)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts 0)) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  ((( &( "want" ) )) # Int  |-> (Z.lxor (Znth u cs 0) (Znth e ws 0)))
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  ((( &( "v" ) )) # Int  |-> (Znth e ts 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
|--
  “ ((top + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition solver_safety_wit_41 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) (e: Z) (u: Z) (v: Z) (want: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= n_pre)) (PreH12 : (0 <= c0)) (PreH13 : (0 <= c1)) (PreH14 : ((c0 + c1 ) <= n_pre)) (PreH15 : (0 <= e)) (PreH16 : (e < (2 * m_pre ))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : (0 <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "want" ) )) # Int  |-> want)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_42 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) (e: Z) (u: Z) (v: Z) (want: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= n_pre)) (PreH12 : (0 <= c0)) (PreH13 : (0 <= c1)) (PreH14 : ((c0 + c1 ) <= n_pre)) (PreH15 : (0 <= e)) (PreH16 : (e < (2 * m_pre ))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : (0 <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1) )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "want" ) )) # Int  |-> want)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_43 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (before: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((total + c1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + c1 )) ”
.

Definition solver_safety_wit_44 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (before: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((total + c0 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (total + c0 )) ”
.

Definition solver_safety_wit_45 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (before: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> (total + c0 ))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((s + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition solver_safety_wit_46 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (before: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> (total + c1 ))
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((s + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition solver_safety_wit_47 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) >= 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "comment_u" ) )) # Ptr  |-> comment_u_pre)
  **  ((( &( "comment_v" ) )) # Ptr  |-> comment_v_pre)
  **  ((( &( "comment_diff" ) )) # Ptr  |-> comment_diff_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "nxt" ) )) # Ptr  |-> nxt_pre)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "wt" ) )) # Ptr  |-> wt_pre)
  **  ((( &( "color" ) )) # Ptr  |-> color_pre)
  **  ((( &( "stack_" ) )) # Ptr  |-> stack__pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((s + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (m_pre <= 500000)) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((((((1 <= (fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = 1))))) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < m_pre)) -> ((((Znth i_3 comment_sources 0) = (fst ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_3 comment_targets 0) = (snd ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_3 comment_kinds 0) = (snd ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ ((Zlength (hs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ns)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ts)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ws)) = (2 * m_pre )) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (HeadsInitialised hs 1 ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (m_pre <= 500000)) (PreH4 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((((((1 <= (fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = 1))))) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < m_pre)) -> ((((Znth i_3 comment_sources 0) = (fst ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_3 comment_targets 0) = (snd ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_3 comment_kinds 0) = (snd ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))),
  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ ((Zlength (hs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ns)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ts)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ws)) = (2 * m_pre )) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (HeadsInitialised hs 1 ) ”
  &&  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
).

Definition solver_entail_wit_2 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth (v) ((-1)) (hs_2)) )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ”
  &&  “ ((Zlength (hs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ns)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ts)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ws)) = (2 * m_pre )) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (HeadsInitialised hs (v + 1 ) ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  TT && emp 
|--
  “ (HeadsInitialised (replace_Znth (v) ((-1)) (hs_2)) (v + 1 ) ) ”
  &&  “ ((Zlength ((replace_Znth (v) ((-1)) (hs_2)))) = (n_pre + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  (HeadsInitialised (replace_Znth (v) ((-1)) (hs_2)) (v + 1 ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  ((Zlength ((replace_Znth (v) ((-1)) (hs_2)))) = (n_pre + 1 ))
.

Definition solver_entail_wit_3 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= m_pre) ”
  &&  “ ((0 < m_pre) -> (((((1 <= (Znth 0 comment_sources 0)) /\ ((Znth 0 comment_sources 0) <= n_pre)) /\ (1 <= (Znth 0 comment_targets 0))) /\ ((Znth 0 comment_targets 0) <= n_pre)) /\ (((Znth 0 comment_kinds 0) = 0) \/ ((Znth 0 comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre 0 hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre 0 hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  TT && emp 
|--
  “ (ForwardStarRanges n_pre 0 hs_2 ns_2 ts_2 ws_2 ) ”
  &&  “ (ForwardStar n_pre m_pre 0 hs_2 ns_2 ts_2 ws_2 comments ) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  (ForwardStarRanges n_pre 0 hs_2 ns_2 ts_2 ws_2 )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  (ForwardStar n_pre m_pre 0 hs_2 ns_2 ts_2 ws_2 comments )
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns_2: (@list Z)) (hs_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs_2 v )),
  forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))
.

Definition solver_entail_wit_4 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_targets 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)))) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs_2 0)) (ns_2)))) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws_2)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts_2)))) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m_pre) ”
  &&  “ (((i + 1 ) < m_pre) -> (((((1 <= (Znth (i + 1 ) comment_sources 0)) /\ ((Znth (i + 1 ) comment_sources 0) <= n_pre)) /\ (1 <= (Znth (i + 1 ) comment_targets 0))) /\ ((Znth (i + 1 ) comment_targets 0) <= n_pre)) /\ (((Znth (i + 1 ) comment_kinds 0) = 0) \/ ((Znth (i + 1 ) comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre (i + 1 ) hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre (i + 1 ) hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  TT && emp 
|--
  “ (ForwardStarRanges n_pre (i + 1 ) (replace_Znth ((Znth i comment_targets 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs_2 0)) (ns_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws_2)))) ) ”
  &&  “ (ForwardStar n_pre m_pre (i + 1 ) (replace_Znth ((Znth i comment_targets 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs_2 0)) (ns_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws_2)))) comments ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (ForwardStarRanges n_pre (i + 1 ) (replace_Znth ((Znth i comment_targets 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs_2 0)) (ns_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws_2)))) )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (ForwardStar n_pre m_pre (i + 1 ) (replace_Znth ((Znth i comment_targets 0)) (((2 * i ) + 1 )) ((replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs_2)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs_2 0)) (ns_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts_2)))) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws_2)))) comments )
.

Definition solver_entail_wit_5 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColoursInitialised cs 1 ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  TT && emp 
|--
  “ (ColoursInitialised cs_2 1 ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments ) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (ColoursInitialised cs_2 1 )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )
.

Definition solver_entail_wit_5_split_goal_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )
.

Definition solver_entail_wit_5_split_goal_4 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments )) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2 )) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))
.

Definition solver_entail_wit_6 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v )),
  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (v) ((-1)) (cs_2)) )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColoursInitialised cs (v + 1 ) ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v )),
  TT && emp 
|--
  “ (ColoursInitialised (replace_Znth (v) ((-1)) (cs_2)) (v + 1 ) ) ”
  &&  “ ((Zlength ((replace_Znth (v) ((-1)) (cs_2)))) = (n_pre + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v )),
  (ColoursInitialised (replace_Znth (v) ((-1)) (cs_2)) (v + 1 ) )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v )),
  ((Zlength ((replace_Znth (v) ((-1)) (cs_2)))) = (n_pre + 1 ))
.

Definition solver_entail_wit_7 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (n_pre + 1 )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (ColourValues n_pre cs ) ”
  &&  “ (ParityRespected comments cs ) ”
  &&  “ (ColouredClosed comments cs ) ”
  &&  “ (MaxImpostersOn n_pre comments cs 0 ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < 1)) -> ((Znth v cs 0) <> (-1))) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  TT && emp 
|--
  “ forall (v: Z), (((1 <= v) /\ (v < 1)) -> ((Znth v cs_2 0) <> (-1))) ”
  &&  “ (MaxImpostersOn n_pre comments cs_2 0 ) ”
  &&  “ (ColouredClosed comments cs_2 ) ”
  &&  “ (ParityRespected comments cs_2 ) ”
  &&  “ (ColourValues n_pre cs_2 ) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  forall (v: Z), (((1 <= v) /\ (v < 1)) -> ((Znth v cs_2 0) <> (-1)))
.

Definition solver_entail_wit_7_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  (MaxImpostersOn n_pre comments cs_2 0 )
.

Definition solver_entail_wit_7_split_goal_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  (ColouredClosed comments cs_2 )
.

Definition solver_entail_wit_7_split_goal_4 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  (ParityRespected comments cs_2 )
.

Definition solver_entail_wit_7_split_goal_5 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  (ColourValues n_pre cs_2 )
.

Definition solver_entail_wit_7_split_goal_6 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (v_2: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs_2 v_2 )),
  forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))
.

Definition solver_entail_wit_8 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs_2 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH18 : (ColourValues n_pre cs_2 )) (PreH19 : (ParityRespected comments cs_2 )) (PreH20 : (ColouredClosed comments cs_2 )) (PreH21 : (MaxImpostersOn n_pre comments cs_2 total )) (PreH22 : forall (v_2: Z), (((1 <= v_2) /\ (v_2 < s)) -> ((Znth v_2 cs_2 0) <> (-1)))) (PreH23 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (0) (s) (ks_2)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (s) (0) (cs_2)) )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
|--
  EX (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= (0 + 1 )) ”
  &&  “ ((0 + 1 ) <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((0 + 0 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (0 + 1 ))) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) ((0 + 1 )) (ks)) 0 0 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs_2 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH18 : (ColourValues n_pre cs_2 )) (PreH19 : (ParityRespected comments cs_2 )) (PreH20 : (ColouredClosed comments cs_2 )) (PreH21 : (MaxImpostersOn n_pre comments cs_2 total )) (PreH22 : forall (v_2: Z), (((1 <= v_2) /\ (v_2 < s)) -> ((Znth v_2 cs_2 0) <> (-1)))) (PreH23 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  TT && emp 
|--
  EX (finished: (@list Z)) (before: (@list Z)),
  “ (0 <= (0 + 1 )) ”
  &&  “ ((0 + 1 ) <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((0 + 0 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (0 + 1 ))) -> ((1 <= (Znth j (replace_Znth (0) (s) (ks_2)) 0)) /\ ((Znth j (replace_Znth (0) (s) (ks_2)) 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength ((replace_Znth (0) (s) (ks_2)))) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s (replace_Znth (s) (0) (cs_2)) 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before (replace_Znth (s) (0) (cs_2)) finished (sublist (0) ((0 + 1 )) ((replace_Znth (0) (s) (ks_2)))) 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_9_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (finished_2: (@list Z)) (cs_2: (@list Z)) (before_2: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth (top - 1 ) ks 0) cs_2 0) = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (0 <= top)) (PreH16 : (top <= n_pre)) (PreH17 : (0 <= c0)) (PreH18 : (0 <= c1)) (PreH19 : ((c0 + c1 ) <= n_pre)) (PreH20 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < top)) -> ((1 <= (Znth j_2 ks 0)) /\ ((Znth j_2 ks 0) <= n_pre)))) (PreH21 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH23 : (ColourValues n_pre before_2 )) (PreH24 : (ParityRespected comments before_2 )) (PreH25 : (ColouredClosed comments before_2 )) (PreH26 : (MaxImpostersOn n_pre comments before_2 total )) (PreH27 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before_2 0) <> (-1)))) (PreH28 : ((Znth s before_2 0) = (-1))) (PreH29 : ((Znth s cs_2 0) <> (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished_2 (sublist (0) (top) (ks)) c0 c1 )) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns_2 ts_2 ws_2 comments )) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns_2 ts_2 ws_2 )) (PreH33 : (top <> 0)),
  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
|--
  (EX (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= (Znth (top - 1 ) ks 0)) ”
  &&  “ ((Znth (top - 1 ) ks 0) <= n_pre) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) cs 0) = 0) ”
  &&  “ (0 <= (top - 1 )) ”
  &&  “ ((top - 1 ) <= n_pre) ”
  &&  “ (0 <= (c0 + 1 )) ”
  &&  “ (0 <= c1) ”
  &&  “ (((c0 + 1 ) + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth (Znth (top - 1 ) ks 0) hs 0)) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) hs 0) < (2 * m_pre )) ”
  &&  “ (((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0)) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) <= n_pre)) /\ (((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 0) \/ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0))) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) cs 0) < 0)) -> ((top - 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top - 1 ))) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks_2)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top - 1 )) (ks_2)) (Znth (top - 1 ) ks 0) (Znth (Znth (top - 1 ) ks 0) hs 0) (c0 + 1 ) c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 ))
  ||
  (EX (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= (Znth (top - 1 ) ks 0)) ”
  &&  “ ((Znth (top - 1 ) ks 0) <= n_pre) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) cs 0) = 1) ”
  &&  “ (0 <= (top - 1 )) ”
  &&  “ ((top - 1 ) <= n_pre) ”
  &&  “ (0 <= (c0 + 1 )) ”
  &&  “ (0 <= c1) ”
  &&  “ (((c0 + 1 ) + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth (Znth (top - 1 ) ks 0) hs 0)) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) hs 0) < (2 * m_pre )) ”
  &&  “ (((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0)) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) <= n_pre)) /\ (((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 0) \/ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0))) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) cs 0) < 0)) -> ((top - 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top - 1 ))) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks_2)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top - 1 )) (ks_2)) (Znth (top - 1 ) ks 0) (Znth (Znth (top - 1 ) ks 0) hs 0) (c0 + 1 ) c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 ))
.

Definition solver_entail_wit_9_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (finished_2: (@list Z)) (cs_2: (@list Z)) (before_2: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth (top - 1 ) ks 0) cs_2 0) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (0 <= top)) (PreH16 : (top <= n_pre)) (PreH17 : (0 <= c0)) (PreH18 : (0 <= c1)) (PreH19 : ((c0 + c1 ) <= n_pre)) (PreH20 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < top)) -> ((1 <= (Znth j_2 ks 0)) /\ ((Znth j_2 ks 0) <= n_pre)))) (PreH21 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH23 : (ColourValues n_pre before_2 )) (PreH24 : (ParityRespected comments before_2 )) (PreH25 : (ColouredClosed comments before_2 )) (PreH26 : (MaxImpostersOn n_pre comments before_2 total )) (PreH27 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before_2 0) <> (-1)))) (PreH28 : ((Znth s before_2 0) = (-1))) (PreH29 : ((Znth s cs_2 0) <> (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished_2 (sublist (0) (top) (ks)) c0 c1 )) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns_2 ts_2 ws_2 comments )) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns_2 ts_2 ws_2 )) (PreH33 : (top <> 0)),
  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
|--
  (EX (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= (Znth (top - 1 ) ks 0)) ”
  &&  “ ((Znth (top - 1 ) ks 0) <= n_pre) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) cs 0) = 0) ”
  &&  “ (0 <= (top - 1 )) ”
  &&  “ ((top - 1 ) <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= (c1 + 1 )) ”
  &&  “ ((c0 + (c1 + 1 ) ) <= n_pre) ”
  &&  “ ((-1) <= (Znth (Znth (top - 1 ) ks 0) hs 0)) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) hs 0) < (2 * m_pre )) ”
  &&  “ (((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0)) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) <= n_pre)) /\ (((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 0) \/ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0))) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) cs 0) < 0)) -> ((top - 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top - 1 ))) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks_2)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top - 1 )) (ks_2)) (Znth (top - 1 ) ks 0) (Znth (Znth (top - 1 ) ks 0) hs 0) c0 (c1 + 1 ) ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 ))
  ||
  (EX (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= (Znth (top - 1 ) ks 0)) ”
  &&  “ ((Znth (top - 1 ) ks 0) <= n_pre) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) cs 0) = 1) ”
  &&  “ (0 <= (top - 1 )) ”
  &&  “ ((top - 1 ) <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= (c1 + 1 )) ”
  &&  “ ((c0 + (c1 + 1 ) ) <= n_pre) ”
  &&  “ ((-1) <= (Znth (Znth (top - 1 ) ks 0) hs 0)) ”
  &&  “ ((Znth (Znth (top - 1 ) ks 0) hs 0) < (2 * m_pre )) ”
  &&  “ (((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0)) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) <= n_pre)) /\ (((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 0) \/ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0))) /\ ((Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth (Znth (top - 1 ) ks 0) hs 0) <> (-1)) /\ ((Znth (Znth (Znth (Znth (top - 1 ) ks 0) hs 0) ts 0) cs 0) < 0)) -> ((top - 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top - 1 ))) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks_2)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top - 1 )) (ks_2)) (Znth (top - 1 ) ks 0) (Znth (Znth (top - 1 ) ks 0) hs 0) c0 (c1 + 1 ) ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 ))
.

Definition solver_entail_wit_10_1 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 0)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns: (@list Z)) (hs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ (0 <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ (1 <= (Znth e ts 0)) ”
  &&  “ ((Znth e ts 0) <= n_pre) ”
  &&  “ (0 <= (Z.lxor (Znth u cs 0) (Znth e ws 0))) ”
  &&  “ ((Z.lxor (Znth u cs 0) (Znth e ws 0)) <= 1) ”
  &&  “ (Spec n_pre comments (-1) ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 0)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  TT && emp 
|--
  “ (Spec n_pre comments (-1) ) ”
  &&  “ ((Z.lxor 0 (Znth e ws 0)) <= 1) ”
  &&  “ (0 <= (Z.lxor 0 (Znth e ws 0))) ”
  &&  emp
).

Definition solver_entail_wit_10_1_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 0)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  (Spec n_pre comments (-1) )
.

Definition solver_entail_wit_10_1_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 0)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  ((Z.lxor 0 (Znth e ws 0)) <= 1)
.

Definition solver_entail_wit_10_1_split_goal_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 0)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  (0 <= (Z.lxor 0 (Znth e ws 0)))
.

Definition solver_entail_wit_10_2 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 1)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (ns: (@list Z)) (hs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ (0 <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ (1 <= (Znth e ts 0)) ”
  &&  “ ((Znth e ts 0) <= n_pre) ”
  &&  “ (0 <= (Z.lxor (Znth u cs 0) (Znth e ws 0))) ”
  &&  “ ((Z.lxor (Znth u cs 0) (Znth e ws 0)) <= 1) ”
  &&  “ (Spec n_pre comments (-1) ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 1)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  TT && emp 
|--
  “ (Spec n_pre comments (-1) ) ”
  &&  “ ((Z.lxor 1 (Znth e ws 0)) <= 1) ”
  &&  “ (0 <= (Z.lxor 1 (Znth e ws 0))) ”
  &&  emp
).

Definition solver_entail_wit_10_2_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 1)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  (Spec n_pre comments (-1) )
.

Definition solver_entail_wit_10_2_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 1)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  ((Z.lxor 1 (Znth e ws 0)) <= 1)
.

Definition solver_entail_wit_10_2_split_goal_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) <> (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 1)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws )),
  (0 <= (Z.lxor 1 (Znth e ws 0)))
.

Definition solver_entail_wit_11_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts_2 0) cs_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs_2 0) = 0)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH29 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before_2 )) (PreH32 : (ParityRespected comments before_2 )) (PreH33 : (ColouredClosed comments before_2 )) (PreH34 : (MaxImpostersOn n_pre comments before_2 total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH36 : ((Znth s before_2 0) = (-1))) (PreH37 : ((Znth s cs_2 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts_2 0)) (ks_2)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts_2 0)) ((Z.lxor (Znth u cs_2 0) (Znth e ws_2 0))) (cs_2)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
|--
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= (top + 1 )) ”
  &&  “ ((top + 1 ) <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> ((top + 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top + 1 ))) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top + 1 )) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
  ||
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= (top + 1 )) ”
  &&  “ ((top + 1 ) <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> ((top + 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top + 1 ))) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top + 1 )) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
.

Definition solver_entail_wit_11_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts_2 0) cs_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs_2 0) = 1)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH29 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before_2 )) (PreH32 : (ParityRespected comments before_2 )) (PreH33 : (ColouredClosed comments before_2 )) (PreH34 : (MaxImpostersOn n_pre comments before_2 total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH36 : ((Znth s before_2 0) = (-1))) (PreH37 : ((Znth s cs_2 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts_2 0)) (ks_2)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts_2 0)) ((Z.lxor (Znth u cs_2 0) (Znth e ws_2 0))) (cs_2)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
|--
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= (top + 1 )) ”
  &&  “ ((top + 1 ) <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> ((top + 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top + 1 ))) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top + 1 )) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
  ||
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= (top + 1 )) ”
  &&  “ ((top + 1 ) <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> ((top + 1 ) < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (top + 1 ))) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) ((top + 1 )) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
.

Definition solver_entail_wit_11_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts_2 0) cs_2 0) = (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)))) (PreH2 : ((Znth (Znth e ts_2 0) cs_2 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs_2 0) = 0)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before_2 )) (PreH33 : (ParityRespected comments before_2 )) (PreH34 : (ColouredClosed comments before_2 )) (PreH35 : (MaxImpostersOn n_pre comments before_2 total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH37 : ((Znth s before_2 0) = (-1))) (PreH38 : ((Znth s cs_2 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
  ||
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
.

Definition solver_entail_wit_11_4 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts_2 0) cs_2 0) = (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)))) (PreH2 : ((Znth (Znth e ts_2 0) cs_2 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs_2 0) = 1)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH30 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before_2 )) (PreH33 : (ParityRespected comments before_2 )) (PreH34 : (ColouredClosed comments before_2 )) (PreH35 : (MaxImpostersOn n_pre comments before_2 total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH37 : ((Znth s before_2 0) = (-1))) (PreH38 : ((Znth s cs_2 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
  ||
  (EX (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (cs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= (Znth e ns_2 0)) ”
  &&  “ ((Znth e ns_2 0) < (2 * m_pre )) ”
  &&  “ (((Znth e ns_2 0) <> (-1)) -> (((((1 <= (Znth (Znth e ns_2 0) ts 0)) /\ ((Znth (Znth e ns_2 0) ts 0) <= n_pre)) /\ (((Znth (Znth e ns_2 0) ws 0) = 0) \/ ((Znth (Znth e ns_2 0) ws 0) = 1))) /\ ((-1) <= (Znth (Znth e ns_2 0) ns 0))) /\ ((Znth (Znth e ns_2 0) ns 0) < (2 * m_pre )))) ”
  &&  “ ((((Znth e ns_2 0) <> (-1)) /\ ((Znth (Znth (Znth e ns_2 0) ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u (Znth e ns_2 0) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks ))
.

Definition solver_entail_wit_12_1 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 0) = 0)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 0)) /\ ((Znth j_2 ks_2 0) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before_2 )) (PreH31 : (ParityRespected comments before_2 )) (PreH32 : (ColouredClosed comments before_2 )) (PreH33 : (MaxImpostersOn n_pre comments before_2 total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH35 : ((Znth s before_2 0) = (-1))) (PreH36 : ((Znth s cs_2 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 0) = 0)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 0)) /\ ((Znth j_2 ks_2 0) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before_2 )) (PreH31 : (ParityRespected comments before_2 )) (PreH32 : (ColouredClosed comments before_2 )) (PreH33 : (MaxImpostersOn n_pre comments before_2 total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH35 : ((Znth s before_2 0) = (-1))) (PreH36 : ((Znth s cs_2 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  TT && emp 
|--
  EX (finished: (@list Z)) (before: (@list Z)),
  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs_2 finished (sublist (0) (top) (ks_2)) c0 c1 ) ”
  &&  emp
).

Definition solver_entail_wit_12_2 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 0) = 1)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 0)) /\ ((Znth j_2 ks_2 0) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before_2 )) (PreH31 : (ParityRespected comments before_2 )) (PreH32 : (ColouredClosed comments before_2 )) (PreH33 : (MaxImpostersOn n_pre comments before_2 total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH35 : ((Znth s before_2 0) = (-1))) (PreH36 : ((Znth s cs_2 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (finished_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (ns_2: (@list Z)) (ws_2: (@list Z)) (ts_2: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs_2: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 0) = 1)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts_2 0)) /\ ((Znth e ts_2 0) <= n_pre)) /\ (((Znth e ws_2 0) = 0) \/ ((Znth e ws_2 0) = 1))) /\ ((-1) <= (Znth e ns_2 0))) /\ ((Znth e ns_2 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts_2 0) cs_2 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 0)) /\ ((Znth j_2 ks_2 0) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before_2 )) (PreH31 : (ParityRespected comments before_2 )) (PreH32 : (ColouredClosed comments before_2 )) (PreH33 : (MaxImpostersOn n_pre comments before_2 total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before_2 0) <> (-1)))) (PreH35 : ((Znth s before_2 0) = (-1))) (PreH36 : ((Znth s cs_2 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist (0) (top) (ks_2)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  TT && emp 
|--
  EX (finished: (@list Z)) (before: (@list Z)),
  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs_2 finished (sublist (0) (top) (ks_2)) c0 c1 ) ”
  &&  emp
).

Definition solver_entail_wit_13 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (finished: (@list Z)) (cs_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (0 <= top)) (PreH15 : (top <= n_pre)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH20 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH21 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH22 : (ColourValues n_pre before_2 )) (PreH23 : (ParityRespected comments before_2 )) (PreH24 : (ColouredClosed comments before_2 )) (PreH25 : (MaxImpostersOn n_pre comments before_2 total )) (PreH26 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before_2 0) <> (-1)))) (PreH27 : ((Znth s before_2 0) = (-1))) (PreH28 : ((Znth s cs_2 0) <> (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished (sublist (0) (top) (ks_2)) c0 c1 )) (PreH30 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH31 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH32 : (top = 0)),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (vertices: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (before: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (top = 0) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentCompleteStrong n_pre comments before cs vertices c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (finished: (@list Z)) (cs_2: (@list Z)) (before_2: (@list Z)) (ks_2: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (0 <= top)) (PreH15 : (top <= n_pre)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks_2 0)) /\ ((Znth j ks_2 0) <= n_pre)))) (PreH20 : ((Zlength (before_2)) = (n_pre + 1 ))) (PreH21 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH22 : (ColourValues n_pre before_2 )) (PreH23 : (ParityRespected comments before_2 )) (PreH24 : (ColouredClosed comments before_2 )) (PreH25 : (MaxImpostersOn n_pre comments before_2 total )) (PreH26 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before_2 0) <> (-1)))) (PreH27 : ((Znth s before_2 0) = (-1))) (PreH28 : ((Znth s cs_2 0) <> (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished (sublist (0) (top) (ks_2)) c0 c1 )) (PreH30 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH31 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH32 : (top = 0)),
  TT && emp 
|--
  EX (vertices: (@list Z)) (before: (@list Z)),
  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 ) ”
  &&  emp
).

Definition solver_entail_wit_14_1 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= (s + 1 )) ”
  &&  “ ((s + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= (total + c0 )) ”
  &&  “ ((total + c0 ) <= n_pre) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (ColourValues n_pre cs ) ”
  &&  “ (ParityRespected comments cs ) ”
  &&  “ (ColouredClosed comments cs ) ”
  &&  “ (MaxImpostersOn n_pre comments cs (total + c0 ) ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < (s + 1 ))) -> ((Znth v cs 0) <> (-1))) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  TT && emp 
|--
  “ forall (v: Z), (((1 <= v) /\ (v < (s + 1 ))) -> ((Znth v cs_2 0) <> (-1))) ”
  &&  “ (MaxImpostersOn n_pre comments cs_2 (total + c0 ) ) ”
  &&  “ (ColouredClosed comments cs_2 ) ”
  &&  “ (ParityRespected comments cs_2 ) ”
  &&  “ (ColourValues n_pre cs_2 ) ”
  &&  “ ((total + c0 ) <= n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  forall (v: Z), (((1 <= v) /\ (v < (s + 1 ))) -> ((Znth v cs_2 0) <> (-1)))
.

Definition solver_entail_wit_14_1_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (MaxImpostersOn n_pre comments cs_2 (total + c0 ) )
.

Definition solver_entail_wit_14_1_split_goal_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (ColouredClosed comments cs_2 )
.

Definition solver_entail_wit_14_1_split_goal_4 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (ParityRespected comments cs_2 )
.

Definition solver_entail_wit_14_1_split_goal_5 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (ColourValues n_pre cs_2 )
.

Definition solver_entail_wit_14_1_split_goal_6 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  ((total + c0 ) <= n_pre)
.

Definition solver_entail_wit_14_1_split_goal_7 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))
.

Definition solver_entail_wit_14_2 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= (s + 1 )) ”
  &&  “ ((s + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= (total + c1 )) ”
  &&  “ ((total + c1 ) <= n_pre) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (ColourValues n_pre cs ) ”
  &&  “ (ParityRespected comments cs ) ”
  &&  “ (ColouredClosed comments cs ) ”
  &&  “ (MaxImpostersOn n_pre comments cs (total + c1 ) ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < (s + 1 ))) -> ((Znth v cs 0) <> (-1))) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  TT && emp 
|--
  “ forall (v: Z), (((1 <= v) /\ (v < (s + 1 ))) -> ((Znth v cs_2 0) <> (-1))) ”
  &&  “ (MaxImpostersOn n_pre comments cs_2 (total + c1 ) ) ”
  &&  “ (ColouredClosed comments cs_2 ) ”
  &&  “ (ParityRespected comments cs_2 ) ”
  &&  “ (ColourValues n_pre cs_2 ) ”
  &&  “ ((total + c1 ) <= n_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  forall (v: Z), (((1 <= v) /\ (v < (s + 1 ))) -> ((Znth v cs_2 0) <> (-1)))
.

Definition solver_entail_wit_14_2_split_goal_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (MaxImpostersOn n_pre comments cs_2 (total + c1 ) )
.

Definition solver_entail_wit_14_2_split_goal_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (ColouredClosed comments cs_2 )
.

Definition solver_entail_wit_14_2_split_goal_4 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (ParityRespected comments cs_2 )
.

Definition solver_entail_wit_14_2_split_goal_5 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  (ColourValues n_pre cs_2 )
.

Definition solver_entail_wit_14_2_split_goal_6 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  ((total + c1 ) <= n_pre)
.

Definition solver_entail_wit_14_2_split_goal_7 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (before: (@list Z)) (cs_2: (@list Z)) (ks_2: (@list Z)) (vertices: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources 0)) /\ ((Znth q_2 comment_sources 0) <= n_pre)) /\ (1 <= (Znth q_2 comment_targets 0))) /\ ((Znth q_2 comment_targets 0) <= n_pre)) /\ ((Znth q_2 comment_sources 0) <> (Znth q_2 comment_targets 0))) /\ (((Znth q_2 comment_kinds 0) = 0) \/ ((Znth q_2 comment_kinds 0) = 1))) /\ ((Znth q_2 comment_sources 0) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_targets 0) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q_2 comment_kinds 0) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = 0)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1 ))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1 ))) (PreH21 : (ColourValues n_pre before )) (PreH22 : (ParityRespected comments before )) (PreH23 : (ColouredClosed comments before )) (PreH24 : (MaxImpostersOn n_pre comments before total )) (PreH25 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH26 : ((Znth s before 0) = (-1))) (PreH27 : ((Znth s cs_2 0) <> (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1 )) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )),
  forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))
.

Definition solver_entail_wit_14_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs_2 0) >= 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH18 : (ColourValues n_pre cs_2 )) (PreH19 : (ParityRespected comments cs_2 )) (PreH20 : (ColouredClosed comments cs_2 )) (PreH21 : (MaxImpostersOn n_pre comments cs_2 total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs_2 0) <> (-1)))) (PreH23 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= (s + 1 )) ”
  &&  “ ((s + 1 ) <= (n_pre + 1 )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (ColourValues n_pre cs ) ”
  &&  “ (ParityRespected comments cs ) ”
  &&  “ (ColouredClosed comments cs ) ”
  &&  “ (MaxImpostersOn n_pre comments cs total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < (s + 1 ))) -> ((Znth v cs 0) <> (-1))) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_entail_wit_15 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (s > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1 ))) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH16 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH17 : (ColourValues n_pre cs_2 )) (PreH18 : (ParityRespected comments cs_2 )) (PreH19 : (ColouredClosed comments cs_2 )) (PreH20 : (MaxImpostersOn n_pre comments cs_2 total )) (PreH21 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs_2 0) <> (-1)))) (PreH22 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs_2 )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns_2 )
  **  (IntArray.full to_pre (2 * m_pre ) ts_2 )
  **  (IntArray.full wt_pre (2 * m_pre ) ws_2 )
  **  (IntArray.full color_pre (n_pre + 1 ) cs_2 )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks_2 )
|--
  EX (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (Spec n_pre comments total ) ”
  &&  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (s > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1 ))) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH16 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH17 : (ColourValues n_pre cs_2 )) (PreH18 : (ParityRespected comments cs_2 )) (PreH19 : (ColouredClosed comments cs_2 )) (PreH20 : (MaxImpostersOn n_pre comments cs_2 total )) (PreH21 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs_2 0) <> (-1)))) (PreH22 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  TT && emp 
|--
  “ (Spec n_pre comments total ) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (ks_2: (@list Z)) (cs_2: (@list Z)) (hs_2: (@list Z)) (ns_2: (@list Z)) (ts_2: (@list Z)) (ws_2: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (s > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1 ))) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments )) (PreH16 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2 )) (PreH17 : (ColourValues n_pre cs_2 )) (PreH18 : (ParityRespected comments cs_2 )) (PreH19 : (ColouredClosed comments cs_2 )) (PreH20 : (MaxImpostersOn n_pre comments cs_2 total )) (PreH21 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs_2 0) <> (-1)))) (PreH22 : ((Zlength (ks_2)) = (n_pre + 1 ))),
  (Spec n_pre comments total )
.

Definition solver_return_wit_1 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (0 <= total)) (PreH7 : (total <= n_pre)) (PreH8 : (Spec n_pre comments total )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (Spec n_pre comments total ) ”
  &&  (IntArray.full_shape comment_u_pre m_pre )
  **  (IntArray.full_shape comment_v_pre m_pre )
  **  (IntArray.full_shape comment_diff_pre m_pre )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (0 <= total)) (PreH7 : (total <= n_pre)) (PreH8 : (Spec n_pre comments total )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  (IntArray.full_shape comment_u_pre m_pre )
  **  (IntArray.full_shape comment_v_pre m_pre )
  **  (IntArray.full_shape comment_diff_pre m_pre )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
).

Definition solver_return_wit_1_split_goal_spatial :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (total: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (0 <= total)) (PreH7 : (total <= n_pre)) (PreH8 : (Spec n_pre comments total )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  (IntArray.full_shape comment_u_pre m_pre )
  **  (IntArray.full_shape comment_v_pre m_pre )
  **  (IntArray.full_shape comment_diff_pre m_pre )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
.

Definition solver_return_wit_2 :=
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) (e: Z) (u: Z) (v: Z) (want: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= n_pre)) (PreH12 : (0 <= c0)) (PreH13 : (0 <= c1)) (PreH14 : ((c0 + c1 ) <= n_pre)) (PreH15 : (0 <= e)) (PreH16 : (e < (2 * m_pre ))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : (0 <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1) )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (Spec n_pre comments (-1) ) ”
  &&  (IntArray.full_shape comment_u_pre m_pre )
  **  (IntArray.full_shape comment_v_pre m_pre )
  **  (IntArray.full_shape comment_diff_pre m_pre )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
) \/
(
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) (e: Z) (u: Z) (v: Z) (want: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= n_pre)) (PreH12 : (0 <= c0)) (PreH13 : (0 <= c1)) (PreH14 : ((c0 + c1 ) <= n_pre)) (PreH15 : (0 <= e)) (PreH16 : (e < (2 * m_pre ))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : (0 <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1) )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  (IntArray.full_shape comment_u_pre m_pre )
  **  (IntArray.full_shape comment_v_pre m_pre )
  **  (IntArray.full_shape comment_diff_pre m_pre )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
).

Definition solver_return_wit_2_split_goal_spatial :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (cs: (@list Z)) (ks: (@list Z)) (s: Z) (total: Z) (top: Z) (c0: Z) (c1: Z) (e: Z) (u: Z) (v: Z) (want: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= n_pre)) (PreH12 : (0 <= c0)) (PreH13 : (0 <= c1)) (PreH14 : ((c0 + c1 ) <= n_pre)) (PreH15 : (0 <= e)) (PreH16 : (e < (2 * m_pre ))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : (0 <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1) )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  (IntArray.full_shape comment_u_pre m_pre )
  **  (IntArray.full_shape comment_v_pre m_pre )
  **  (IntArray.full_shape comment_diff_pre m_pre )
  **  (IntArray.full_shape head_pre (n_pre + 1 ) )
  **  (IntArray.full_shape nxt_pre (2 * m_pre ) )
  **  (IntArray.full_shape to_pre (2 * m_pre ) )
  **  (IntArray.full_shape wt_pre (2 * m_pre ) )
  **  (IntArray.full_shape color_pre (n_pre + 1 ) )
  **  (IntArray.full_shape stack__pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_1 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (ns: (@list Z)) (hs: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : ((Zlength (hs)) = (n_pre + 1 ))) (PreH14 : ((Zlength (ns)) = (2 * m_pre ))) (PreH15 : ((Zlength (ts)) = (2 * m_pre ))) (PreH16 : ((Zlength (ws)) = (2 * m_pre ))) (PreH17 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH18 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH19 : (HeadsInitialised hs v )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (v <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) /\ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <> (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 0) \/ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) /\ ((Znth i comment_sources 0) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_targets 0) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i comment_kinds 0) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= (n_pre + 1 )) ”
  &&  “ ((Zlength (hs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ns)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ts)) = (2 * m_pre )) ”
  &&  “ ((Zlength (ws)) = (2 * m_pre )) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (HeadsInitialised hs v ) ”
  &&  (((head_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i head_pre v 0 (n_pre + 1 ) hs )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_2 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((comment_v_pre + (i * sizeof(INT)))) # Int  |-> (Znth i comment_targets 0))
  **  (IntArray.missing_i comment_v_pre i 0 m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_3 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((comment_u_pre + (i * sizeof(INT)))) # Int  |-> (Znth i comment_sources 0))
  **  (IntArray.missing_i comment_u_pre i 0 m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_4 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((to_pre + ((2 * i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i to_pre (2 * i ) 0 (2 * m_pre ) ts )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_5 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((comment_diff_pre + (i * sizeof(INT)))) # Int  |-> (Znth i comment_kinds 0))
  **  (IntArray.missing_i comment_diff_pre i 0 m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_6 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((wt_pre + ((2 * i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i wt_pre (2 * i ) 0 (2 * m_pre ) ws )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_7 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((head_pre + ((Znth i comment_sources 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i comment_sources 0) hs 0))
  **  (IntArray.missing_i head_pre (Znth i comment_sources 0) 0 (n_pre + 1 ) hs )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_8 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((nxt_pre + ((2 * i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nxt_pre (2 * i ) 0 (2 * m_pre ) ns )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_9 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((head_pre + ((Znth i comment_sources 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i head_pre (Znth i comment_sources 0) 0 (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_10 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((to_pre + (((2 * i ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i to_pre ((2 * i ) + 1 ) 0 (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_11 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((comment_diff_pre + (i * sizeof(INT)))) # Int  |-> (Znth i comment_kinds 0))
  **  (IntArray.missing_i comment_diff_pre i 0 m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_12 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((wt_pre + (((2 * i ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i wt_pre ((2 * i ) + 1 ) 0 (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_13 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((head_pre + ((Znth i comment_targets 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) 0))
  **  (IntArray.missing_i head_pre (Znth i comment_targets 0) 0 (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_14 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((nxt_pre + (((2 * i ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nxt_pre ((2 * i ) + 1 ) 0 (2 * m_pre ) (replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_15 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (0 <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments )) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws )) (PreH16 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH17 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)))) )
  **  (IntArray.full head_pre (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (i < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= m_pre) ”
  &&  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources 0)) /\ ((Znth i comment_sources 0) <= n_pre)) /\ (1 <= (Znth i comment_targets 0))) /\ ((Znth i comment_targets 0) <= n_pre)) /\ (((Znth i comment_kinds 0) = 0) \/ ((Znth i comment_kinds 0) = 1)))) ”
  &&  “ (ForwardStar n_pre m_pre i hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre i hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((head_pre + ((Znth i comment_targets 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i head_pre (Znth i comment_targets 0) 0 (n_pre + 1 ) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) )
  **  (IntArray.full nxt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth (Znth i comment_targets 0) (replace_Znth ((Znth i comment_sources 0)) ((2 * i )) (hs)) 0)) ((replace_Znth ((2 * i )) ((Znth (Znth i comment_sources 0) hs 0)) (ns)))) )
  **  (IntArray.full wt_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_kinds 0)) ((replace_Znth ((2 * i )) ((Znth i comment_kinds 0)) (ws)))) )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full to_pre (2 * m_pre ) (replace_Znth (((2 * i ) + 1 )) ((Znth i comment_sources 0)) ((replace_Znth ((2 * i )) ((Znth i comment_targets 0)) (ts)))) )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_16 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (v: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1 ))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH15 : ((Zlength (cs)) = (n_pre + 1 ))) (PreH16 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH17 : (ColoursInitialised cs v )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (v <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= (n_pre + 1 )) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ ((Zlength (cs)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColoursInitialised cs v ) ”
  &&  (((color_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i color_pre v 0 (n_pre + 1 ) cs )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_17 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (s <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1 ))) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH16 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH17 : (ColourValues n_pre cs )) (PreH18 : (ParityRespected comments cs )) (PreH19 : (ColouredClosed comments cs )) (PreH20 : (MaxImpostersOn n_pre comments cs total )) (PreH21 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (s <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= (n_pre + 1 )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (ColourValues n_pre cs ) ”
  &&  “ (ParityRespected comments cs ) ”
  &&  “ (ColouredClosed comments cs ) ”
  &&  “ (MaxImpostersOn n_pre comments cs total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1))) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((color_pre + (s * sizeof(INT)))) # Int  |-> (Znth s cs 0))
  **  (IntArray.missing_i color_pre s 0 (n_pre + 1 ) cs )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_18 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth s cs 0) < 0) ”
  &&  “ (s <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= (n_pre + 1 )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (ColourValues n_pre cs ) ”
  &&  “ (ParityRespected comments cs ) ”
  &&  “ (ColouredClosed comments cs ) ”
  &&  “ (MaxImpostersOn n_pre comments cs total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1))) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((color_pre + (s * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i color_pre s 0 (n_pre + 1 ) cs )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_19 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (ks: (@list Z)) (cs: (@list Z)) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth s cs 0) < 0)) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1 ))) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH18 : (ColourValues n_pre cs )) (PreH19 : (ParityRespected comments cs )) (PreH20 : (ColouredClosed comments cs )) (PreH21 : (MaxImpostersOn n_pre comments cs total )) (PreH22 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1 ))),
  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (s) (0) (cs)) )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth s cs 0) < 0) ”
  &&  “ (s <= n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= (n_pre + 1 )) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (ColourValues n_pre cs ) ”
  &&  “ (ParityRespected comments cs ) ”
  &&  “ (ColouredClosed comments cs ) ”
  &&  “ (MaxImpostersOn n_pre comments cs total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v cs 0) <> (-1))) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  (((stack__pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i stack__pre 0 0 (n_pre + 1 ) ks )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth (s) (0) (cs)) )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
.

Definition solver_partial_solve_wit_20 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (0 <= top)) (PreH15 : (top <= n_pre)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1 ))) (PreH21 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH22 : (ColourValues n_pre before )) (PreH23 : (ParityRespected comments before )) (PreH24 : (ColouredClosed comments before )) (PreH25 : (MaxImpostersOn n_pre comments before total )) (PreH26 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH27 : ((Znth s before 0) = (-1))) (PreH28 : ((Znth s cs 0) <> (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH32 : (top <> 0)),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (top <> 0) ”
  &&  (((stack__pre + ((top - 1 ) * sizeof(INT)))) # Int  |-> (Znth (top - 1 ) ks 0))
  **  (IntArray.missing_i stack__pre (top - 1 ) 0 (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
.

Definition solver_partial_solve_wit_21 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (0 <= top)) (PreH15 : (top <= n_pre)) (PreH16 : (0 <= c0)) (PreH17 : (0 <= c1)) (PreH18 : ((c0 + c1 ) <= n_pre)) (PreH19 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1 ))) (PreH21 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH22 : (ColourValues n_pre before )) (PreH23 : (ParityRespected comments before )) (PreH24 : (ColouredClosed comments before )) (PreH25 : (MaxImpostersOn n_pre comments before total )) (PreH26 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH27 : ((Znth s before 0) = (-1))) (PreH28 : ((Znth s cs 0) <> (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH32 : (top <> 0)),
  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (top <> 0) ”
  &&  (((color_pre + ((Znth (top - 1 ) ks 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (top - 1 ) ks 0) cs 0))
  **  (IntArray.missing_i color_pre (Znth (top - 1 ) ks 0) 0 (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
.

Definition solver_partial_solve_wit_22 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth (top - 1 ) ks 0) cs 0) = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (0 <= top)) (PreH16 : (top <= n_pre)) (PreH17 : (0 <= c0)) (PreH18 : (0 <= c1)) (PreH19 : ((c0 + c1 ) <= n_pre)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1 ))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH23 : (ColourValues n_pre before )) (PreH24 : (ParityRespected comments before )) (PreH25 : (ColouredClosed comments before )) (PreH26 : (MaxImpostersOn n_pre comments before total )) (PreH27 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH28 : ((Znth s before 0) = (-1))) (PreH29 : ((Znth s cs 0) <> (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH33 : (top <> 0)),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ ((Znth (Znth (top - 1 ) ks 0) cs 0) = 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (top <> 0) ”
  &&  (((head_pre + ((Znth (top - 1 ) ks 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (top - 1 ) ks 0) hs 0))
  **  (IntArray.missing_i head_pre (Znth (top - 1 ) ks 0) 0 (n_pre + 1 ) hs )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
.

Definition solver_partial_solve_wit_23 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (ns: (@list Z)) (ts: (@list Z)) (ws: (@list Z)) (finished: (@list Z)) (cs: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (c1: Z) (c0: Z) (top: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth (top - 1 ) ks 0) cs 0) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (0 <= top)) (PreH16 : (top <= n_pre)) (PreH17 : (0 <= c0)) (PreH18 : (0 <= c1)) (PreH19 : ((c0 + c1 ) <= n_pre)) (PreH20 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1 ))) (PreH22 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH23 : (ColourValues n_pre before )) (PreH24 : (ParityRespected comments before )) (PreH25 : (ColouredClosed comments before )) (PreH26 : (MaxImpostersOn n_pre comments before total )) (PreH27 : forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1)))) (PreH28 : ((Znth s before 0) = (-1))) (PreH29 : ((Znth s cs 0) <> (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 )) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws )) (PreH33 : (top <> 0)),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
|--
  “ ((Znth (Znth (top - 1 ) ks 0) cs 0) <> 0) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v: Z), (((1 <= v) /\ (v < s)) -> ((Znth v before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist (0) (top) (ks)) c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  “ (top <> 0) ”
  &&  (((head_pre + ((Znth (top - 1 ) ks 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (top - 1 ) ks 0) hs 0))
  **  (IntArray.missing_i head_pre (Znth (top - 1 ) ks 0) 0 (n_pre + 1 ) hs )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
.

Definition solver_partial_solve_wit_24 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 0)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + (u * sizeof(INT)))) # Int  |-> (Znth u cs 0))
  **  (IntArray.missing_i color_pre u 0 (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_25 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 0)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((wt_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ws 0))
  **  (IntArray.missing_i wt_pre e 0 (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_26 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 1)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + (u * sizeof(INT)))) # Int  |-> (Znth u cs 0))
  **  (IntArray.missing_i color_pre u 0 (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_27 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 1)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((wt_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ws 0))
  **  (IntArray.missing_i wt_pre e 0 (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_28 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 0)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((to_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ts 0))
  **  (IntArray.missing_i to_pre e 0 (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_29 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 1)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((to_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ts 0))
  **  (IntArray.missing_i to_pre e 0 (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_30 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 0)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + ((Znth e ts 0) * sizeof(INT)))) # Int  |-> (Znth (Znth e ts 0) cs 0))
  **  (IntArray.missing_i color_pre (Znth e ts 0) 0 (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_31 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : (0 <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs 0) = 1)) (PreH18 : (0 <= top)) (PreH19 : (top <= n_pre)) (PreH20 : (0 <= c0)) (PreH21 : (0 <= c1)) (PreH22 : ((c0 + c1 ) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre ))) (PreH25 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH26 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH27 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1 ))) (PreH29 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH30 : (ColourValues n_pre before )) (PreH31 : (ParityRespected comments before )) (PreH32 : (ColouredClosed comments before )) (PreH33 : (MaxImpostersOn n_pre comments before total )) (PreH34 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH35 : ((Znth s before 0) = (-1))) (PreH36 : ((Znth s cs 0) <> (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + ((Znth e ts 0) * sizeof(INT)))) # Int  |-> (Znth (Znth e ts 0) cs 0))
  **  (IntArray.missing_i color_pre (Znth e ts 0) 0 (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_32 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 0)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) < 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + ((Znth e ts 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i color_pre (Znth e ts 0) 0 (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_33 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 1)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) < 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + ((Znth e ts 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i color_pre (Znth e ts 0) 0 (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_34 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 0)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) < 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((stack__pre + (top * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i stack__pre top 0 (n_pre + 1 ) ks )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
.

Definition solver_partial_solve_wit_35 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 1)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) < 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((stack__pre + (top * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i stack__pre top 0 (n_pre + 1 ) ks )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
.

Definition solver_partial_solve_wit_36 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 0)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) >= 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + ((Znth e ts 0) * sizeof(INT)))) # Int  |-> (Znth (Znth e ts 0) cs 0))
  **  (IntArray.missing_i color_pre (Znth e ts 0) 0 (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_37 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 1)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) >= 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((color_pre + ((Znth e ts 0) * sizeof(INT)))) # Int  |-> (Znth (Znth e ts 0) cs 0))
  **  (IntArray.missing_i color_pre (Znth e ts 0) 0 (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_38 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 0)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts 0)) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
|--
  “ ((Znth (Znth e ts 0) cs 0) < 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ns 0))
  **  (IntArray.missing_i nxt_pre e 0 (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts 0)) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
.

Definition solver_partial_solve_wit_39 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : (0 <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs 0) = 1)) (PreH19 : (0 <= top)) (PreH20 : (top <= n_pre)) (PreH21 : (0 <= c0)) (PreH22 : (0 <= c1)) (PreH23 : ((c0 + c1 ) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre ))) (PreH26 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH27 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH28 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1 ))) (PreH30 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH31 : (ColourValues n_pre before )) (PreH32 : (ParityRespected comments before )) (PreH33 : (ColouredClosed comments before )) (PreH34 : (MaxImpostersOn n_pre comments before total )) (PreH35 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH36 : ((Znth s before 0) = (-1))) (PreH37 : ((Znth s cs 0) <> (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts 0)) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
|--
  “ ((Znth (Znth e ts 0) cs 0) < 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ns 0))
  **  (IntArray.missing_i nxt_pre e 0 (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) (replace_Znth (top) ((Znth e ts 0)) (ks)) )
  **  (IntArray.full color_pre (n_pre + 1 ) (replace_Znth ((Znth e ts 0)) ((Z.lxor (Znth u cs 0) (Znth e ws 0))) (cs)) )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
.

Definition solver_partial_solve_wit_40 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) = (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 0)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) = (Z.lxor (Znth u cs 0) (Znth e ws 0))) ”
  &&  “ ((Znth (Znth e ts 0) cs 0) >= 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 0) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ns 0))
  **  (IntArray.missing_i nxt_pre e 0 (2 * m_pre ) ns )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
.

Definition solver_partial_solve_wit_41 :=
forall (comment_kinds: (@list Z)) (comment_targets: (@list Z)) (comment_sources: (@list Z)) (comments: (@list ((Z * Z) * Z))) (n_pre: Z) (m_pre: Z) (comment_u_pre: Z) (comment_v_pre: Z) (comment_diff_pre: Z) (head_pre: Z) (nxt_pre: Z) (to_pre: Z) (wt_pre: Z) (color_pre: Z) (stack__pre: Z) (hs: (@list Z)) (finished: (@list Z)) (before: (@list Z)) (ks: (@list Z)) (ns: (@list Z)) (ws: (@list Z)) (ts: (@list Z)) (e: Z) (c1: Z) (c0: Z) (top: Z) (cs: (@list Z)) (u: Z) (total: Z) (s: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((Znth (Znth e ts 0) cs 0) = (Z.lxor (Znth u cs 0) (Znth e ws 0)))) (PreH2 : ((Znth (Znth e ts 0) cs 0) >= 0)) (PreH3 : (e <> (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : (0 <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs 0) = 1)) (PreH20 : (0 <= top)) (PreH21 : (top <= n_pre)) (PreH22 : (0 <= c0)) (PreH23 : (0 <= c1)) (PreH24 : ((c0 + c1 ) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre ))) (PreH27 : ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre ))))) (PreH28 : (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre))) (PreH29 : forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1 ))) (PreH31 : ((Zlength (ks)) = (n_pre + 1 ))) (PreH32 : (ColourValues n_pre before )) (PreH33 : (ParityRespected comments before )) (PreH34 : (ColouredClosed comments before )) (PreH35 : (MaxImpostersOn n_pre comments before total )) (PreH36 : forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1)))) (PreH37 : ((Znth s before 0) = (-1))) (PreH38 : ((Znth s cs 0) <> (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 )) (PreH40 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments )) (PreH41 : (ForwardStarRanges n_pre m_pre hs ns ts ws )),
  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full nxt_pre (2 * m_pre ) ns )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
|--
  “ ((Znth (Znth e ts 0) cs 0) = (Z.lxor (Znth u cs 0) (Znth e ws 0))) ”
  &&  “ ((Znth (Znth e ts 0) cs 0) >= 0) ”
  &&  “ (e <> (-1)) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ (0 <= m_pre) ”
  &&  “ (m_pre <= 500000) ”
  &&  “ (m_pre = (Zlength (comments))) ”
  &&  “ ((Zlength (comment_sources)) = m_pre) ”
  &&  “ ((Zlength (comment_targets)) = m_pre) ”
  &&  “ ((Zlength (comment_kinds)) = m_pre) ”
  &&  “ forall (q: Z), (((0 <= q) /\ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources 0)) /\ ((Znth q comment_sources 0) <= n_pre)) /\ (1 <= (Znth q comment_targets 0))) /\ ((Znth q comment_targets 0) <= n_pre)) /\ ((Znth q comment_sources 0) <> (Znth q comment_targets 0))) /\ (((Znth q comment_kinds 0) = 0) \/ ((Znth q comment_kinds 0) = 1))) /\ ((Znth q comment_sources 0) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_targets 0) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth q comment_kinds 0) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (1 <= s) ”
  &&  “ (s <= n_pre) ”
  &&  “ (0 <= total) ”
  &&  “ (total <= n_pre) ”
  &&  “ (1 <= u) ”
  &&  “ (u <= n_pre) ”
  &&  “ ((Znth u cs 0) = 1) ”
  &&  “ (0 <= top) ”
  &&  “ (top <= n_pre) ”
  &&  “ (0 <= c0) ”
  &&  “ (0 <= c1) ”
  &&  “ ((c0 + c1 ) <= n_pre) ”
  &&  “ ((-1) <= e) ”
  &&  “ (e < (2 * m_pre )) ”
  &&  “ ((e <> (-1)) -> (((((1 <= (Znth e ts 0)) /\ ((Znth e ts 0) <= n_pre)) /\ (((Znth e ws 0) = 0) \/ ((Znth e ws 0) = 1))) /\ ((-1) <= (Znth e ns 0))) /\ ((Znth e ns 0) < (2 * m_pre )))) ”
  &&  “ (((e <> (-1)) /\ ((Znth (Znth e ts 0) cs 0) < 0)) -> (top < n_pre)) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < top)) -> ((1 <= (Znth j ks 0)) /\ ((Znth j ks 0) <= n_pre))) ”
  &&  “ ((Zlength (before)) = (n_pre + 1 )) ”
  &&  “ ((Zlength (ks)) = (n_pre + 1 )) ”
  &&  “ (ColourValues n_pre before ) ”
  &&  “ (ParityRespected comments before ) ”
  &&  “ (ColouredClosed comments before ) ”
  &&  “ (MaxImpostersOn n_pre comments before total ) ”
  &&  “ forall (v0: Z), (((1 <= v0) /\ (v0 < s)) -> ((Znth v0 before 0) <> (-1))) ”
  &&  “ ((Znth s before 0) = (-1)) ”
  &&  “ ((Znth s cs 0) <> (-1)) ”
  &&  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist (0) (top) (ks)) u e c0 c1 ) ”
  &&  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments ) ”
  &&  “ (ForwardStarRanges n_pre m_pre hs ns ts ws ) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int  |-> (Znth e ns 0))
  **  (IntArray.missing_i nxt_pre e 0 (2 * m_pre ) ns )
  **  (IntArray.full color_pre (n_pre + 1 ) cs )
  **  (IntArray.full wt_pre (2 * m_pre ) ws )
  **  (IntArray.full to_pre (2 * m_pre ) ts )
  **  (IntArray.full comment_u_pre m_pre comment_sources )
  **  (IntArray.full comment_v_pre m_pre comment_targets )
  **  (IntArray.full comment_diff_pre m_pre comment_kinds )
  **  (IntArray.full head_pre (n_pre + 1 ) hs )
  **  (IntArray.full stack__pre (n_pre + 1 ) ks )
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
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Axiom proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
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
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.
Axiom proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34.
Axiom proof_of_solver_partial_solve_wit_35 : solver_partial_solve_wit_35.
Axiom proof_of_solver_partial_solve_wit_36 : solver_partial_solve_wit_36.
Axiom proof_of_solver_partial_solve_wit_37 : solver_partial_solve_wit_37.
Axiom proof_of_solver_partial_solve_wit_38 : solver_partial_solve_wit_38.
Axiom proof_of_solver_partial_solve_wit_39 : solver_partial_solve_wit_39.
Axiom proof_of_solver_partial_solve_wit_40 : solver_partial_solve_wit_40.
Axiom proof_of_solver_partial_solve_wit_41 : solver_partial_solve_wit_41.

End VC_Correct.
