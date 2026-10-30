From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_copyi -----*)

Definition mpn_copyi_safety_wit_1_shifted :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  “ ((False \/ (True /\ (off_shifted = 0))) \/ (True /\ (off_shifted > 0))) ”
.

Definition mpn_copyi_safety_wit_2_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyi_safety_wit_3_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyi_safety_wit_4_non_alias :=
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH3 : (list_within_bound UINT_MOD l )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.undef_full d_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyi_safety_wit_5_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_copyi_safety_wit_6_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre i (i + 1 ) (replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted)))) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_copyi_safety_wit_7_non_alias :=
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full d_pre (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_copyi_entail_wit_1_off_zero :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
).

Definition mpn_copyi_entail_wit_1_off_zero_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)),
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyi_entail_wit_2_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)),
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)),
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_entail_wit_2_off_pos_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)),
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_entail_wit_3_off_zero :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (s_pre = d_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (sublist (0) (0) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  TT && emp 
|--
  “ ((@nil Z) = (sublist (0) (0) (l_shifted))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_3_off_zero_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  ((@nil Z) = (sublist (0) (0) (l_shifted)))
.

Definition mpn_copyi_entail_wit_4_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (sublist (off_shifted) ((off_shifted + 0 )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  TT && emp 
|--
  “ ((@nil Z) = (sublist (off_shifted) ((off_shifted + 0 )) (l_shifted))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_4_off_pos_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )),
  ((@nil Z) = (sublist (off_shifted) ((off_shifted + 0 )) (l_shifted)))
.

Definition mpn_copyi_entail_wit_5_non_alias :=
(
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH3 : (list_within_bound UINT_MOD l )),
  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre 0 (sublist (0) (0) (l)) )
  **  (UIntArray.undef_seg d_pre 0 n_pre )
  **  (UIntArray.full s_pre n_pre l )
) \/
(
forall (val_non_alias: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH3 : (list_within_bound UINT_MOD l )),
  TT && emp 
|--
  “ (0 <= n_pre) ”
  &&  “ ((sublist (0) (0) (l)) = (@nil Z)) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_5_non_alias_split_goal_1 :=
forall (val_non_alias: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH3 : (list_within_bound UINT_MOD l )),
  (0 <= n_pre)
.

Definition mpn_copyi_entail_wit_5_non_alias_split_goal_2 :=
forall (val_non_alias: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH3 : (list_within_bound UINT_MOD l )),
  ((sublist (0) (0) (l)) = (@nil Z))
.

Definition mpn_copyi_entail_wit_6_off_zero :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  ((( &( "s" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (s_pre = d_pre) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg d_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  TT && emp 
|--
  “ ((sublist (0) ((i + 1 )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) ((i + 1 )) (l_shifted))))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_6_off_zero_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  ((sublist (0) ((i + 1 )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) ((i + 1 )) (l_shifted)))))
.

Definition mpn_copyi_entail_wit_7_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre i (i + 1 ) (replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted)))) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 (i + 1 ) (sublist (off_shifted) ((off_shifted + (i + 1 ) )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ ((sublist (off_shifted) ((off_shifted + (i + 1 ) )) (l_shifted)) = (app ((sublist (off_shifted) ((off_shifted + i )) (l_shifted))) ((replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted))))))) ”
  &&  (UIntArray.seg d_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_entail_wit_7_off_pos_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ ((sublist (off_shifted) ((off_shifted + (i + 1 ) )) (l_shifted)) = (app ((sublist (off_shifted) ((off_shifted + i )) (l_shifted))) ((replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted))))))) ”
.

Definition mpn_copyi_entail_wit_7_off_pos_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_entail_wit_8_non_alias :=
(
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full d_pre (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre (i + 1 ) (sublist (0) ((i + 1 )) (l)) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
) \/
(
forall (val_non_alias: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_8_non_alias_split_goal_1 :=
forall (val_non_alias: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  ((app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l)))
.

Definition mpn_copyi_return_wit_1_off_zero :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  TT && emp 
|--
  “ ((sublist (0) ((0 + n_pre )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) (n_pre) (l_shifted))))) ”
  &&  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_return_wit_1_off_zero_split_goal_1 :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  ((sublist (0) ((0 + n_pre )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) (n_pre) (l_shifted)))))
.

Definition mpn_copyi_return_wit_1_off_zero_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  TT && emp 
|--
  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_return_wit_2_off_pos :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_return_wit_2_off_pos_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_return_wit_3_non_alias :=
(
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val_non_alias n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val_non_alias n_pre )
) \/
(
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val_non_alias n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val_non_alias n_pre )
).

Definition mpn_copyi_return_wit_3_non_alias_split_goal_spatial :=
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val_non_alias n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val_non_alias n_pre )
.

Definition mpn_copyi_partial_solve_wit_1_non_alias :=
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z),
  (mpd_store_Z UINT_MOD s_pre val_non_alias n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  (mpd_store_Z UINT_MOD s_pre val_non_alias n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
.

Definition mpn_copyi_partial_solve_wit_2_off_zero_pure :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  “ (d_pre = d_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
.

Definition mpn_copyi_partial_solve_wit_2_off_zero_aux :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  “ (d_pre = d_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (i < n_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (s_pre = d_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_2_off_zero := mpn_copyi_partial_solve_wit_2_off_zero_pure -> mpn_copyi_partial_solve_wit_2_off_zero_aux.

Definition mpn_copyi_partial_solve_wit_3_off_pos_pure :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
.

Definition mpn_copyi_partial_solve_wit_3_off_pos_aux :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (i < n_pre) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_3_off_pos := mpn_copyi_partial_solve_wit_3_off_pos_pure -> mpn_copyi_partial_solve_wit_3_off_pos_aux.

Definition mpn_copyi_partial_solve_wit_4_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (d_pre = d_pre)) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted = 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (s_pre = d_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted = 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ (i < n_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (s_pre = d_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) ((i + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i d_pre i i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_5_off_zero :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ (i < n_pre) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ (s_pre = d_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted = 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i d_pre i i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_6_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i s_pre i i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_7_off_pos :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )),
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (i < n_pre) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  “ (off_shifted > 0) ”
  &&  “ (n_pre >= 0) ”
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ”
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i d_pre i i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_8_non_alias :=
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((s_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i s_pre i 0 n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
.

Definition mpn_copyi_partial_solve_wit_9_non_alias :=
forall (val_non_alias: Z) (d_pre: Z) (s_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
.

Definition mpn_copyi_which_implies_wit_1 :=
(
forall (val_non_alias: Z) (n: Z) (s: Z),
  (mpd_store_Z UINT_MOD s val_non_alias n )
|--
  EX (l: (@list Z)),
  “ ((Zlength (l)) = n) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full s n l )
) \/
(
forall (val_non_alias: Z) (n: Z) (s: Z),
  (mpd_store_Z UINT_MOD s val_non_alias n )
|--
  EX (l: (@list Z)),
  “ ((Zlength (l)) = n) ”
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full s n l )
).

Definition mpn_copyi_which_implies_wit_2 :=
(
forall (l_shifted: (@list Z)) (d_pre: Z) (n_pre: Z) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)),
  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  “ (s = d_pre) ”
  &&  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (l_shifted: (@list Z)) (d_pre: Z) (n_pre: Z) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)),
  TT && emp 
|--
  “ ((sublist (i) (n_pre) (l_shifted)) = (app ((sublist (i) ((i + 1 )) (l_shifted))) ((sublist ((i + 1 )) (n_pre) (l_shifted))))) ”
  &&  “ ((Zlength ((sublist (i) ((i + 1 )) (l_shifted)))) = ((i + 1 ) - i )) ”
  &&  emp
).

Definition mpn_copyi_which_implies_wit_2_split_goal_1 :=
forall (l_shifted: (@list Z)) (d_pre: Z) (n_pre: Z) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)),
  ((sublist (i) (n_pre) (l_shifted)) = (app ((sublist (i) ((i + 1 )) (l_shifted))) ((sublist ((i + 1 )) (n_pre) (l_shifted)))))
.

Definition mpn_copyi_which_implies_wit_2_split_goal_2 :=
forall (l_shifted: (@list Z)) (d_pre: Z) (n_pre: Z) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)),
  ((Zlength ((sublist (i) ((i + 1 )) (l_shifted)))) = ((i + 1 ) - i ))
.

Definition mpn_copyi_which_implies_wit_3 :=
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))),
  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))),
  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_which_implies_wit_3_split_goal_spatial :=
forall (off_shifted: Z) (l_shifted: (@list Z)) (d_pre: Z) (s_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))),
  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_copyi_safety_wit_1_shifted : mpn_copyi_safety_wit_1_shifted.
Axiom proof_of_mpn_copyi_safety_wit_2_off_zero : mpn_copyi_safety_wit_2_off_zero.
Axiom proof_of_mpn_copyi_safety_wit_3_off_pos : mpn_copyi_safety_wit_3_off_pos.
Axiom proof_of_mpn_copyi_safety_wit_4_non_alias : mpn_copyi_safety_wit_4_non_alias.
Axiom proof_of_mpn_copyi_safety_wit_5_off_zero : mpn_copyi_safety_wit_5_off_zero.
Axiom proof_of_mpn_copyi_safety_wit_6_off_pos : mpn_copyi_safety_wit_6_off_pos.
Axiom proof_of_mpn_copyi_safety_wit_7_non_alias : mpn_copyi_safety_wit_7_non_alias.
Axiom proof_of_mpn_copyi_entail_wit_1_off_zero : mpn_copyi_entail_wit_1_off_zero.
Axiom proof_of_mpn_copyi_entail_wit_2_off_pos : mpn_copyi_entail_wit_2_off_pos.
Axiom proof_of_mpn_copyi_entail_wit_3_off_zero : mpn_copyi_entail_wit_3_off_zero.
Axiom proof_of_mpn_copyi_entail_wit_4_off_pos : mpn_copyi_entail_wit_4_off_pos.
Axiom proof_of_mpn_copyi_entail_wit_5_non_alias : mpn_copyi_entail_wit_5_non_alias.
Axiom proof_of_mpn_copyi_entail_wit_6_off_zero : mpn_copyi_entail_wit_6_off_zero.
Axiom proof_of_mpn_copyi_entail_wit_7_off_pos : mpn_copyi_entail_wit_7_off_pos.
Axiom proof_of_mpn_copyi_entail_wit_8_non_alias : mpn_copyi_entail_wit_8_non_alias.
Axiom proof_of_mpn_copyi_return_wit_1_off_zero : mpn_copyi_return_wit_1_off_zero.
Axiom proof_of_mpn_copyi_return_wit_2_off_pos : mpn_copyi_return_wit_2_off_pos.
Axiom proof_of_mpn_copyi_return_wit_3_non_alias : mpn_copyi_return_wit_3_non_alias.
Axiom proof_of_mpn_copyi_partial_solve_wit_1_non_alias : mpn_copyi_partial_solve_wit_1_non_alias.
Axiom proof_of_mpn_copyi_partial_solve_wit_2_off_zero_pure : mpn_copyi_partial_solve_wit_2_off_zero_pure.
Axiom proof_of_mpn_copyi_partial_solve_wit_2_off_zero : mpn_copyi_partial_solve_wit_2_off_zero.
Axiom proof_of_mpn_copyi_partial_solve_wit_3_off_pos_pure : mpn_copyi_partial_solve_wit_3_off_pos_pure.
Axiom proof_of_mpn_copyi_partial_solve_wit_3_off_pos : mpn_copyi_partial_solve_wit_3_off_pos.
Axiom proof_of_mpn_copyi_partial_solve_wit_4_off_zero : mpn_copyi_partial_solve_wit_4_off_zero.
Axiom proof_of_mpn_copyi_partial_solve_wit_5_off_zero : mpn_copyi_partial_solve_wit_5_off_zero.
Axiom proof_of_mpn_copyi_partial_solve_wit_6_off_pos : mpn_copyi_partial_solve_wit_6_off_pos.
Axiom proof_of_mpn_copyi_partial_solve_wit_7_off_pos : mpn_copyi_partial_solve_wit_7_off_pos.
Axiom proof_of_mpn_copyi_partial_solve_wit_8_non_alias : mpn_copyi_partial_solve_wit_8_non_alias.
Axiom proof_of_mpn_copyi_partial_solve_wit_9_non_alias : mpn_copyi_partial_solve_wit_9_non_alias.
Axiom proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Axiom proof_of_mpn_copyi_which_implies_wit_2 : mpn_copyi_which_implies_wit_2.
Axiom proof_of_mpn_copyi_which_implies_wit_3 : mpn_copyi_which_implies_wit_3.

End VC_Correct.
