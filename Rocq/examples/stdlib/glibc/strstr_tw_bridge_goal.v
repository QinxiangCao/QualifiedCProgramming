From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.strstr_tw_bridge_lib.
Local Open Scope sac.

(*----- Function strstr_tw_bridge -----*)

Definition strstr_tw_bridge_entail_wit_1 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (known_pre: Z) (ne_pre: Z) (nl_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl_pre )) (PreH6 : (256 < nl_pre)) (PreH7 : (nl_pre <= known_pre)) (PreH8 : (known_pre <= hl)),
  (UCharArray.full base length bytes )
|--
  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl_pre ) ”
  &&  “ (256 < nl_pre) ”
  &&  “ (nl_pre <= known_pre) ”
  &&  “ (known_pre <= hl) ”
  &&  “ (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) ) ”
  &&  (UCharArray.full hs_pre hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne_pre nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs_pre hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (known_pre: Z) (ne_pre: Z) (nl_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl_pre )) (PreH6 : (256 < nl_pre)) (PreH7 : (nl_pre <= known_pre)) (PreH8 : (known_pre <= hl)),
  (UCharArray.full base length bytes )
|--
  “ (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) ) ”
  &&  (UCharArray.full hs_pre hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne_pre nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs_pre hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
).

Definition strstr_tw_bridge_entail_wit_1_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (known_pre: Z) (ne_pre: Z) (nl_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl_pre )) (PreH6 : (256 < nl_pre)) (PreH7 : (nl_pre <= known_pre)) (PreH8 : (known_pre <= hl)),
  (UCharArray.full base length bytes )
|--
  “ (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) ) ”
.

Definition strstr_tw_bridge_entail_wit_1_split_goal_spatial :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (known_pre: Z) (ne_pre: Z) (nl_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl_pre )) (PreH6 : (256 < nl_pre)) (PreH7 : (nl_pre <= known_pre)) (PreH8 : (known_pre <= hl)),
  (UCharArray.full base length bytes )
|--
  (UCharArray.full hs_pre hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne_pre nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs_pre hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
.

Definition strstr_tw_bridge_entail_wit_2 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (ret: (@option Z)) (retval: Z) (PreH1 : (match_post (sublist (ho) ((ho + hl )) (bytes)) (sublist (no) ((no + nl_pre )) (bytes)) ret )) (PreH2 : ((uchar_ptr_option_repr (hs) (retval) (sizeof(UCHAR))) = ret)) (PreH3 : (hs = (base + ho ))) (PreH4 : (ne = (base + no ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl_pre )) (PreH8 : (256 < nl_pre)) (PreH9 : (nl_pre <= known)) (PreH10 : (known <= hl)) (PreH11 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ (hs = (base + ho )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (nl_pre <= known) ”
  &&  “ (known <= hl) ”
  &&  “ (hp_result bytes base ho hl no nl_pre retval ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (ret: (@option Z)) (retval: Z) (PreH1 : (match_post (sublist (ho) ((ho + hl )) (bytes)) (sublist (no) ((no + nl_pre )) (bytes)) ret )) (PreH2 : ((uchar_ptr_option_repr (hs) (retval) (sizeof(UCHAR))) = ret)) (PreH3 : (hs = (base + ho ))) (PreH4 : (ne = (base + no ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl_pre )) (PreH8 : (256 < nl_pre)) (PreH9 : (nl_pre <= known)) (PreH10 : (known <= hl)) (PreH11 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ (hp_result bytes base ho hl no nl_pre retval ) ”
  &&  (UCharArray.full base length bytes )
).

Definition strstr_tw_bridge_entail_wit_2_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (ret: (@option Z)) (retval: Z) (PreH1 : (match_post (sublist (ho) ((ho + hl )) (bytes)) (sublist (no) ((no + nl_pre )) (bytes)) ret )) (PreH2 : ((uchar_ptr_option_repr (hs) (retval) (sizeof(UCHAR))) = ret)) (PreH3 : (hs = (base + ho ))) (PreH4 : (ne = (base + no ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl_pre )) (PreH8 : (256 < nl_pre)) (PreH9 : (nl_pre <= known)) (PreH10 : (known <= hl)) (PreH11 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ (hp_result bytes base ho hl no nl_pre retval ) ”
.

Definition strstr_tw_bridge_entail_wit_2_split_goal_spatial :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (ret: (@option Z)) (retval: Z) (PreH1 : (match_post (sublist (ho) ((ho + hl )) (bytes)) (sublist (no) ((no + nl_pre )) (bytes)) ret )) (PreH2 : ((uchar_ptr_option_repr (hs) (retval) (sizeof(UCHAR))) = ret)) (PreH3 : (hs = (base + ho ))) (PreH4 : (ne = (base + no ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl_pre )) (PreH8 : (256 < nl_pre)) (PreH9 : (nl_pre <= known)) (PreH10 : (known <= hl)) (PreH11 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  (UCharArray.full base length bytes )
.

Definition strstr_tw_bridge_return_wit_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (r: Z) (PreH1 : (hs = (base + ho ))) (PreH2 : (ne = (base + no ))) (PreH3 : (nl_pre <= known)) (PreH4 : (known <= hl)) (PreH5 : (hp_result bytes base ho hl no nl_pre r )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl_pre r ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_tw_bridge_partial_solve_wit_1_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (hs = (base + ho ))) (PreH2 : (ne = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl_pre )) (PreH6 : (256 < nl_pre)) (PreH7 : (nl_pre <= known)) (PreH8 : (known <= hl)) (PreH9 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  ((( &( "r" ) )) # Ptr  |->_)
  **  ((( &( "nl" ) )) # Int  |-> nl_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "known" ) )) # UInt64  |-> known)
  **  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) ) ”
  &&  “ (nl_pre <= known) ”
  &&  “ (known <= hl) ”
  &&  “ (nl_pre = nl_pre) ”
  &&  “ (32 < nl_pre) ”
  &&  “ (nl_pre <= hl) ”
  &&  “ (hs > 0) ”
  &&  “ (ne > 0) ”
  &&  “ ((base + no ) > 0) ”
  &&  “ ((base + ho ) > 0) ”
  &&  “ (hl <= INT_MAX) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (known <= UINT64_MAX)) (PreH2 : (known >= 0)) (PreH3 : (nl_pre <= INT_MAX)) (PreH4 : (nl_pre >= INT_MIN)) (PreH5 : (hs = (base + ho ))) (PreH6 : (ne = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl_pre )) (PreH10 : (256 < nl_pre)) (PreH11 : (nl_pre <= known)) (PreH12 : (known <= hl)) (PreH13 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  ((( &( "r" ) )) # Ptr  |->_)
  **  ((( &( "nl" ) )) # Int  |-> nl_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "known" ) )) # UInt64  |-> known)
  **  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ (hl <= INT_MAX) ”
  &&  “ ((base + ho ) > 0) ”
  &&  “ ((base + no ) > 0) ”
  &&  “ ((base + no ) > 0) ”
  &&  “ ((base + ho ) > 0) ”
).

Definition strstr_tw_bridge_partial_solve_wit_1_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (known <= UINT64_MAX)) (PreH2 : (known >= 0)) (PreH3 : (nl_pre <= INT_MAX)) (PreH4 : (nl_pre >= INT_MIN)) (PreH5 : (hs = (base + ho ))) (PreH6 : (ne = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl_pre )) (PreH10 : (256 < nl_pre)) (PreH11 : (nl_pre <= known)) (PreH12 : (known <= hl)) (PreH13 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  ((( &( "r" ) )) # Ptr  |->_)
  **  ((( &( "nl" ) )) # Int  |-> nl_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "known" ) )) # UInt64  |-> known)
  **  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ (hl <= INT_MAX) ”
.

Definition strstr_tw_bridge_partial_solve_wit_1_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (known <= UINT64_MAX)) (PreH2 : (known >= 0)) (PreH3 : (nl_pre <= INT_MAX)) (PreH4 : (nl_pre >= INT_MIN)) (PreH5 : (hs = (base + ho ))) (PreH6 : (ne = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl_pre )) (PreH10 : (256 < nl_pre)) (PreH11 : (nl_pre <= known)) (PreH12 : (known <= hl)) (PreH13 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  ((( &( "r" ) )) # Ptr  |->_)
  **  ((( &( "nl" ) )) # Int  |-> nl_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "known" ) )) # UInt64  |-> known)
  **  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ ((base + ho ) > 0) ”
.

Definition strstr_tw_bridge_partial_solve_wit_1_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (known <= UINT64_MAX)) (PreH2 : (known >= 0)) (PreH3 : (nl_pre <= INT_MAX)) (PreH4 : (nl_pre >= INT_MIN)) (PreH5 : (hs = (base + ho ))) (PreH6 : (ne = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl_pre )) (PreH10 : (256 < nl_pre)) (PreH11 : (nl_pre <= known)) (PreH12 : (known <= hl)) (PreH13 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  ((( &( "r" ) )) # Ptr  |->_)
  **  ((( &( "nl" ) )) # Int  |-> nl_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "known" ) )) # UInt64  |-> known)
  **  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ ((base + no ) > 0) ”
.

Definition strstr_tw_bridge_partial_solve_wit_1_pure_split_goal_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (known <= UINT64_MAX)) (PreH2 : (known >= 0)) (PreH3 : (nl_pre <= INT_MAX)) (PreH4 : (nl_pre >= INT_MIN)) (PreH5 : (hs = (base + ho ))) (PreH6 : (ne = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl_pre )) (PreH10 : (256 < nl_pre)) (PreH11 : (nl_pre <= known)) (PreH12 : (known <= hl)) (PreH13 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  ((( &( "r" ) )) # Ptr  |->_)
  **  ((( &( "nl" ) )) # Int  |-> nl_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "known" ) )) # UInt64  |-> known)
  **  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ ((base + no ) > 0) ”
.

Definition strstr_tw_bridge_partial_solve_wit_1_pure_split_goal_5 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (known <= UINT64_MAX)) (PreH2 : (known >= 0)) (PreH3 : (nl_pre <= INT_MAX)) (PreH4 : (nl_pre >= INT_MIN)) (PreH5 : (hs = (base + ho ))) (PreH6 : (ne = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl_pre )) (PreH10 : (256 < nl_pre)) (PreH11 : (nl_pre <= known)) (PreH12 : (known <= hl)) (PreH13 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  ((( &( "r" ) )) # Ptr  |->_)
  **  ((( &( "nl" ) )) # Int  |-> nl_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "known" ) )) # UInt64  |-> known)
  **  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ ((base + ho ) > 0) ”
.

Definition strstr_tw_bridge_partial_solve_wit_1_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (nl_pre: Z) (hs: Z) (ne: Z) (known: Z) (PreH1 : (hs = (base + ho ))) (PreH2 : (ne = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl_pre )) (PreH6 : (256 < nl_pre)) (PreH7 : (nl_pre <= known)) (PreH8 : (known <= hl)) (PreH9 : (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) )),
  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
|--
  “ (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) ) ”
  &&  “ (nl_pre <= known) ”
  &&  “ (known <= hl) ”
  &&  “ (nl_pre = nl_pre) ”
  &&  “ (32 < nl_pre) ”
  &&  “ (nl_pre <= hl) ”
  &&  “ (hs > 0) ”
  &&  “ (ne > 0) ”
  &&  “ ((base + no ) > 0) ”
  &&  “ ((base + ho ) > 0) ”
  &&  “ (hl <= INT_MAX) ”
  &&  “ (hs = (base + ho )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl_pre ) ”
  &&  “ (256 < nl_pre) ”
  &&  “ (nl_pre <= known) ”
  &&  “ (known <= hl) ”
  &&  “ (tw_nonzero_bytes (sublist (ho) ((ho + hl )) (bytes)) ) ”
  &&  (UCharArray.full hs hl (sublist (ho) ((ho + hl )) (bytes)) )
  **  (UCharArray.full ne nl_pre (sublist (no) ((no + nl_pre )) (bytes)) )
  **  (tw_terminator hs hl )
  **  (gs_tw_frame base length bytes ho hl no nl_pre )
.

Definition strstr_tw_bridge_partial_solve_wit_1 := strstr_tw_bridge_partial_solve_wit_1_pure -> strstr_tw_bridge_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_strstr_tw_bridge_entail_wit_1 : strstr_tw_bridge_entail_wit_1.
Axiom proof_of_strstr_tw_bridge_entail_wit_2 : strstr_tw_bridge_entail_wit_2.
Axiom proof_of_strstr_tw_bridge_return_wit_1 : strstr_tw_bridge_return_wit_1.
Axiom proof_of_strstr_tw_bridge_partial_solve_wit_1_pure : strstr_tw_bridge_partial_solve_wit_1_pure.
Axiom proof_of_strstr_tw_bridge_partial_solve_wit_1 : strstr_tw_bridge_partial_solve_wit_1.

End VC_Correct.
