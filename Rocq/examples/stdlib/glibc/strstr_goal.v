From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.strstr_lib.
Local Open Scope sac.

(*----- Function gs_read -----*)

Definition gs_read_safety_wit_1 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  ((( &( "p" ) )) # Ptr  |-> p)
  **  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gs_read_entail_wit_1 :=
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p_pre: Z) (PreH1 : (p_pre = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.full base length bytes )
|--
  “ (p_pre = (base + index )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  (UCharArray.seg p_pre (0 - index ) (length - index ) bytes )
) \/
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p_pre: Z) (PreH1 : (p_pre = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.full base length bytes )
|--
  (UCharArray.seg p_pre (0 - index ) (length - index ) bytes )
).

Definition gs_read_entail_wit_1_split_goal_spatial :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p_pre: Z) (PreH1 : (p_pre = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.full base length bytes )
|--
  (UCharArray.seg p_pre (0 - index ) (length - index ) bytes )
.

Definition gs_read_return_wit_1 :=
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  “ ((Znth (0 - (0 - index ) ) bytes 0) = (Znth (index) (bytes) (0))) ”
  &&  “ (0 <= (Znth (0 - (0 - index ) ) bytes 0)) ”
  &&  “ ((Znth (0 - (0 - index ) ) bytes 0) < 256) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  “ ((Znth (0 - (0 - index ) ) bytes 0) < 256) ”
  &&  “ (0 <= (Znth (0 - (0 - index ) ) bytes 0)) ”
  &&  “ ((Znth (0 - (0 - index ) ) bytes 0) = (Znth (index) (bytes) (0))) ”
  &&  (UCharArray.full base length bytes )
).

Definition gs_read_return_wit_1_split_goal_1 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  “ ((Znth (0 - (0 - index ) ) bytes 0) < 256) ”
.

Definition gs_read_return_wit_1_split_goal_2 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  “ (0 <= (Znth (0 - (0 - index ) ) bytes 0)) ”
.

Definition gs_read_return_wit_1_split_goal_3 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  “ ((Znth (0 - (0 - index ) ) bytes 0) = (Znth (index) (bytes) (0))) ”
.

Definition gs_read_return_wit_1_split_goal_spatial :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  (UCharArray.full base length bytes )
.

Definition gs_read_partial_solve_wit_1 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (p: Z) (PreH1 : (p = (base + index ))) (PreH2 : (0 <= index)) (PreH3 : (index < length)) (PreH4 : (gs_bytes bytes )),
  (UCharArray.seg p (0 - index ) (length - index ) bytes )
|--
  “ (p = (base + index )) ”
  &&  “ (0 <= index) ”
  &&  “ (index < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  (((p + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0 - (0 - index ) ) bytes 0))
  **  (UCharArray.missing_i p 0 (0 - index ) (length - index ) bytes )
.

(*----- Function strstr2 -----*)

Definition strstr2_safety_wit_1 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^16) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^16) )) (32))) ”
  &&  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^16) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^16) )) (32))) ”
  &&  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
).

Definition strstr2_safety_wit_1_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^16) )) (32)) <= INT_MAX) ”
.

Definition strstr2_safety_wit_1_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^16) )) (32))) ”
.

Definition strstr2_safety_wit_1_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (16 <= 31) ”
.

Definition strstr2_safety_wit_1_split_goal_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= 16) ”
.

Definition strstr2_safety_wit_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition strstr2_safety_wit_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strstr2_safety_wit_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "h2" ) )) # UInt  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr2_safety_wit_5 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (hs = ((base + ho ) + pos ))) (PreH4 : (0 < base)) (PreH5 : ((base + length ) <= UINT_MAX)) (PreH6 : (gs_inputs bytes length ho hl no 2 )) (PreH7 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH8 : (0 <= pos)) (PreH9 : (pos <= hl)) (PreH10 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH11 : (0 <= c)) (PreH12 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr2_safety_wit_6 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition strstr2_safety_wit_7 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition strstr2_safety_wit_8 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ False ”
.

Definition strstr2_safety_wit_9 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )) (PreH9 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ False ”
.

Definition strstr2_safety_wit_10 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition strstr2_safety_wit_11 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )) (PreH9 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr2_entail_wit_1 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth (ho) (bytes) (0)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 < 256)) (PreH4 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (retval = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval)) (PreH9 : (retval < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
|--
  EX (pos: Z),
  “ (ne_pre = (base + no )) ”
  &&  “ (hs_pre = ((base + ho ) + pos )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 2 ) ”
  &&  “ (gs_short bytes ho hl no 2 pos (Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) 0 ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ (retval_3 = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth (ho) (bytes) (0)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 < 256)) (PreH4 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (retval = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval)) (PreH9 : (retval < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 2 )),
  TT && emp 
|--
  EX (pos: Z),
  “ ((base + ho ) = ((base + ho ) + pos )) ”
  &&  “ (gs_short bytes ho hl no 2 pos (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (no) (bytes) (0)) 16)) (32)) (Znth ((no + 1 )) (bytes) (0))) 0 ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ ((Znth (ho) (bytes) (0)) = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  emp
).

Definition strstr2_entail_wit_2 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos_2: Z) (hs: Z) (retval: Z) (PreH1 : (retval = (Znth (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (c <> 0)) (PreH5 : (h1 <> h2)) (PreH6 : (ne_pre = (base + no ))) (PreH7 : (hs = ((base + ho ) + pos_2 ))) (PreH8 : (0 < base)) (PreH9 : ((base + length ) <= UINT_MAX)) (PreH10 : (gs_inputs bytes length ho hl no 2 )) (PreH11 : (gs_short bytes ho hl no 2 pos_2 h1 h2 )) (PreH12 : (0 <= pos_2)) (PreH13 : (pos_2 <= hl)) (PreH14 : (c = (Znth ((ho + pos_2 )) (bytes) (0)))) (PreH15 : (0 <= c)) (PreH16 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  EX (pos: Z),
  “ (ne_pre = (base + no )) ”
  &&  “ ((hs + (1 * sizeof(UCHAR))) = ((base + ho ) + pos )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 2 ) ”
  &&  “ (gs_short bytes ho hl no 2 pos h1 (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ (retval = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos_2: Z) (hs: Z) (retval: Z) (PreH1 : (retval = (Znth (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (c <> 0)) (PreH5 : (h1 <> h2)) (PreH6 : (ne_pre = (base + no ))) (PreH7 : (hs = ((base + ho ) + pos_2 ))) (PreH8 : (0 < base)) (PreH9 : ((base + length ) <= UINT_MAX)) (PreH10 : (gs_inputs bytes length ho hl no 2 )) (PreH11 : (gs_short bytes ho hl no 2 pos_2 h1 h2 )) (PreH12 : (0 <= pos_2)) (PreH13 : (pos_2 <= hl)) (PreH14 : (c = (Znth ((ho + pos_2 )) (bytes) (0)))) (PreH15 : (0 <= c)) (PreH16 : (c < 256)),
  TT && emp 
|--
  EX (pos: Z),
  “ ((((base + ho ) + pos_2 ) + (1 * sizeof(UCHAR))) = ((base + ho ) + pos )) ”
  &&  “ (gs_short bytes ho hl no 2 pos h1 (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) (Znth ((ho + pos_2 )) (bytes) (0))) ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ ((Znth (((((base + ho ) + pos_2 ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) (bytes) (0)) = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  emp
).

Definition strstr2_return_wit_1 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no 2 (hs + ((-2) * sizeof(CHAR))) ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no 2 (((base + ho ) + pos ) + ((-2) * sizeof(CHAR))) ) ”
  &&  emp
).

Definition strstr2_return_wit_1_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  (hp_result bytes base ho hl no 2 (((base + ho ) + pos ) + ((-2) * sizeof(CHAR))) )
.

Definition strstr2_return_wit_2 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )) (PreH9 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no 2 0 ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )) (PreH9 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no 2 0 ) ”
  &&  emp
).

Definition strstr2_return_wit_2_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )) (PreH9 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  (hp_result bytes base ho hl no 2 0 )
.

Definition strstr2_partial_solve_wit_1_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (ne_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= no) ”
  &&  “ (no < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr2_partial_solve_wit_1_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= no) ”
.

Definition strstr2_partial_solve_wit_1_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (no < length) ”
.

Definition strstr2_partial_solve_wit_1_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr2_partial_solve_wit_1_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
|--
  “ (ne_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
  &&  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 2 ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr2_partial_solve_wit_1 := strstr2_partial_solve_wit_1_pure -> strstr2_partial_solve_wit_1_aux.

Definition strstr2_partial_solve_wit_2_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((ne_pre + (1 * sizeof(UCHAR))) = (base + (no + 1 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (0 <= (no + 1 )) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= (no + 1 )) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr2_partial_solve_wit_2_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= (no + 1 )) ”
.

Definition strstr2_partial_solve_wit_2_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((no + 1 ) < length) ”
.

Definition strstr2_partial_solve_wit_2_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr2_partial_solve_wit_2_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
|--
  “ ((ne_pre + (1 * sizeof(UCHAR))) = (base + (no + 1 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (0 <= (no + 1 )) ”
  &&  “ (retval = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 2 ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr2_partial_solve_wit_2 := strstr2_partial_solve_wit_2_pure -> strstr2_partial_solve_wit_2_aux.

Definition strstr2_partial_solve_wit_3_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (hs_pre = (base + ho )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (ho < length) ”
  &&  “ (0 <= ho) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (retval = (Znth (no) (bytes) (0)))) (PreH9 : (0 <= retval)) (PreH10 : (retval < 256)) (PreH11 : (hs_pre = (base + ho ))) (PreH12 : (ne_pre = (base + no ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= ho) ”
  &&  “ (ho < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr2_partial_solve_wit_3_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (retval = (Znth (no) (bytes) (0)))) (PreH9 : (0 <= retval)) (PreH10 : (retval < 256)) (PreH11 : (hs_pre = (base + ho ))) (PreH12 : (ne_pre = (base + no ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= ho) ”
.

Definition strstr2_partial_solve_wit_3_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (retval = (Znth (no) (bytes) (0)))) (PreH9 : (0 <= retval)) (PreH10 : (retval < 256)) (PreH11 : (hs_pre = (base + ho ))) (PreH12 : (ne_pre = (base + no ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (ho < length) ”
.

Definition strstr2_partial_solve_wit_3_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (retval = (Znth (no) (bytes) (0)))) (PreH9 : (0 <= retval)) (PreH10 : (retval < 256)) (PreH11 : (hs_pre = (base + ho ))) (PreH12 : (ne_pre = (base + no ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no 2 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl retval 16)) (32)) retval_2))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr2_partial_solve_wit_3_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 2 )),
  (UCharArray.full base length bytes )
|--
  “ (hs_pre = (base + ho )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (ho < length) ”
  &&  “ (0 <= ho) ”
  &&  “ (retval_2 = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 2 ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr2_partial_solve_wit_3 := strstr2_partial_solve_wit_3_pure -> strstr2_partial_solve_wit_3_aux.

Definition strstr2_partial_solve_wit_4_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ ((hs + (1 * sizeof(UCHAR))) = (base + ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 2 )) (PreH14 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
).

Definition strstr2_partial_solve_wit_4_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 2 )) (PreH14 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr2_partial_solve_wit_4_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 2 )) (PreH14 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
.

Definition strstr2_partial_solve_wit_4_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 2 )) (PreH14 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr2_partial_solve_wit_4_pure_split_goal_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 2 )) (PreH14 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
.

Definition strstr2_partial_solve_wit_4_pure_split_goal_5 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 2 )) (PreH14 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl h2 16)) (32)) c))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr2_partial_solve_wit_4_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 2 )) (PreH8 : (gs_short bytes ho hl no 2 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  “ ((hs + (1 * sizeof(UCHAR))) = (base + ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (c <> 0) ”
  &&  “ (h1 <> h2) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (hs = ((base + ho ) + pos )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 2 ) ”
  &&  “ (gs_short bytes ho hl no 2 pos h1 h2 ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ (c = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 256) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr2_partial_solve_wit_4 := strstr2_partial_solve_wit_4_pure -> strstr2_partial_solve_wit_4_aux.

(*----- Function strstr3 -----*)

Definition strstr3_safety_wit_1 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^8) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^8) )) (32))) ”
  &&  “ (8 <= 31) ”
  &&  “ (0 <= 8) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^8) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^8) )) (32))) ”
  &&  “ (8 <= 31) ”
  &&  “ (0 <= 8) ”
).

Definition strstr3_safety_wit_1_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^8) )) (32)) <= INT_MAX) ”
.

Definition strstr3_safety_wit_1_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^8) )) (32))) ”
.

Definition strstr3_safety_wit_1_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (8 <= 31) ”
.

Definition strstr3_safety_wit_1_split_goal_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= 8) ”
.

Definition strstr3_safety_wit_2 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^16) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^16) )) (32))) ”
  &&  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^16) )) (32)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^16) )) (32))) ”
  &&  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
).

Definition strstr3_safety_wit_2_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((signed_last_nbits ((retval * (2^16) )) (32)) <= INT_MAX) ”
.

Definition strstr3_safety_wit_2_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((INT_MIN) <= (signed_last_nbits ((retval * (2^16) )) (32))) ”
.

Definition strstr3_safety_wit_2_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (16 <= 31) ”
.

Definition strstr3_safety_wit_2_split_goal_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= 16) ”
.

Definition strstr3_safety_wit_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (24 <= 31) ”
  &&  “ (0 <= 24) ”
.

Definition strstr3_safety_wit_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (24 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 24) ”
.

Definition strstr3_safety_wit_5 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strstr3_safety_wit_6 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition strstr3_safety_wit_7 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition strstr3_safety_wit_8 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 < 256)) (PreH4 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (retval = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval)) (PreH9 : (retval < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition strstr3_safety_wit_9 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 < 256)) (PreH4 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (retval = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval)) (PreH9 : (retval < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "h2" ) )) # UInt  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr3_safety_wit_10 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (hs = ((base + ho ) + pos ))) (PreH4 : (0 < base)) (PreH5 : ((base + length ) <= UINT_MAX)) (PreH6 : (gs_inputs bytes length ho hl no 3 )) (PreH7 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH8 : (0 <= pos)) (PreH9 : (pos <= hl)) (PreH10 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH11 : (0 <= c)) (PreH12 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr3_safety_wit_11 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (8 <= 31) ”
  &&  “ (0 <= 8) ”
.

Definition strstr3_safety_wit_12 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition strstr3_safety_wit_13 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ False ”
.

Definition strstr3_safety_wit_14 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )) (PreH9 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ False ”
.

Definition strstr3_safety_wit_15 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition strstr3_safety_wit_16 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )) (PreH9 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "h2" ) )) # UInt  |-> h2)
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr3_entail_wit_1 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (Znth (ho) (bytes) (0)))) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 < 256)) (PreH4 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (retval = (Znth (no) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (hs_pre = (base + ho ))) (PreH14 : (ne_pre = (base + no ))) (PreH15 : (0 < base)) (PreH16 : ((base + length ) <= UINT_MAX)) (PreH17 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
|--
  EX (pos: Z),
  “ (ne_pre = (base + no )) ”
  &&  “ (hs_pre = ((base + ho ) + pos )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 3 ) ”
  &&  “ (gs_short bytes ho hl no 3 pos (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) 0 ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ (retval_4 = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  “ (0 <= retval_4) ”
  &&  “ (retval_4 < 256) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (Znth (ho) (bytes) (0)))) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 < 256)) (PreH4 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 < 256)) (PreH7 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (retval = (Znth (no) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (hs_pre = (base + ho ))) (PreH14 : (ne_pre = (base + no ))) (PreH15 : (0 < base)) (PreH16 : ((base + length ) <= UINT_MAX)) (PreH17 : (gs_inputs bytes length ho hl no 3 )),
  TT && emp 
|--
  EX (pos: Z),
  “ ((base + ho ) = ((base + ho ) + pos )) ”
  &&  “ (gs_short bytes ho hl no 3 pos (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl (Znth (no) (bytes) (0)) 24)) (32)) (unsigned_last_nbits ((Z.shiftl (Znth ((no + 1 )) (bytes) (0)) 16)) (32))) (unsigned_last_nbits ((Z.shiftl (Znth ((no + 2 )) (bytes) (0)) 8)) (32))) 0 ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ ((Znth (ho) (bytes) (0)) = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  emp
).

Definition strstr3_entail_wit_2 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos_2: Z) (hs: Z) (retval: Z) (PreH1 : (retval = (Znth (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (c <> 0)) (PreH5 : (h1 <> h2)) (PreH6 : (ne_pre = (base + no ))) (PreH7 : (hs = ((base + ho ) + pos_2 ))) (PreH8 : (0 < base)) (PreH9 : ((base + length ) <= UINT_MAX)) (PreH10 : (gs_inputs bytes length ho hl no 3 )) (PreH11 : (gs_short bytes ho hl no 3 pos_2 h1 h2 )) (PreH12 : (0 <= pos_2)) (PreH13 : (pos_2 <= hl)) (PreH14 : (c = (Znth ((ho + pos_2 )) (bytes) (0)))) (PreH15 : (0 <= c)) (PreH16 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  EX (pos: Z),
  “ (ne_pre = (base + no )) ”
  &&  “ ((hs + (1 * sizeof(UCHAR))) = ((base + ho ) + pos )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 3 ) ”
  &&  “ (gs_short bytes ho hl no 3 pos h1 (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ (retval = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos_2: Z) (hs: Z) (retval: Z) (PreH1 : (retval = (Znth (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (c <> 0)) (PreH5 : (h1 <> h2)) (PreH6 : (ne_pre = (base + no ))) (PreH7 : (hs = ((base + ho ) + pos_2 ))) (PreH8 : (0 < base)) (PreH9 : ((base + length ) <= UINT_MAX)) (PreH10 : (gs_inputs bytes length ho hl no 3 )) (PreH11 : (gs_short bytes ho hl no 3 pos_2 h1 h2 )) (PreH12 : (0 <= pos_2)) (PreH13 : (pos_2 <= hl)) (PreH14 : (c = (Znth ((ho + pos_2 )) (bytes) (0)))) (PreH15 : (0 <= c)) (PreH16 : (c < 256)),
  TT && emp 
|--
  EX (pos: Z),
  “ ((((base + ho ) + pos_2 ) + (1 * sizeof(UCHAR))) = ((base + ho ) + pos )) ”
  &&  “ (gs_short bytes ho hl no 3 pos h1 (unsigned_last_nbits ((Z.shiftl (Z.lor h2 (Znth ((ho + pos_2 )) (bytes) (0))) 8)) (32)) ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ ((Znth (((((base + ho ) + pos_2 ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) (bytes) (0)) = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  emp
).

Definition strstr3_return_wit_1 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no 3 (hs + ((-3) * sizeof(CHAR))) ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no 3 (((base + ho ) + pos ) + ((-3) * sizeof(CHAR))) ) ”
  &&  emp
).

Definition strstr3_return_wit_1_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 = h2)) (PreH2 : (h1 = h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  (hp_result bytes base ho hl no 3 (((base + ho ) + pos ) + ((-3) * sizeof(CHAR))) )
.

Definition strstr3_return_wit_2 :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )) (PreH9 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no 3 0 ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )) (PreH9 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no 3 0 ) ”
  &&  emp
).

Definition strstr3_return_wit_2_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <> h2)) (PreH2 : (c = 0)) (PreH3 : (h1 <> h2)) (PreH4 : (ne_pre = (base + no ))) (PreH5 : (hs = ((base + ho ) + pos ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )) (PreH9 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH10 : (0 <= pos)) (PreH11 : (pos <= hl)) (PreH12 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH13 : (0 <= c)) (PreH14 : (c < 256)),
  (hp_result bytes base ho hl no 3 0 )
.

Definition strstr3_partial_solve_wit_1_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (ne_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= no) ”
  &&  “ (no < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr3_partial_solve_wit_1_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= no) ”
.

Definition strstr3_partial_solve_wit_1_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (no < length) ”
.

Definition strstr3_partial_solve_wit_1_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr3_partial_solve_wit_1_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (PreH1 : (hs_pre = (base + ho ))) (PreH2 : (ne_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
|--
  “ (ne_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
  &&  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 3 ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr3_partial_solve_wit_1 := strstr3_partial_solve_wit_1_pure -> strstr3_partial_solve_wit_1_aux.

Definition strstr3_partial_solve_wit_2_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((ne_pre + (1 * sizeof(UCHAR))) = (base + (no + 1 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (0 <= (no + 1 )) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= (no + 1 )) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr3_partial_solve_wit_2_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= (no + 1 )) ”
.

Definition strstr3_partial_solve_wit_2_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((no + 1 ) < length) ”
.

Definition strstr3_partial_solve_wit_2_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr3_partial_solve_wit_2_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (hs_pre = (base + ho ))) (PreH5 : (ne_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
|--
  “ ((ne_pre + (1 * sizeof(UCHAR))) = (base + (no + 1 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (0 <= (no + 1 )) ”
  &&  “ (retval = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 3 ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr3_partial_solve_wit_2 := strstr3_partial_solve_wit_2_pure -> strstr3_partial_solve_wit_2_aux.

Definition strstr3_partial_solve_wit_3_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((ne_pre + (2 * sizeof(UCHAR))) = (base + (no + 2 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 2 ) < length) ”
  &&  “ (0 <= (no + 2 )) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= (no + 2 )) ”
  &&  “ ((no + 2 ) < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr3_partial_solve_wit_3_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= (no + 2 )) ”
.

Definition strstr3_partial_solve_wit_3_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ ((no + 2 ) < length) ”
.

Definition strstr3_partial_solve_wit_3_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |->_)
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr3_partial_solve_wit_3_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (Znth (no) (bytes) (0)))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (hs_pre = (base + ho ))) (PreH8 : (ne_pre = (base + no ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
|--
  “ ((ne_pre + (2 * sizeof(UCHAR))) = (base + (no + 2 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 2 ) < length) ”
  &&  “ (0 <= (no + 2 )) ”
  &&  “ (retval_2 = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 3 ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr3_partial_solve_wit_3 := strstr3_partial_solve_wit_3_pure -> strstr3_partial_solve_wit_3_aux.

Definition strstr3_partial_solve_wit_4_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 < 256)) (PreH4 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (retval = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval)) (PreH9 : (retval < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (hs_pre = (base + ho )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (ho < length) ”
  &&  “ (0 <= ho) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < 256)) (PreH11 : (retval = (Znth (no) (bytes) (0)))) (PreH12 : (0 <= retval)) (PreH13 : (retval < 256)) (PreH14 : (hs_pre = (base + ho ))) (PreH15 : (ne_pre = (base + no ))) (PreH16 : (0 < base)) (PreH17 : ((base + length ) <= UINT_MAX)) (PreH18 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= ho) ”
  &&  “ (ho < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr3_partial_solve_wit_4_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < 256)) (PreH11 : (retval = (Znth (no) (bytes) (0)))) (PreH12 : (0 <= retval)) (PreH13 : (retval < 256)) (PreH14 : (hs_pre = (base + ho ))) (PreH15 : (ne_pre = (base + no ))) (PreH16 : (0 < base)) (PreH17 : ((base + length ) <= UINT_MAX)) (PreH18 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (0 <= ho) ”
.

Definition strstr3_partial_solve_wit_4_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < 256)) (PreH11 : (retval = (Znth (no) (bytes) (0)))) (PreH12 : (0 <= retval)) (PreH13 : (retval < 256)) (PreH14 : (hs_pre = (base + ho ))) (PreH15 : (ne_pre = (base + no ))) (PreH16 : (0 < base)) (PreH17 : ((base + length ) <= UINT_MAX)) (PreH18 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (ho < length) ”
.

Definition strstr3_partial_solve_wit_4_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : ((Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))) >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < 256)) (PreH11 : (retval = (Znth (no) (bytes) (0)))) (PreH12 : (0 <= retval)) (PreH13 : (retval < 256)) (PreH14 : (hs_pre = (base + ho ))) (PreH15 : (ne_pre = (base + no ))) (PreH16 : (0 < base)) (PreH17 : ((base + length ) <= UINT_MAX)) (PreH18 : (gs_inputs bytes length ho hl no 3 )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "h2" ) )) # UInt  |-> 0)
  **  (UCharArray.full base length bytes )
  **  ((( &( "h1" ) )) # UInt  |-> (Z.lor (Z.lor (unsigned_last_nbits ((Z.shiftl retval 24)) (32)) (unsigned_last_nbits ((Z.shiftl retval_2 16)) (32))) (unsigned_last_nbits ((Z.shiftl retval_3 8)) (32))))
  **  ((( &( "hs" ) )) # Ptr  |-> hs_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr3_partial_solve_wit_4_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (hs_pre: Z) (ne_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 < 256)) (PreH4 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 < 256)) (PreH7 : (retval = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval)) (PreH9 : (retval < 256)) (PreH10 : (hs_pre = (base + ho ))) (PreH11 : (ne_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no 3 )),
  (UCharArray.full base length bytes )
|--
  “ (hs_pre = (base + ho )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (ho < length) ”
  &&  “ (0 <= ho) ”
  &&  “ (retval_3 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  “ (retval_2 = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (hs_pre = (base + ho )) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 3 ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr3_partial_solve_wit_4 := strstr3_partial_solve_wit_4_pure -> strstr3_partial_solve_wit_4_aux.

Definition strstr3_partial_solve_wit_5_pure :=
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ ((hs + (1 * sizeof(UCHAR))) = (base + ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
) \/
(
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 3 )) (PreH14 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
).

Definition strstr3_partial_solve_wit_5_pure_split_goal_1 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 3 )) (PreH14 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr3_partial_solve_wit_5_pure_split_goal_2 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 3 )) (PreH14 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
.

Definition strstr3_partial_solve_wit_5_pure_split_goal_3 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 3 )) (PreH14 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr3_partial_solve_wit_5_pure_split_goal_4 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 3 )) (PreH14 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
.

Definition strstr3_partial_solve_wit_5_pure_split_goal_5 :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (h1 <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) <= UINT_MAX)) (PreH3 : (h1 >= 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)) >= 0)) (PreH5 : (c <= INT_MAX)) (PreH6 : (c >= INT_MIN)) (PreH7 : (c <> 0)) (PreH8 : (h1 <> h2)) (PreH9 : (ne_pre = (base + no ))) (PreH10 : (hs = ((base + ho ) + pos ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no 3 )) (PreH14 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH15 : (0 <= pos)) (PreH16 : (pos <= hl)) (PreH17 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH18 : (0 <= c)) (PreH19 : (c < 256)),
  ((( &( "ne" ) )) # Ptr  |-> ne_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> (hs + (1 * sizeof(UCHAR))))
  **  ((( &( "h2" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Z.lor h2 c) 8)) (32)))
  **  ((( &( "h1" ) )) # UInt  |-> h1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr3_partial_solve_wit_5_aux :=
forall (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (ne_pre: Z) (c: Z) (h1: Z) (h2: Z) (pos: Z) (hs: Z) (PreH1 : (c <> 0)) (PreH2 : (h1 <> h2)) (PreH3 : (ne_pre = (base + no ))) (PreH4 : (hs = ((base + ho ) + pos ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no 3 )) (PreH8 : (gs_short bytes ho hl no 3 pos h1 h2 )) (PreH9 : (0 <= pos)) (PreH10 : (pos <= hl)) (PreH11 : (c = (Znth ((ho + pos )) (bytes) (0)))) (PreH12 : (0 <= c)) (PreH13 : (c < 256)),
  (UCharArray.full base length bytes )
|--
  “ ((hs + (1 * sizeof(UCHAR))) = (base + ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= ((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (((hs + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR))) < length) ”
  &&  “ (0 <= ((((base + ho ) + pos ) + (1 * sizeof(UCHAR))) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (c <> 0) ”
  &&  “ (h1 <> h2) ”
  &&  “ (ne_pre = (base + no )) ”
  &&  “ (hs = ((base + ho ) + pos )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no 3 ) ”
  &&  “ (gs_short bytes ho hl no 3 pos h1 h2 ) ”
  &&  “ (0 <= pos) ”
  &&  “ (pos <= hl) ”
  &&  “ (c = (Znth ((ho + pos )) (bytes) (0))) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 256) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr3_partial_solve_wit_5 := strstr3_partial_solve_wit_5_pure -> strstr3_partial_solve_wit_5_aux.

(*----- Function strstr -----*)

Definition strstr_safety_wit_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (haystack_pre = (base + ho ))) (PreH5 : (needle_pre = (base + no ))) (PreH6 : (0 < base)) (PreH7 : ((base + length ) <= UINT_MAX)) (PreH8 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr_safety_wit_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (gs_strchr bytes base ho hl retval_2 retval_3 )) (PreH2 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth (no) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack_pre = (base + ho ))) (PreH10 : (needle_pre = (base + no ))) (PreH11 : (0 < base)) (PreH12 : ((base + length ) <= UINT_MAX)) (PreH13 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> retval_3)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr_safety_wit_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (PreH1 : (haystack = (base + ho ))) (PreH2 : (needle = (base + no ))) (PreH3 : (ne = needle)) (PreH4 : (hs = ((base + ho ) + start ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl )) (PreH8 : (0 < nl)) (PreH9 : (0 <= start)) (PreH10 : (start < hl)) (PreH11 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH12 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base length bytes )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strstr_safety_wit_4 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (haystack = (base + ho ))) (PreH5 : (needle = (base + no ))) (PreH6 : (ne = needle)) (PreH7 : (hs = ((base + ho ) + start ))) (PreH8 : (0 < base)) (PreH9 : ((base + length ) <= UINT_MAX)) (PreH10 : (gs_inputs bytes length ho hl no nl )) (PreH11 : (0 < nl)) (PreH12 : (0 <= start)) (PreH13 : (start < hl)) (PreH14 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH15 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr_safety_wit_5 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition strstr_safety_wit_6 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH6 : (0 <= retval)) (PreH7 : (retval < 256)) (PreH8 : (haystack = (base + ho ))) (PreH9 : (needle = (base + no ))) (PreH10 : (ne = needle)) (PreH11 : (hs = ((base + ho ) + start ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no nl )) (PreH15 : (0 < nl)) (PreH16 : (0 <= start)) (PreH17 : (start < hl)) (PreH18 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH19 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr_safety_wit_7 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition strstr_safety_wit_8 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (retval <> 0)) (PreH9 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH10 : (0 <= retval)) (PreH11 : (retval < 256)) (PreH12 : (haystack = (base + ho ))) (PreH13 : (needle = (base + no ))) (PreH14 : (ne = needle)) (PreH15 : (hs = ((base + ho ) + start ))) (PreH16 : (0 < base)) (PreH17 : ((base + length ) <= UINT_MAX)) (PreH18 : (gs_inputs bytes length ho hl no nl )) (PreH19 : (0 < nl)) (PreH20 : (0 <= start)) (PreH21 : (start < hl)) (PreH22 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH23 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr_safety_wit_9 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = nl)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH12 : (0 <= retval)) (PreH13 : (retval < 256)) (PreH14 : (haystack = (base + ho ))) (PreH15 : (needle = (base + no ))) (PreH16 : (ne = needle)) (PreH17 : (hs = ((base + ho ) + start ))) (PreH18 : (0 < base)) (PreH19 : ((base + length ) <= UINT_MAX)) (PreH20 : (gs_inputs bytes length ho hl no nl )) (PreH21 : (0 < nl)) (PreH22 : (0 <= start)) (PreH23 : (start < hl)) (PreH24 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH25 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (512 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 512) ”
.

Definition strstr_safety_wit_10 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 < retval_4)) (PreH2 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr_safety_wit_11 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_4 retval_6 )) (PreH2 : (retval_5 >= retval_4)) (PreH3 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH4 : (retval_4 = nl)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 < 256)) (PreH9 : (retval_2 <> 0)) (PreH10 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 < 256)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH15 : (0 <= retval)) (PreH16 : (retval < 256)) (PreH17 : (haystack = (base + ho ))) (PreH18 : (needle = (base + no ))) (PreH19 : (ne = needle)) (PreH20 : (hs = ((base + ho ) + start ))) (PreH21 : (0 < base)) (PreH22 : ((base + length ) <= UINT_MAX)) (PreH23 : (gs_inputs bytes length ho hl no nl )) (PreH24 : (0 < nl)) (PreH25 : (0 <= start)) (PreH26 : (start < hl)) (PreH27 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH28 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strstr_safety_wit_12 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_4 retval_6 )) (PreH3 : (retval_5 >= retval_4)) (PreH4 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH5 : (retval_4 = nl)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 < 256)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 < 256)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH16 : (0 <= retval)) (PreH17 : (retval < 256)) (PreH18 : (haystack = (base + ho ))) (PreH19 : (needle = (base + no ))) (PreH20 : (ne = needle)) (PreH21 : (hs = ((base + ho ) + start ))) (PreH22 : (0 < base)) (PreH23 : ((base + length ) <= UINT_MAX)) (PreH24 : (gs_inputs bytes length ho hl no nl )) (PreH25 : (0 < nl)) (PreH26 : (0 <= start)) (PreH27 : (start < hl)) (PreH28 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH29 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (256 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 256) ”
.

Definition strstr_entail_wit_1 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (gs_strchr bytes base ho hl retval_3 retval )) (PreH3 : (retval_3 = (Znth (no) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack_pre = (base + ho ))) (PreH11 : (needle_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
|--
  EX (start: Z),
  “ (haystack_pre = (base + ho )) ”
  &&  “ (needle_pre = (base + no )) ”
  &&  “ (needle_pre = needle_pre) ”
  &&  “ (retval = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (gs_strchr bytes base ho hl retval_3 retval )) (PreH3 : (retval_3 = (Znth (no) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack_pre = (base + ho ))) (PreH11 : (needle_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no nl )),
  TT && emp 
|--
  EX (start: Z),
  “ (retval = ((base + ho ) + start )) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  emp
).

Definition strstr_return_wit_1 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no retval_5 retval )) (PreH2 : (retval_5 <= 256)) (PreH3 : (retval_7 <> 0)) (PreH4 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_5 retval_7 )) (PreH5 : (retval_6 >= retval_5)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_5 512) retval_6 )) (PreH7 : (retval_5 = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no retval_5 retval )) (PreH2 : (retval_5 <= 256)) (PreH3 : (retval_7 <> 0)) (PreH4 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_5 retval_7 )) (PreH5 : (retval_6 >= retval_5)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_5 512) retval_6 )) (PreH7 : (retval_5 = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  emp
).

Definition strstr_return_wit_1_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no retval_5 retval )) (PreH2 : (retval_5 <= 256)) (PreH3 : (retval_7 <> 0)) (PreH4 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_5 retval_7 )) (PreH5 : (retval_6 >= retval_5)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_5 512) retval_6 )) (PreH7 : (retval_5 = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (hp_result bytes base ho hl no nl retval )
.

Definition strstr_return_wit_2 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (retval_5) (32)) retval )) (PreH2 : (retval_5 > 256)) (PreH3 : (retval_7 <> 0)) (PreH4 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_5 retval_7 )) (PreH5 : (retval_6 >= retval_5)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_5 512) retval_6 )) (PreH7 : (retval_5 = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (retval_5) (32)) retval )) (PreH2 : (retval_5 > 256)) (PreH3 : (retval_7 <> 0)) (PreH4 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_5 retval_7 )) (PreH5 : (retval_6 >= retval_5)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_5 512) retval_6 )) (PreH7 : (retval_5 = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  emp
).

Definition strstr_return_wit_2_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (retval_5) (32)) retval )) (PreH2 : (retval_5 > 256)) (PreH3 : (retval_7 <> 0)) (PreH4 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_5 retval_7 )) (PreH5 : (retval_6 >= retval_5)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_5 512) retval_6 )) (PreH7 : (retval_5 = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (hp_result bytes base ho hl no nl retval )
.

Definition strstr_return_wit_3 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_4 retval_6 )) (PreH3 : (retval_5 >= retval_4)) (PreH4 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH5 : (retval_4 = nl)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 < 256)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 < 256)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH16 : (0 <= retval)) (PreH17 : (retval < 256)) (PreH18 : (haystack = (base + ho ))) (PreH19 : (needle = (base + no ))) (PreH20 : (ne = needle)) (PreH21 : (hs = ((base + ho ) + start ))) (PreH22 : (0 < base)) (PreH23 : ((base + length ) <= UINT_MAX)) (PreH24 : (gs_inputs bytes length ho hl no nl )) (PreH25 : (0 < nl)) (PreH26 : (0 <= start)) (PreH27 : (start < hl)) (PreH28 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH29 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl hs ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_4 retval_6 )) (PreH3 : (retval_5 >= retval_4)) (PreH4 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH5 : (retval_4 = nl)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 < 256)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 < 256)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH16 : (0 <= retval)) (PreH17 : (retval < 256)) (PreH18 : (haystack = (base + ho ))) (PreH19 : (needle = (base + no ))) (PreH20 : (ne = needle)) (PreH21 : (hs = ((base + ho ) + start ))) (PreH22 : (0 < base)) (PreH23 : ((base + length ) <= UINT_MAX)) (PreH24 : (gs_inputs bytes length ho hl no nl )) (PreH25 : (0 < nl)) (PreH26 : (0 <= start)) (PreH27 : (start < hl)) (PreH28 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH29 : (hp_no_match_before bytes ho hl no nl start )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl ((base + ho ) + start ) ) ”
  &&  emp
).

Definition strstr_return_wit_3_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval_4 retval_6 )) (PreH3 : (retval_5 >= retval_4)) (PreH4 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH5 : (retval_4 = nl)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 < 256)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 < 256)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH16 : (0 <= retval)) (PreH17 : (retval < 256)) (PreH18 : (haystack = (base + ho ))) (PreH19 : (needle = (base + no ))) (PreH20 : (ne = needle)) (PreH21 : (hs = ((base + ho ) + start ))) (PreH22 : (0 < base)) (PreH23 : ((base + length ) <= UINT_MAX)) (PreH24 : (gs_inputs bytes length ho hl no nl )) (PreH25 : (0 < nl)) (PreH26 : (0 <= start)) (PreH27 : (start < hl)) (PreH28 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH29 : (hp_no_match_before bytes ho hl no nl start )),
  (hp_result bytes base ho hl no nl ((base + ho ) + start ) )
.

Definition strstr_return_wit_4 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 < retval_4)) (PreH2 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl 0 ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 < retval_4)) (PreH2 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl 0 ) ”
  &&  emp
).

Definition strstr_return_wit_4_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 < retval_4)) (PreH2 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval_4 512) retval_5 )) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  (hp_result bytes base ho hl no nl 0 )
.

Definition strstr_return_wit_5 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 3 retval )) (PreH2 : (retval_4 = 0)) (PreH3 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 < 256)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 < 256)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 < 256)) (PreH14 : (haystack = (base + ho ))) (PreH15 : (needle = (base + no ))) (PreH16 : (ne = needle)) (PreH17 : (hs = ((base + ho ) + start ))) (PreH18 : (0 < base)) (PreH19 : ((base + length ) <= UINT_MAX)) (PreH20 : (gs_inputs bytes length ho hl no nl )) (PreH21 : (0 < nl)) (PreH22 : (0 <= start)) (PreH23 : (start < hl)) (PreH24 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH25 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 3 retval )) (PreH2 : (retval_4 = 0)) (PreH3 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 < 256)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 < 256)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 < 256)) (PreH14 : (haystack = (base + ho ))) (PreH15 : (needle = (base + no ))) (PreH16 : (ne = needle)) (PreH17 : (hs = ((base + ho ) + start ))) (PreH18 : (0 < base)) (PreH19 : ((base + length ) <= UINT_MAX)) (PreH20 : (gs_inputs bytes length ho hl no nl )) (PreH21 : (0 < nl)) (PreH22 : (0 <= start)) (PreH23 : (start < hl)) (PreH24 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH25 : (hp_no_match_before bytes ho hl no nl start )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  emp
).

Definition strstr_return_wit_5_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 3 retval )) (PreH2 : (retval_4 = 0)) (PreH3 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 < 256)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 < 256)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 < 256)) (PreH14 : (haystack = (base + ho ))) (PreH15 : (needle = (base + no ))) (PreH16 : (ne = needle)) (PreH17 : (hs = ((base + ho ) + start ))) (PreH18 : (0 < base)) (PreH19 : ((base + length ) <= UINT_MAX)) (PreH20 : (gs_inputs bytes length ho hl no nl )) (PreH21 : (0 < nl)) (PreH22 : (0 <= start)) (PreH23 : (start < hl)) (PreH24 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH25 : (hp_no_match_before bytes ho hl no nl start )),
  (hp_result bytes base ho hl no nl retval )
.

Definition strstr_return_wit_6 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 2 retval )) (PreH2 : (retval_3 = 0)) (PreH3 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack = (base + ho ))) (PreH11 : (needle = (base + no ))) (PreH12 : (ne = needle)) (PreH13 : (hs = ((base + ho ) + start ))) (PreH14 : (0 < base)) (PreH15 : ((base + length ) <= UINT_MAX)) (PreH16 : (gs_inputs bytes length ho hl no nl )) (PreH17 : (0 < nl)) (PreH18 : (0 <= start)) (PreH19 : (start < hl)) (PreH20 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH21 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 2 retval )) (PreH2 : (retval_3 = 0)) (PreH3 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack = (base + ho ))) (PreH11 : (needle = (base + no ))) (PreH12 : (ne = needle)) (PreH13 : (hs = ((base + ho ) + start ))) (PreH14 : (0 < base)) (PreH15 : ((base + length ) <= UINT_MAX)) (PreH16 : (gs_inputs bytes length ho hl no nl )) (PreH17 : (0 < nl)) (PreH18 : (0 <= start)) (PreH19 : (start < hl)) (PreH20 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH21 : (hp_no_match_before bytes ho hl no nl start )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  emp
).

Definition strstr_return_wit_6_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (hp_result bytes base (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 2 retval )) (PreH2 : (retval_3 = 0)) (PreH3 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack = (base + ho ))) (PreH11 : (needle = (base + no ))) (PreH12 : (ne = needle)) (PreH13 : (hs = ((base + ho ) + start ))) (PreH14 : (0 < base)) (PreH15 : ((base + length ) <= UINT_MAX)) (PreH16 : (gs_inputs bytes length ho hl no nl )) (PreH17 : (0 < nl)) (PreH18 : (0 <= start)) (PreH19 : (start < hl)) (PreH20 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH21 : (hp_no_match_before bytes ho hl no nl start )),
  (hp_result bytes base ho hl no nl retval )
.

Definition strstr_return_wit_7 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl hs ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl ((base + ho ) + start ) ) ”
  &&  emp
).

Definition strstr_return_wit_7_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (hp_result bytes base ho hl no nl ((base + ho ) + start ) )
.

Definition strstr_return_wit_8 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (gs_strchr bytes base ho hl retval_3 retval )) (PreH3 : (retval_3 = (Znth (no) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack_pre = (base + ho ))) (PreH11 : (needle_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl retval ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (gs_strchr bytes base ho hl retval_3 retval )) (PreH3 : (retval_3 = (Znth (no) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack_pre = (base + ho ))) (PreH11 : (needle_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no nl )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl 0 ) ”
  &&  emp
).

Definition strstr_return_wit_8_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (gs_strchr bytes base ho hl retval_3 retval )) (PreH3 : (retval_3 = (Znth (no) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (haystack_pre = (base + ho ))) (PreH11 : (needle_pre = (base + no ))) (PreH12 : (0 < base)) (PreH13 : ((base + length ) <= UINT_MAX)) (PreH14 : (gs_inputs bytes length ho hl no nl )),
  (hp_result bytes base ho hl no nl 0 )
.

Definition strstr_return_wit_9 :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
|--
  “ (hp_result bytes base ho hl no nl haystack_pre ) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  TT && emp 
|--
  “ (hp_result bytes base ho hl no nl (base + ho ) ) ”
  &&  emp
).

Definition strstr_return_wit_9_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (hp_result bytes base ho hl no nl (base + ho ) )
.

Definition strstr_partial_solve_wit_1_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (PreH1 : (haystack_pre = (base + ho ))) (PreH2 : (needle_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl )),
  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (needle_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (PreH1 : (haystack_pre = (base + ho ))) (PreH2 : (needle_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl )),
  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= no) ”
  &&  “ (no < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr_partial_solve_wit_1_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (PreH1 : (haystack_pre = (base + ho ))) (PreH2 : (needle_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl )),
  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= no) ”
.

Definition strstr_partial_solve_wit_1_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (PreH1 : (haystack_pre = (base + ho ))) (PreH2 : (needle_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl )),
  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (no < length) ”
.

Definition strstr_partial_solve_wit_1_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (PreH1 : (haystack_pre = (base + ho ))) (PreH2 : (needle_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl )),
  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full base length bytes )
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr_partial_solve_wit_1_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (PreH1 : (haystack_pre = (base + ho ))) (PreH2 : (needle_pre = (base + no ))) (PreH3 : (0 < base)) (PreH4 : ((base + length ) <= UINT_MAX)) (PreH5 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
|--
  “ (needle_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
  &&  “ (haystack_pre = (base + ho )) ”
  &&  “ (needle_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_1 := strstr_partial_solve_wit_1_pure -> strstr_partial_solve_wit_1_aux.

Definition strstr_partial_solve_wit_2_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (needle_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (0 <= no) ”
  &&  “ (no < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr_partial_solve_wit_2_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (0 <= no) ”
.

Definition strstr_partial_solve_wit_2_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (no < length) ”
.

Definition strstr_partial_solve_wit_2_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr_partial_solve_wit_2_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth (no) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack_pre = (base + ho ))) (PreH6 : (needle_pre = (base + no ))) (PreH7 : (0 < base)) (PreH8 : ((base + length ) <= UINT_MAX)) (PreH9 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
|--
  “ (needle_pre = (base + no )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ (no < length) ”
  &&  “ (0 <= no) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (haystack_pre = (base + ho )) ”
  &&  “ (needle_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_2 := strstr_partial_solve_wit_2_pure -> strstr_partial_solve_wit_2_aux.

Definition strstr_partial_solve_wit_3_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (haystack_pre = (base + ho ))) (PreH9 : (needle_pre = (base + no ))) (PreH10 : (0 < base)) (PreH11 : ((base + length ) <= UINT_MAX)) (PreH12 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (haystack_pre = (base + ho )) ”
  &&  “ (0 < retval) ”
  &&  “ (retval < 256) ”
  &&  “ (hp_cstring bytes ho hl ) ”
  &&  “ ((ho + hl ) < length) ”
  &&  “ (0 <= hl) ”
  &&  “ (0 <= ho) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (haystack_pre = (base + ho ))) (PreH9 : (needle_pre = (base + no ))) (PreH10 : (0 < base)) (PreH11 : ((base + length ) <= UINT_MAX)) (PreH12 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (0 <= ho) ”
  &&  “ (0 <= hl) ”
  &&  “ ((ho + hl ) < length) ”
  &&  “ (hp_cstring bytes ho hl ) ”
).

Definition strstr_partial_solve_wit_3_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (haystack_pre = (base + ho ))) (PreH9 : (needle_pre = (base + no ))) (PreH10 : (0 < base)) (PreH11 : ((base + length ) <= UINT_MAX)) (PreH12 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (0 <= ho) ”
.

Definition strstr_partial_solve_wit_3_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (haystack_pre = (base + ho ))) (PreH9 : (needle_pre = (base + no ))) (PreH10 : (0 < base)) (PreH11 : ((base + length ) <= UINT_MAX)) (PreH12 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (0 <= hl) ”
.

Definition strstr_partial_solve_wit_3_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (haystack_pre = (base + ho ))) (PreH9 : (needle_pre = (base + no ))) (PreH10 : (0 < base)) (PreH11 : ((base + length ) <= UINT_MAX)) (PreH12 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ ((ho + hl ) < length) ”
.

Definition strstr_partial_solve_wit_3_pure_split_goal_4 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (haystack_pre = (base + ho ))) (PreH9 : (needle_pre = (base + no ))) (PreH10 : (0 < base)) (PreH11 : ((base + length ) <= UINT_MAX)) (PreH12 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
|--
  “ (hp_cstring bytes ho hl ) ”
.

Definition strstr_partial_solve_wit_3_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (haystack_pre: Z) (needle_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Znth (no) (bytes) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (Znth (no) (bytes) (0)))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 < 256)) (PreH8 : (haystack_pre = (base + ho ))) (PreH9 : (needle_pre = (base + no ))) (PreH10 : (0 < base)) (PreH11 : ((base + length ) <= UINT_MAX)) (PreH12 : (gs_inputs bytes length ho hl no nl )),
  (UCharArray.full base length bytes )
|--
  “ (haystack_pre = (base + ho )) ”
  &&  “ (0 < retval) ”
  &&  “ (retval < 256) ”
  &&  “ (hp_cstring bytes ho hl ) ”
  &&  “ ((ho + hl ) < length) ”
  &&  “ (0 <= hl) ”
  &&  “ (0 <= ho) ”
  &&  “ (retval = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval_2 = (Znth (no) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (haystack_pre = (base + ho )) ”
  &&  “ (needle_pre = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_3 := strstr_partial_solve_wit_3_pure -> strstr_partial_solve_wit_3_aux.

Definition strstr_partial_solve_wit_4_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (PreH1 : (haystack = (base + ho ))) (PreH2 : (needle = (base + no ))) (PreH3 : (ne = needle)) (PreH4 : (hs = ((base + ho ) + start ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl )) (PreH8 : (0 < nl)) (PreH9 : (0 <= start)) (PreH10 : (start < hl)) (PreH11 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH12 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base length bytes )
|--
  “ ((ne + (1 * sizeof(UCHAR))) = (base + (no + 1 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (0 <= (no + 1 )) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (PreH1 : (haystack = (base + ho ))) (PreH2 : (needle = (base + no ))) (PreH3 : (ne = needle)) (PreH4 : (hs = ((base + ho ) + start ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl )) (PreH8 : (0 < nl)) (PreH9 : (0 <= start)) (PreH10 : (start < hl)) (PreH11 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH12 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= (no + 1 )) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr_partial_solve_wit_4_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (PreH1 : (haystack = (base + ho ))) (PreH2 : (needle = (base + no ))) (PreH3 : (ne = needle)) (PreH4 : (hs = ((base + ho ) + start ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl )) (PreH8 : (0 < nl)) (PreH9 : (0 <= start)) (PreH10 : (start < hl)) (PreH11 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH12 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base length bytes )
|--
  “ (0 <= (no + 1 )) ”
.

Definition strstr_partial_solve_wit_4_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (PreH1 : (haystack = (base + ho ))) (PreH2 : (needle = (base + no ))) (PreH3 : (ne = needle)) (PreH4 : (hs = ((base + ho ) + start ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl )) (PreH8 : (0 < nl)) (PreH9 : (0 <= start)) (PreH10 : (start < hl)) (PreH11 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH12 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base length bytes )
|--
  “ ((no + 1 ) < length) ”
.

Definition strstr_partial_solve_wit_4_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (PreH1 : (haystack = (base + ho ))) (PreH2 : (needle = (base + no ))) (PreH3 : (ne = needle)) (PreH4 : (hs = ((base + ho ) + start ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl )) (PreH8 : (0 < nl)) (PreH9 : (0 <= start)) (PreH10 : (start < hl)) (PreH11 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH12 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base length bytes )
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr_partial_solve_wit_4_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (PreH1 : (haystack = (base + ho ))) (PreH2 : (needle = (base + no ))) (PreH3 : (ne = needle)) (PreH4 : (hs = ((base + ho ) + start ))) (PreH5 : (0 < base)) (PreH6 : ((base + length ) <= UINT_MAX)) (PreH7 : (gs_inputs bytes length ho hl no nl )) (PreH8 : (0 < nl)) (PreH9 : (0 <= start)) (PreH10 : (start < hl)) (PreH11 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH12 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ ((ne + (1 * sizeof(UCHAR))) = (base + (no + 1 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 1 ) < length) ”
  &&  “ (0 <= (no + 1 )) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_4 := strstr_partial_solve_wit_4_pure -> strstr_partial_solve_wit_4_aux.

Definition strstr_partial_solve_wit_5_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((ne + (2 * sizeof(UCHAR))) = (base + (no + 2 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 2 ) < length) ”
  &&  “ (0 <= (no + 2 )) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (no + 2 )) ”
  &&  “ ((no + 2 ) < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr_partial_solve_wit_5_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (no + 2 )) ”
.

Definition strstr_partial_solve_wit_5_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((no + 2 ) < length) ”
.

Definition strstr_partial_solve_wit_5_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr_partial_solve_wit_5_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH3 : (0 <= retval)) (PreH4 : (retval < 256)) (PreH5 : (haystack = (base + ho ))) (PreH6 : (needle = (base + no ))) (PreH7 : (ne = needle)) (PreH8 : (hs = ((base + ho ) + start ))) (PreH9 : (0 < base)) (PreH10 : ((base + length ) <= UINT_MAX)) (PreH11 : (gs_inputs bytes length ho hl no nl )) (PreH12 : (0 < nl)) (PreH13 : (0 <= start)) (PreH14 : (start < hl)) (PreH15 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH16 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ ((ne + (2 * sizeof(UCHAR))) = (base + (no + 2 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 2 ) < length) ”
  &&  “ (0 <= (no + 2 )) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_5 := strstr_partial_solve_wit_5_pure -> strstr_partial_solve_wit_5_aux.

Definition strstr_partial_solve_wit_6_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
).

Definition strstr_partial_solve_wit_6_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
.

Definition strstr_partial_solve_wit_6_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
.

Definition strstr_partial_solve_wit_6_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 2 ) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (retval_2 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_6 := strstr_partial_solve_wit_6_pure -> strstr_partial_solve_wit_6_aux.

Definition strstr_partial_solve_wit_7_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((ne + (3 * sizeof(UCHAR))) = (base + (no + 3 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 3 ) < length) ”
  &&  “ (0 <= (no + 3 )) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (no + 3 )) ”
  &&  “ ((no + 3 ) < length) ”
  &&  “ (gs_bytes bytes ) ”
).

Definition strstr_partial_solve_wit_7_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (no + 3 )) ”
.

Definition strstr_partial_solve_wit_7_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((no + 3 ) < length) ”
.

Definition strstr_partial_solve_wit_7_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_bytes bytes ) ”
.

Definition strstr_partial_solve_wit_7_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < 256)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH7 : (0 <= retval)) (PreH8 : (retval < 256)) (PreH9 : (haystack = (base + ho ))) (PreH10 : (needle = (base + no ))) (PreH11 : (ne = needle)) (PreH12 : (hs = ((base + ho ) + start ))) (PreH13 : (0 < base)) (PreH14 : ((base + length ) <= UINT_MAX)) (PreH15 : (gs_inputs bytes length ho hl no nl )) (PreH16 : (0 < nl)) (PreH17 : (0 <= start)) (PreH18 : (start < hl)) (PreH19 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH20 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ ((ne + (3 * sizeof(UCHAR))) = (base + (no + 3 ) )) ”
  &&  “ (gs_bytes bytes ) ”
  &&  “ ((no + 3 ) < length) ”
  &&  “ (0 <= (no + 3 )) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval_2 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_7 := strstr_partial_solve_wit_7_pure -> strstr_partial_solve_wit_7_aux.

Definition strstr_partial_solve_wit_8_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
).

Definition strstr_partial_solve_wit_8_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
.

Definition strstr_partial_solve_wit_8_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
.

Definition strstr_partial_solve_wit_8_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no 3 ) ”
  &&  “ (retval_3 = 0) ”
  &&  “ (retval_3 = (Znth ((no + 3 )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval_2 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_8 := strstr_partial_solve_wit_8_pure -> strstr_partial_solve_wit_8_aux.

Definition strstr_partial_solve_wit_9_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "ne_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (ne = (base + no )) ”
  &&  “ (0 <= nl) ”
  &&  “ (hp_cstring bytes no nl ) ”
  &&  “ ((no + nl ) < length) ”
  &&  “ (0 <= no) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "ne_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= no) ”
  &&  “ ((no + nl ) < length) ”
  &&  “ (hp_cstring bytes no nl ) ”
).

Definition strstr_partial_solve_wit_9_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "ne_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= no) ”
.

Definition strstr_partial_solve_wit_9_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "ne_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((no + nl ) < length) ”
.

Definition strstr_partial_solve_wit_9_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "ne_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hp_cstring bytes no nl ) ”
.

Definition strstr_partial_solve_wit_9_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < 256)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 < 256)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH11 : (0 <= retval)) (PreH12 : (retval < 256)) (PreH13 : (haystack = (base + ho ))) (PreH14 : (needle = (base + no ))) (PreH15 : (ne = needle)) (PreH16 : (hs = ((base + ho ) + start ))) (PreH17 : (0 < base)) (PreH18 : ((base + length ) <= UINT_MAX)) (PreH19 : (gs_inputs bytes length ho hl no nl )) (PreH20 : (0 < nl)) (PreH21 : (0 <= start)) (PreH22 : (start < hl)) (PreH23 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH24 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (ne = (base + no )) ”
  &&  “ (0 <= nl) ”
  &&  “ (hp_cstring bytes no nl ) ”
  &&  “ ((no + nl ) < length) ”
  &&  “ (0 <= no) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_3 = (Znth ((no + 3 )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval_2 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_9 := strstr_partial_solve_wit_9_pure -> strstr_partial_solve_wit_9_aux.

Definition strstr_partial_solve_wit_10_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = nl)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH12 : (0 <= retval)) (PreH13 : (retval < 256)) (PreH14 : (haystack = (base + ho ))) (PreH15 : (needle = (base + no ))) (PreH16 : (ne = needle)) (PreH17 : (hs = ((base + ho ) + start ))) (PreH18 : (0 < base)) (PreH19 : ((base + length ) <= UINT_MAX)) (PreH20 : (gs_inputs bytes length ho hl no nl )) (PreH21 : (0 < nl)) (PreH22 : (0 <= start)) (PreH23 : (start < hl)) (PreH24 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH25 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= (hs + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (0 <= ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (((hs + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (hp_cstring bytes (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <= UINT64_MAX)) (PreH2 : (retval_4 >= 0)) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
).

Definition strstr_partial_solve_wit_10_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <= UINT64_MAX)) (PreH2 : (retval_4 >= 0)) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr_partial_solve_wit_10_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <= UINT64_MAX)) (PreH2 : (retval_4 >= 0)) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
.

Definition strstr_partial_solve_wit_10_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <= UINT64_MAX)) (PreH2 : (retval_4 >= 0)) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
.

Definition strstr_partial_solve_wit_10_pure_split_goal_4 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <= UINT64_MAX)) (PreH2 : (retval_4 >= 0)) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
.

Definition strstr_partial_solve_wit_10_pure_split_goal_5 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <= UINT64_MAX)) (PreH2 : (retval_4 >= 0)) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
.

Definition strstr_partial_solve_wit_10_pure_split_goal_6 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <= UINT64_MAX)) (PreH2 : (retval_4 >= 0)) (PreH3 : (retval_4 = nl)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 < 256)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_2)) (PreH11 : (retval_2 < 256)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  ((( &( "hs_len" ) )) # UInt64  |->_)
  **  (UCharArray.full base length bytes )
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval_4)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr_partial_solve_wit_10_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = nl)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_3 = (Znth ((no + 3 )) (bytes) (0)))) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 < 256)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (Znth ((no + 2 )) (bytes) (0)))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < 256)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (Znth ((no + 1 )) (bytes) (0)))) (PreH12 : (0 <= retval)) (PreH13 : (retval < 256)) (PreH14 : (haystack = (base + ho ))) (PreH15 : (needle = (base + no ))) (PreH16 : (ne = needle)) (PreH17 : (hs = ((base + ho ) + start ))) (PreH18 : (0 < base)) (PreH19 : ((base + length ) <= UINT_MAX)) (PreH20 : (gs_inputs bytes length ho hl no nl )) (PreH21 : (0 < nl)) (PreH22 : (0 <= start)) (PreH23 : (start < hl)) (PreH24 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH25 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= (hs + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (0 <= ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (((hs + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (hp_cstring bytes (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (retval_4 = nl) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_3 = (Znth ((no + 3 )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval_2 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_10 := strstr_partial_solve_wit_10_pure -> strstr_partial_solve_wit_10_aux.

Definition strstr_partial_solve_wit_11_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval_5 >= retval)) (PreH2 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH3 : (retval = nl)) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_4)) (PreH7 : (retval_4 < 256)) (PreH8 : (retval_3 <> 0)) (PreH9 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 < 256)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 <= (hs + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (0 <= retval) ”
  &&  “ (((hs + ((-base) * sizeof(UCHAR))) + retval ) <= length) ”
  &&  “ ((no + retval ) <= length) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + nl ) <= length) ”
  &&  “ (0 <= no) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (0 <= no) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + nl ) <= length) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + nl ) <= length) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
).

Definition strstr_partial_solve_wit_11_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr_partial_solve_wit_11_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= no) ”
.

Definition strstr_partial_solve_wit_11_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + nl ) <= length) ”
.

Definition strstr_partial_solve_wit_11_pure_split_goal_4 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((no + nl ) <= length) ”
.

Definition strstr_partial_solve_wit_11_pure_split_goal_5 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((no + nl ) <= length) ”
.

Definition strstr_partial_solve_wit_11_pure_split_goal_6 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + nl ) <= length) ”
.

Definition strstr_partial_solve_wit_11_pure_split_goal_7 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_5 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_5 >= 0)) (PreH5 : (retval_5 >= retval)) (PreH6 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH7 : (retval = nl)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH10 : (0 <= retval_4)) (PreH11 : (retval_4 < 256)) (PreH12 : (retval_3 <> 0)) (PreH13 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH14 : (0 <= retval_3)) (PreH15 : (retval_3 < 256)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 < 256)) (PreH20 : (haystack = (base + ho ))) (PreH21 : (needle = (base + no ))) (PreH22 : (ne = needle)) (PreH23 : (hs = ((base + ho ) + start ))) (PreH24 : (0 < base)) (PreH25 : ((base + length ) <= UINT_MAX)) (PreH26 : (gs_inputs bytes length ho hl no nl )) (PreH27 : (0 < nl)) (PreH28 : (0 <= start)) (PreH29 : (start < hl)) (PreH30 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH31 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_5)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr_partial_solve_wit_11_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval_5 >= retval)) (PreH2 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 )) (PreH3 : (retval = nl)) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_4 = (Znth ((no + 3 )) (bytes) (0)))) (PreH6 : (0 <= retval_4)) (PreH7 : (retval_4 < 256)) (PreH8 : (retval_3 <> 0)) (PreH9 : (retval_3 = (Znth ((no + 2 )) (bytes) (0)))) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 < 256)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (Znth ((no + 1 )) (bytes) (0)))) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 < 256)) (PreH16 : (haystack = (base + ho ))) (PreH17 : (needle = (base + no ))) (PreH18 : (ne = needle)) (PreH19 : (hs = ((base + ho ) + start ))) (PreH20 : (0 < base)) (PreH21 : ((base + length ) <= UINT_MAX)) (PreH22 : (gs_inputs bytes length ho hl no nl )) (PreH23 : (0 < nl)) (PreH24 : (0 <= start)) (PreH25 : (start < hl)) (PreH26 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH27 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 <= (hs + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (0 <= retval) ”
  &&  “ (((hs + ((-base) * sizeof(UCHAR))) + retval ) <= length) ”
  &&  “ ((no + retval ) <= length) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + nl ) <= length) ”
  &&  “ (0 <= no) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (retval_5 >= retval) ”
  &&  “ (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_5 ) ”
  &&  “ (retval = nl) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (retval_4 = (Znth ((no + 3 )) (bytes) (0))) ”
  &&  “ (0 <= retval_4) ”
  &&  “ (retval_4 < 256) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_3 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (retval_2 = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_11 := strstr_partial_solve_wit_11_pure -> strstr_partial_solve_wit_11_aux.

Definition strstr_partial_solve_wit_12_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval > 256)) (PreH2 : (retval_6 <> 0)) (PreH3 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH4 : (retval_2 >= retval)) (PreH5 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH6 : (retval = nl)) (PreH7 : (retval_5 <> 0)) (PreH8 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 < 256)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 < 256)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH17 : (0 <= retval_3)) (PreH18 : (retval_3 < 256)) (PreH19 : (haystack = (base + ho ))) (PreH20 : (needle = (base + no ))) (PreH21 : (ne = needle)) (PreH22 : (hs = ((base + ho ) + start ))) (PreH23 : (0 < base)) (PreH24 : ((base + length ) <= UINT_MAX)) (PreH25 : (gs_inputs bytes length ho hl no nl )) (PreH26 : (0 < nl)) (PreH27 : (0 <= start)) (PreH28 : (start < hl)) (PreH29 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH30 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (retval) (32)) ) ”
  &&  “ (256 < (signed_last_nbits (retval) (32))) ”
  &&  “ ((signed_last_nbits (retval) (32)) <= retval_2) ”
  &&  “ (retval_2 <= ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ ((signed_last_nbits (nl) (32)) <= retval_2) ”
  &&  “ (256 < (signed_last_nbits (nl) (32))) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (nl) (32)) ) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (nl) (32)) ) ”
  &&  “ (256 < (signed_last_nbits (nl) (32))) ”
  &&  “ ((signed_last_nbits (nl) (32)) <= retval_2) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ ((signed_last_nbits (nl) (32)) <= retval_2) ”
  &&  “ (256 < (signed_last_nbits (nl) (32))) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (nl) (32)) ) ”
).

Definition strstr_partial_solve_wit_12_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (nl) (32)) ) ”
.

Definition strstr_partial_solve_wit_12_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (256 < (signed_last_nbits (nl) (32))) ”
.

Definition strstr_partial_solve_wit_12_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((signed_last_nbits (nl) (32)) <= retval_2) ”
.

Definition strstr_partial_solve_wit_12_pure_split_goal_4 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
.

Definition strstr_partial_solve_wit_12_pure_split_goal_5 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
.

Definition strstr_partial_solve_wit_12_pure_split_goal_6 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((signed_last_nbits (nl) (32)) <= retval_2) ”
.

Definition strstr_partial_solve_wit_12_pure_split_goal_7 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (256 < (signed_last_nbits (nl) (32))) ”
.

Definition strstr_partial_solve_wit_12_pure_split_goal_8 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval > 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (nl) (32)) ) ”
.

Definition strstr_partial_solve_wit_12_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval > 256)) (PreH2 : (retval_6 <> 0)) (PreH3 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH4 : (retval_2 >= retval)) (PreH5 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH6 : (retval = nl)) (PreH7 : (retval_5 <> 0)) (PreH8 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 < 256)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 < 256)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH17 : (0 <= retval_3)) (PreH18 : (retval_3 < 256)) (PreH19 : (haystack = (base + ho ))) (PreH20 : (needle = (base + no ))) (PreH21 : (ne = needle)) (PreH22 : (hs = ((base + ho ) + start ))) (PreH23 : (0 < base)) (PreH24 : ((base + length ) <= UINT_MAX)) (PreH25 : (gs_inputs bytes length ho hl no nl )) (PreH26 : (0 < nl)) (PreH27 : (0 <= start)) (PreH28 : (start < hl)) (PreH29 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH30 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hs = (base + (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base + no )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (retval) (32)) ) ”
  &&  “ (256 < (signed_last_nbits (retval) (32))) ”
  &&  “ ((signed_last_nbits (retval) (32)) <= retval_2) ”
  &&  “ (retval_2 <= ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ ((signed_last_nbits (nl) (32)) <= retval_2) ”
  &&  “ (256 < (signed_last_nbits (nl) (32))) ”
  &&  “ (gs_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no (signed_last_nbits (nl) (32)) ) ”
  &&  “ (retval > 256) ”
  &&  “ (retval_6 <> 0) ”
  &&  “ (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 ) ”
  &&  “ (retval_2 >= retval) ”
  &&  “ (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 ) ”
  &&  “ (retval = nl) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ (retval_5 = (Znth ((no + 3 )) (bytes) (0))) ”
  &&  “ (0 <= retval_5) ”
  &&  “ (retval_5 < 256) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (retval_4 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_4) ”
  &&  “ (retval_4 < 256) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_3 = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_12 := strstr_partial_solve_wit_12_pure -> strstr_partial_solve_wit_12_aux.

Definition strstr_partial_solve_wit_13_pure :=
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= 256)) (PreH2 : (retval_6 <> 0)) (PreH3 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH4 : (retval_2 >= retval)) (PreH5 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH6 : (retval = nl)) (PreH7 : (retval_5 <> 0)) (PreH8 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 < 256)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 < 256)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH17 : (0 <= retval_3)) (PreH18 : (retval_3 < 256)) (PreH19 : (haystack = (base + ho ))) (PreH20 : (needle = (base + no ))) (PreH21 : (ne = needle)) (PreH22 : (hs = ((base + ho ) + start ))) (PreH23 : (0 < base)) (PreH24 : ((base + length ) <= UINT_MAX)) (PreH25 : (gs_inputs bytes length ho hl no nl )) (PreH26 : (0 < nl)) (PreH27 : (0 <= start)) (PreH28 : (start < hl)) (PreH29 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH30 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hs = (base + ((hs + ((-base) * sizeof(UCHAR))) * sizeof(UCHAR) ) )) ”
  &&  “ (ne = (base + (no * sizeof(UCHAR) ) )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (0 <= (hs + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (retval <= retval_2) ”
  &&  “ (retval_2 <= ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (hp_cstring bytes (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (3 <= retval) ”
  &&  “ (retval <= 256) ”
  &&  “ (((hs + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ ((no + retval ) <= length) ”
  &&  “ (hp_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no retval ) ”
  &&  “ (hp_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no nl ) ”
  &&  “ (length <= INT_MAX) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (3 <= nl) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= no) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
) \/
(
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (0 <= no) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (3 <= nl) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ (length <= INT_MAX) ”
  &&  “ (hp_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no nl ) ”
  &&  “ (hp_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no nl ) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (3 <= nl) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
).

Definition strstr_partial_solve_wit_13_pure_split_goal_1 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_2 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= no) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_3 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_4 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_5 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (3 <= nl) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_6 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_7 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((no + nl ) <= length) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_8 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (length <= INT_MAX) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_9 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hp_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no nl ) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_10 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hp_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no nl ) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_11 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ ((no + nl ) <= length) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_12 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_13 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (3 <= nl) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_14 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_15 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
.

Definition strstr_partial_solve_wit_13_pure_split_goal_16 :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= UINT64_MAX)) (PreH2 : (retval_2 <= UINT64_MAX)) (PreH3 : (retval >= 0)) (PreH4 : (retval_2 >= 0)) (PreH5 : (retval <= 256)) (PreH6 : (retval_6 <> 0)) (PreH7 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH8 : (retval_2 >= retval)) (PreH9 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH10 : (retval = nl)) (PreH11 : (retval_5 <> 0)) (PreH12 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 < 256)) (PreH15 : (retval_4 <> 0)) (PreH16 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 < 256)) (PreH19 : (retval_3 <> 0)) (PreH20 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 < 256)) (PreH23 : (haystack = (base + ho ))) (PreH24 : (needle = (base + no ))) (PreH25 : (ne = needle)) (PreH26 : (hs = ((base + ho ) + start ))) (PreH27 : (0 < base)) (PreH28 : ((base + length ) <= UINT_MAX)) (PreH29 : (gs_inputs bytes length ho hl no nl )) (PreH30 : (0 < nl)) (PreH31 : (0 <= start)) (PreH32 : (start < hl)) (PreH33 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH34 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
  **  ((( &( "hs_len" ) )) # UInt64  |-> retval_2)
  **  ((( &( "ne_len" ) )) # UInt64  |-> retval)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack)
  **  ((( &( "needle" ) )) # Ptr  |-> needle)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
|--
  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
.

Definition strstr_partial_solve_wit_13_aux :=
forall (nl: Z) (no: Z) (hl: Z) (ho: Z) (bytes: (@list Z)) (length: Z) (base: Z) (start: Z) (haystack: Z) (needle: Z) (ne: Z) (hs: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval <= 256)) (PreH2 : (retval_6 <> 0)) (PreH3 : (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 )) (PreH4 : (retval_2 >= retval)) (PreH5 : (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 )) (PreH6 : (retval = nl)) (PreH7 : (retval_5 <> 0)) (PreH8 : (retval_5 = (Znth ((no + 3 )) (bytes) (0)))) (PreH9 : (0 <= retval_5)) (PreH10 : (retval_5 < 256)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (Znth ((no + 2 )) (bytes) (0)))) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 < 256)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (Znth ((no + 1 )) (bytes) (0)))) (PreH17 : (0 <= retval_3)) (PreH18 : (retval_3 < 256)) (PreH19 : (haystack = (base + ho ))) (PreH20 : (needle = (base + no ))) (PreH21 : (ne = needle)) (PreH22 : (hs = ((base + ho ) + start ))) (PreH23 : (0 < base)) (PreH24 : ((base + length ) <= UINT_MAX)) (PreH25 : (gs_inputs bytes length ho hl no nl )) (PreH26 : (0 < nl)) (PreH27 : (0 <= start)) (PreH28 : (start < hl)) (PreH29 : ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0)))) (PreH30 : (hp_no_match_before bytes ho hl no nl start )),
  (UCharArray.full base length bytes )
|--
  “ (hs = (base + ((hs + ((-base) * sizeof(UCHAR))) * sizeof(UCHAR) ) )) ”
  &&  “ (ne = (base + (no * sizeof(UCHAR) ) )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (0 <= (hs + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (retval <= retval_2) ”
  &&  “ (retval_2 <= ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (hp_cstring bytes (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (3 <= retval) ”
  &&  “ (retval <= 256) ”
  &&  “ (((hs + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ ((no + retval ) <= length) ”
  &&  “ (hp_inputs bytes length (hs + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) no retval ) ”
  &&  “ (hp_inputs bytes length (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) no nl ) ”
  &&  “ (length <= INT_MAX) ”
  &&  “ ((no + nl ) <= length) ”
  &&  “ (((((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) + ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) < length) ”
  &&  “ (3 <= nl) ”
  &&  “ (hp_cstring bytes (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) ) ) ”
  &&  “ (retval_2 <= ((ho + hl ) - (((base + ho ) + start ) + ((-base) * sizeof(UCHAR))) )) ”
  &&  “ (0 <= no) ”
  &&  “ (0 <= (((base + ho ) + start ) + ((-base) * sizeof(UCHAR)))) ”
  &&  “ (retval <= 256) ”
  &&  “ (retval_6 <> 0) ”
  &&  “ (hp_memcmp_result bytes (hs + ((-base) * sizeof(UCHAR))) no retval retval_6 ) ”
  &&  “ (retval_2 >= retval) ”
  &&  “ (gs_probe ((ho + hl ) - (hs + ((-base) * sizeof(UCHAR))) ) (Z.lor retval 512) retval_2 ) ”
  &&  “ (retval = nl) ”
  &&  “ (retval_5 <> 0) ”
  &&  “ (retval_5 = (Znth ((no + 3 )) (bytes) (0))) ”
  &&  “ (0 <= retval_5) ”
  &&  “ (retval_5 < 256) ”
  &&  “ (retval_4 <> 0) ”
  &&  “ (retval_4 = (Znth ((no + 2 )) (bytes) (0))) ”
  &&  “ (0 <= retval_4) ”
  &&  “ (retval_4 < 256) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (retval_3 = (Znth ((no + 1 )) (bytes) (0))) ”
  &&  “ (0 <= retval_3) ”
  &&  “ (retval_3 < 256) ”
  &&  “ (haystack = (base + ho )) ”
  &&  “ (needle = (base + no )) ”
  &&  “ (ne = needle) ”
  &&  “ (hs = ((base + ho ) + start )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (gs_inputs bytes length ho hl no nl ) ”
  &&  “ (0 < nl) ”
  &&  “ (0 <= start) ”
  &&  “ (start < hl) ”
  &&  “ ((Znth ((ho + start )) (bytes) (0)) = (Znth (no) (bytes) (0))) ”
  &&  “ (hp_no_match_before bytes ho hl no nl start ) ”
  &&  (UCharArray.full base length bytes )
.

Definition strstr_partial_solve_wit_13 := strstr_partial_solve_wit_13_pure -> strstr_partial_solve_wit_13_aux.

Module Type VC_Correct.


Axiom proof_of_gs_read_safety_wit_1 : gs_read_safety_wit_1.
Axiom proof_of_gs_read_entail_wit_1 : gs_read_entail_wit_1.
Axiom proof_of_gs_read_return_wit_1 : gs_read_return_wit_1.
Axiom proof_of_gs_read_partial_solve_wit_1 : gs_read_partial_solve_wit_1.
Axiom proof_of_strstr2_safety_wit_1 : strstr2_safety_wit_1.
Axiom proof_of_strstr2_safety_wit_2 : strstr2_safety_wit_2.
Axiom proof_of_strstr2_safety_wit_3 : strstr2_safety_wit_3.
Axiom proof_of_strstr2_safety_wit_4 : strstr2_safety_wit_4.
Axiom proof_of_strstr2_safety_wit_5 : strstr2_safety_wit_5.
Axiom proof_of_strstr2_safety_wit_6 : strstr2_safety_wit_6.
Axiom proof_of_strstr2_safety_wit_7 : strstr2_safety_wit_7.
Axiom proof_of_strstr2_safety_wit_8 : strstr2_safety_wit_8.
Axiom proof_of_strstr2_safety_wit_9 : strstr2_safety_wit_9.
Axiom proof_of_strstr2_safety_wit_10 : strstr2_safety_wit_10.
Axiom proof_of_strstr2_safety_wit_11 : strstr2_safety_wit_11.
Axiom proof_of_strstr2_entail_wit_1 : strstr2_entail_wit_1.
Axiom proof_of_strstr2_entail_wit_2 : strstr2_entail_wit_2.
Axiom proof_of_strstr2_return_wit_1 : strstr2_return_wit_1.
Axiom proof_of_strstr2_return_wit_2 : strstr2_return_wit_2.
Axiom proof_of_strstr2_partial_solve_wit_1_pure : strstr2_partial_solve_wit_1_pure.
Axiom proof_of_strstr2_partial_solve_wit_1 : strstr2_partial_solve_wit_1.
Axiom proof_of_strstr2_partial_solve_wit_2_pure : strstr2_partial_solve_wit_2_pure.
Axiom proof_of_strstr2_partial_solve_wit_2 : strstr2_partial_solve_wit_2.
Axiom proof_of_strstr2_partial_solve_wit_3_pure : strstr2_partial_solve_wit_3_pure.
Axiom proof_of_strstr2_partial_solve_wit_3 : strstr2_partial_solve_wit_3.
Axiom proof_of_strstr2_partial_solve_wit_4_pure : strstr2_partial_solve_wit_4_pure.
Axiom proof_of_strstr2_partial_solve_wit_4 : strstr2_partial_solve_wit_4.
Axiom proof_of_strstr3_safety_wit_1 : strstr3_safety_wit_1.
Axiom proof_of_strstr3_safety_wit_2 : strstr3_safety_wit_2.
Axiom proof_of_strstr3_safety_wit_3 : strstr3_safety_wit_3.
Axiom proof_of_strstr3_safety_wit_4 : strstr3_safety_wit_4.
Axiom proof_of_strstr3_safety_wit_5 : strstr3_safety_wit_5.
Axiom proof_of_strstr3_safety_wit_6 : strstr3_safety_wit_6.
Axiom proof_of_strstr3_safety_wit_7 : strstr3_safety_wit_7.
Axiom proof_of_strstr3_safety_wit_8 : strstr3_safety_wit_8.
Axiom proof_of_strstr3_safety_wit_9 : strstr3_safety_wit_9.
Axiom proof_of_strstr3_safety_wit_10 : strstr3_safety_wit_10.
Axiom proof_of_strstr3_safety_wit_11 : strstr3_safety_wit_11.
Axiom proof_of_strstr3_safety_wit_12 : strstr3_safety_wit_12.
Axiom proof_of_strstr3_safety_wit_13 : strstr3_safety_wit_13.
Axiom proof_of_strstr3_safety_wit_14 : strstr3_safety_wit_14.
Axiom proof_of_strstr3_safety_wit_15 : strstr3_safety_wit_15.
Axiom proof_of_strstr3_safety_wit_16 : strstr3_safety_wit_16.
Axiom proof_of_strstr3_entail_wit_1 : strstr3_entail_wit_1.
Axiom proof_of_strstr3_entail_wit_2 : strstr3_entail_wit_2.
Axiom proof_of_strstr3_return_wit_1 : strstr3_return_wit_1.
Axiom proof_of_strstr3_return_wit_2 : strstr3_return_wit_2.
Axiom proof_of_strstr3_partial_solve_wit_1_pure : strstr3_partial_solve_wit_1_pure.
Axiom proof_of_strstr3_partial_solve_wit_1 : strstr3_partial_solve_wit_1.
Axiom proof_of_strstr3_partial_solve_wit_2_pure : strstr3_partial_solve_wit_2_pure.
Axiom proof_of_strstr3_partial_solve_wit_2 : strstr3_partial_solve_wit_2.
Axiom proof_of_strstr3_partial_solve_wit_3_pure : strstr3_partial_solve_wit_3_pure.
Axiom proof_of_strstr3_partial_solve_wit_3 : strstr3_partial_solve_wit_3.
Axiom proof_of_strstr3_partial_solve_wit_4_pure : strstr3_partial_solve_wit_4_pure.
Axiom proof_of_strstr3_partial_solve_wit_4 : strstr3_partial_solve_wit_4.
Axiom proof_of_strstr3_partial_solve_wit_5_pure : strstr3_partial_solve_wit_5_pure.
Axiom proof_of_strstr3_partial_solve_wit_5 : strstr3_partial_solve_wit_5.
Axiom proof_of_strstr_safety_wit_1 : strstr_safety_wit_1.
Axiom proof_of_strstr_safety_wit_2 : strstr_safety_wit_2.
Axiom proof_of_strstr_safety_wit_3 : strstr_safety_wit_3.
Axiom proof_of_strstr_safety_wit_4 : strstr_safety_wit_4.
Axiom proof_of_strstr_safety_wit_5 : strstr_safety_wit_5.
Axiom proof_of_strstr_safety_wit_6 : strstr_safety_wit_6.
Axiom proof_of_strstr_safety_wit_7 : strstr_safety_wit_7.
Axiom proof_of_strstr_safety_wit_8 : strstr_safety_wit_8.
Axiom proof_of_strstr_safety_wit_9 : strstr_safety_wit_9.
Axiom proof_of_strstr_safety_wit_10 : strstr_safety_wit_10.
Axiom proof_of_strstr_safety_wit_11 : strstr_safety_wit_11.
Axiom proof_of_strstr_safety_wit_12 : strstr_safety_wit_12.
Axiom proof_of_strstr_entail_wit_1 : strstr_entail_wit_1.
Axiom proof_of_strstr_return_wit_1 : strstr_return_wit_1.
Axiom proof_of_strstr_return_wit_2 : strstr_return_wit_2.
Axiom proof_of_strstr_return_wit_3 : strstr_return_wit_3.
Axiom proof_of_strstr_return_wit_4 : strstr_return_wit_4.
Axiom proof_of_strstr_return_wit_5 : strstr_return_wit_5.
Axiom proof_of_strstr_return_wit_6 : strstr_return_wit_6.
Axiom proof_of_strstr_return_wit_7 : strstr_return_wit_7.
Axiom proof_of_strstr_return_wit_8 : strstr_return_wit_8.
Axiom proof_of_strstr_return_wit_9 : strstr_return_wit_9.
Axiom proof_of_strstr_partial_solve_wit_1_pure : strstr_partial_solve_wit_1_pure.
Axiom proof_of_strstr_partial_solve_wit_1 : strstr_partial_solve_wit_1.
Axiom proof_of_strstr_partial_solve_wit_2_pure : strstr_partial_solve_wit_2_pure.
Axiom proof_of_strstr_partial_solve_wit_2 : strstr_partial_solve_wit_2.
Axiom proof_of_strstr_partial_solve_wit_3_pure : strstr_partial_solve_wit_3_pure.
Axiom proof_of_strstr_partial_solve_wit_3 : strstr_partial_solve_wit_3.
Axiom proof_of_strstr_partial_solve_wit_4_pure : strstr_partial_solve_wit_4_pure.
Axiom proof_of_strstr_partial_solve_wit_4 : strstr_partial_solve_wit_4.
Axiom proof_of_strstr_partial_solve_wit_5_pure : strstr_partial_solve_wit_5_pure.
Axiom proof_of_strstr_partial_solve_wit_5 : strstr_partial_solve_wit_5.
Axiom proof_of_strstr_partial_solve_wit_6_pure : strstr_partial_solve_wit_6_pure.
Axiom proof_of_strstr_partial_solve_wit_6 : strstr_partial_solve_wit_6.
Axiom proof_of_strstr_partial_solve_wit_7_pure : strstr_partial_solve_wit_7_pure.
Axiom proof_of_strstr_partial_solve_wit_7 : strstr_partial_solve_wit_7.
Axiom proof_of_strstr_partial_solve_wit_8_pure : strstr_partial_solve_wit_8_pure.
Axiom proof_of_strstr_partial_solve_wit_8 : strstr_partial_solve_wit_8.
Axiom proof_of_strstr_partial_solve_wit_9_pure : strstr_partial_solve_wit_9_pure.
Axiom proof_of_strstr_partial_solve_wit_9 : strstr_partial_solve_wit_9.
Axiom proof_of_strstr_partial_solve_wit_10_pure : strstr_partial_solve_wit_10_pure.
Axiom proof_of_strstr_partial_solve_wit_10 : strstr_partial_solve_wit_10.
Axiom proof_of_strstr_partial_solve_wit_11_pure : strstr_partial_solve_wit_11_pure.
Axiom proof_of_strstr_partial_solve_wit_11 : strstr_partial_solve_wit_11.
Axiom proof_of_strstr_partial_solve_wit_12_pure : strstr_partial_solve_wit_12_pure.
Axiom proof_of_strstr_partial_solve_wit_12 : strstr_partial_solve_wit_12.
Axiom proof_of_strstr_partial_solve_wit_13_pure : strstr_partial_solve_wit_13_pure.
Axiom proof_of_strstr_partial_solve_wit_13 : strstr_partial_solve_wit_13.

End VC_Correct.
