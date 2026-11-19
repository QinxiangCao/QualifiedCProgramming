From SimpleC.Verification Require Import VCPrelude.
Import Snaive_C_Rules64.
Require Import SimpleC.EE.stdlib.glibc.memmove_lib.
Local Open Scope sac.

(*----- Function mm_load_byte -----*)

Definition mm_load_byte_entail_wit_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_in p_pre b1 n1 b2 n2 )) (PreH4 : (mm_initialized m p_pre )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
|--
  (EX (v: Z),
  “ ((mm_lookup (m) (p_pre)) = (Some (v))) ”
  &&  “ (b2 <= p_pre) ”
  &&  “ (p_pre < (b2 + n2 )) ”
  &&  “ ((Znth ((p_pre + ((-b2) * sizeof(UCHAR)))) ((mm_cells (b2) (n2) (m))) (None)) = (Some (v))) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) ))
  ||
  (EX (v: Z),
  “ ((mm_lookup (m) (p_pre)) = (Some (v))) ”
  &&  “ (b1 <= p_pre) ”
  &&  “ (p_pre < (b1 + n1 )) ”
  &&  “ ((Znth ((p_pre + ((-b1) * sizeof(UCHAR)))) ((mm_cells (b1) (n1) (m))) (None)) = (Some (v))) ”
  &&  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) ))
.

Definition mm_load_byte_return_wit_1 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b1 <= p_pre)) (PreH3 : (p_pre < (b1 + n1 ))) (PreH4 : ((Znth ((p_pre + ((-b1) * sizeof(UCHAR)))) ((mm_cells (b1) (n1) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
|--
  “ ((mm_lookup (m) (p_pre)) = (Some (v))) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= 255) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
) \/
(
forall (m: mm_memory) (n1: Z) (b1: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b1 <= p_pre)) (PreH3 : (p_pre < (b1 + n1 ))) (PreH4 : ((Znth ((p_pre + ((-b1) * sizeof(UCHAR)))) ((mm_cells (b1) (n1) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
|--
  “ (v <= 255) ”
  &&  “ (0 <= v) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
).

Definition mm_load_byte_return_wit_1_split_goal_1 :=
forall (m: mm_memory) (n1: Z) (b1: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b1 <= p_pre)) (PreH3 : (p_pre < (b1 + n1 ))) (PreH4 : ((Znth ((p_pre + ((-b1) * sizeof(UCHAR)))) ((mm_cells (b1) (n1) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
|--
  “ (v <= 255) ”
.

Definition mm_load_byte_return_wit_1_split_goal_2 :=
forall (m: mm_memory) (n1: Z) (b1: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b1 <= p_pre)) (PreH3 : (p_pre < (b1 + n1 ))) (PreH4 : ((Znth ((p_pre + ((-b1) * sizeof(UCHAR)))) ((mm_cells (b1) (n1) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
|--
  “ (0 <= v) ”
.

Definition mm_load_byte_return_wit_1_split_goal_spatial :=
forall (m: mm_memory) (n1: Z) (b1: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b1 <= p_pre)) (PreH3 : (p_pre < (b1 + n1 ))) (PreH4 : ((Znth ((p_pre + ((-b1) * sizeof(UCHAR)))) ((mm_cells (b1) (n1) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
|--
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
.

Definition mm_load_byte_return_wit_2 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b2 <= p_pre)) (PreH3 : (p_pre < (b2 + n2 ))) (PreH4 : ((Znth ((p_pre + ((-b2) * sizeof(UCHAR)))) ((mm_cells (b2) (n2) (m))) (None)) = (Some (v)))),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  “ ((mm_lookup (m) (p_pre)) = (Some (v))) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= 255) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b2 <= p_pre)) (PreH3 : (p_pre < (b2 + n2 ))) (PreH4 : ((Znth ((p_pre + ((-b2) * sizeof(UCHAR)))) ((mm_cells (b2) (n2) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  “ (v <= 255) ”
  &&  “ (0 <= v) ”
  &&  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
).

Definition mm_load_byte_return_wit_2_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b2 <= p_pre)) (PreH3 : (p_pre < (b2 + n2 ))) (PreH4 : ((Znth ((p_pre + ((-b2) * sizeof(UCHAR)))) ((mm_cells (b2) (n2) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  “ (v <= 255) ”
.

Definition mm_load_byte_return_wit_2_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b2 <= p_pre)) (PreH3 : (p_pre < (b2 + n2 ))) (PreH4 : ((Znth ((p_pre + ((-b2) * sizeof(UCHAR)))) ((mm_cells (b2) (n2) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  “ (0 <= v) ”
.

Definition mm_load_byte_return_wit_2_split_goal_spatial :=
forall (m: mm_memory) (n2: Z) (b2: Z) (p_pre: Z) (v: Z) (PreH1 : ((mm_lookup (m) (p_pre)) = (Some (v)))) (PreH2 : (b2 <= p_pre)) (PreH3 : (p_pre < (b2 + n2 ))) (PreH4 : ((Znth ((p_pre + ((-b2) * sizeof(UCHAR)))) ((mm_cells (b2) (n2) (m))) (None)) = (Some (v)))),
  ((p_pre) # UChar  |-> v)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
.

(*----- Function mm_store_byte -----*)

Definition mm_store_byte_entail_wit_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_in p_pre b1 n1 b2 n2 )) (PreH4 : (mm_separated b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
|--
  (“ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (b1 <= p_pre) ”
  &&  “ (p_pre < (b1 + n1 )) ”
  &&  ((p_pre) # UChar  |->_)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) ))
  ||
  (“ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (b2 <= p_pre) ”
  &&  “ (p_pre < (b2 + n2 )) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  ((p_pre) # UChar  |->_)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) ))
.

Definition mm_store_byte_return_wit_1 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b1 <= p_pre)) (PreH5 : (p_pre < (b1 + n1 ))),
  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
|--
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b1 <= p_pre)) (PreH5 : (p_pre < (b1 + n1 ))),
  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
|--
  “ ((mm_cells (b2) (n2) (m)) = (mm_cells (b2) (n2) ((mm_write (m) (p_pre) ((Some (value_pre))))))) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
).

Definition mm_store_byte_return_wit_1_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b1 <= p_pre)) (PreH5 : (p_pre < (b1 + n1 ))),
  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
|--
  “ ((mm_cells (b2) (n2) (m)) = (mm_cells (b2) (n2) ((mm_write (m) (p_pre) ((Some (value_pre))))))) ”
.

Definition mm_store_byte_return_wit_1_split_goal_spatial :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b1 <= p_pre)) (PreH5 : (p_pre < (b1 + n1 ))),
  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b1 - p_pre ) ((b1 + n1 ) - p_pre ) (mm_cells (b1) (n1) (m)) )
|--
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
.

Definition mm_store_byte_return_wit_2 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b2 <= p_pre)) (PreH5 : (p_pre < (b2 + n2 ))),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b2 <= p_pre)) (PreH5 : (p_pre < (b2 + n2 ))),
  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  “ ((mm_cells (b1) (n1) (m)) = (mm_cells (b1) (n1) ((mm_write (m) (p_pre) ((Some (value_pre))))))) ”
  &&  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
).

Definition mm_store_byte_return_wit_2_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b2 <= p_pre)) (PreH5 : (p_pre < (b2 + n2 ))),
  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  “ ((mm_cells (b1) (n1) (m)) = (mm_cells (b1) (n1) ((mm_write (m) (p_pre) ((Some (value_pre))))))) ”
.

Definition mm_store_byte_return_wit_2_split_goal_spatial :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (p_pre: Z) (value_pre: Z) (PreH1 : (0 <= n1)) (PreH2 : (0 <= n2)) (PreH3 : (mm_separated b1 n1 b2 n2 )) (PreH4 : (b2 <= p_pre)) (PreH5 : (p_pre < (b2 + n2 ))),
  ((p_pre) # UChar  |-> value_pre)
  **  (UCharArray.mixed_missing_i p_pre 0 (b2 - p_pre ) ((b2 + n2 ) - p_pre ) (mm_cells (b2) (n2) (m)) )
|--
  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write (m) (p_pre) ((Some (value_pre)))))) )
.

Module Type VC_Correct.


Axiom proof_of_mm_load_byte_entail_wit_1 : mm_load_byte_entail_wit_1.
Axiom proof_of_mm_load_byte_return_wit_1 : mm_load_byte_return_wit_1.
Axiom proof_of_mm_load_byte_return_wit_2 : mm_load_byte_return_wit_2.
Axiom proof_of_mm_store_byte_entail_wit_1 : mm_store_byte_entail_wit_1.
Axiom proof_of_mm_store_byte_return_wit_1 : mm_store_byte_return_wit_1.
Axiom proof_of_mm_store_byte_return_wit_2 : mm_store_byte_return_wit_2.

End VC_Correct.
