From SimpleC.Verification Require Import VCPrelude.
Import Snaive_C_Rules64.
Require Import SimpleC.EE.stdlib.glibc.memmove_lib.
Require Import SimpleC.EE.stdlib.glibc.memmove_contract_lib.
Local Open Scope sac.

(*----- Function mm_copy_forward -----*)

Definition mm_copy_forward_safety_wit_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (remaining = (n_pre - i ))) (PreH4 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (dest_pre <= src_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mm_copy_forward_safety_wit_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (remaining = (n_pre - i ))) (PreH4 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mm_copy_forward_safety_wit_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (dest_pre <= src_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_forward_safety_wit_4 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_forward_safety_wit_5 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (dest_pre <= src_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_forward_safety_wit_6 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_forward_safety_wit_7 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (dest_pre <= src_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_forward_safety_wit_8 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_forward_entail_wit_1_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1)) (PreH3 : (0 <= n2)) (PreH4 : (0 <= src_pre)) (PreH5 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : (0 <= dest_pre)) (PreH7 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH8 : (dest_pre <= src_pre)) (PreH9 : (mm_separated b1 n1 b2 n2 )) (PreH10 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
|--
  (EX (i: Z),
  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (n_pre = (n_pre - i )) ”
  &&  “ (src_pre = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest_pre = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (dest_pre <= src_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) ))
  ||
  (EX (i: Z),
  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (n_pre = (n_pre - i )) ”
  &&  “ (src_pre = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest_pre = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) ))
.

Definition mm_copy_forward_entail_wit_1_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1)) (PreH3 : (0 <= n2)) (PreH4 : (0 <= src_pre)) (PreH5 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : (0 <= dest_pre)) (PreH7 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH8 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH9 : (mm_separated b1 n1 b2 n2 )) (PreH10 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
|--
  (EX (i: Z),
  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (n_pre = (n_pre - i )) ”
  &&  “ (src_pre = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest_pre = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (dest_pre <= src_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) ))
  ||
  (EX (i: Z),
  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (n_pre = (n_pre - i )) ”
  &&  “ (src_pre = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest_pre = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) ))
.

Definition mm_copy_forward_entail_wit_2_1 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i_2: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= n_pre)) (PreH7 : (remaining = (n_pre - i_2 ))) (PreH8 : (src = (src_pre + (i_2 * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i_2 * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (dest_pre <= src_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
|--
  EX (i: Z),
  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((remaining - 1 ) = (n_pre - i )) ”
  &&  “ ((src + (1 * sizeof(UCHAR))) = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ ((dest + (1 * sizeof(UCHAR))) = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (dest_pre <= src_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i_2: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= n_pre)) (PreH7 : (remaining = (n_pre - i_2 ))) (PreH8 : (src = (src_pre + (i_2 * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i_2 * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (dest_pre <= src_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  TT && emp 
|--
  EX (i: Z),
  “ ((mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i_2 ) - 1 ) ) - 1 )))) ((dest_pre + (i_2 * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i))))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i_2 ) - 1 ) ) - 1 )))) ((dest_pre + (i_2 * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (((n_pre - i_2 ) - 1 ) = (n_pre - i )) ”
  &&  “ (((src_pre + (i_2 * sizeof(UCHAR))) + (1 * sizeof(UCHAR))) = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (((dest_pre + (i_2 * sizeof(UCHAR))) + (1 * sizeof(UCHAR))) = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  emp
).

Definition mm_copy_forward_entail_wit_2_2 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i_2: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= n_pre)) (PreH7 : (remaining = (n_pre - i_2 ))) (PreH8 : (src = (src_pre + (i_2 * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i_2 * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 )))) (dest) ((Some (retval)))))) )
|--
  EX (i: Z),
  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((remaining - 1 ) = (n_pre - i )) ”
  &&  “ ((src + (1 * sizeof(UCHAR))) = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ ((dest + (1 * sizeof(UCHAR))) = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i_2: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= n_pre)) (PreH7 : (remaining = (n_pre - i_2 ))) (PreH8 : (src = (src_pre + (i_2 * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i_2 * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  TT && emp 
|--
  EX (i: Z),
  “ ((mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i_2 ) - 1 ) ) - 1 )))) ((dest_pre + (i_2 * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i))))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i_2 ) - 1 ) ) - 1 )))) ((dest_pre + (i_2 * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (((n_pre - i_2 ) - 1 ) = (n_pre - i )) ”
  &&  “ (((src_pre + (i_2 * sizeof(UCHAR))) + (1 * sizeof(UCHAR))) = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (((dest_pre + (i_2 * sizeof(UCHAR))) + (1 * sizeof(UCHAR))) = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  emp
).

Definition mm_copy_forward_return_wit_1 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (dest_pre <= src_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (dest_pre <= src_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  TT && emp 
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre))))) ”
  &&  emp
).

Definition mm_copy_forward_return_wit_1_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (dest_pre <= src_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))))
.

Definition mm_copy_forward_return_wit_1_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (dest_pre <= src_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))))
.

Definition mm_copy_forward_return_wit_2 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  TT && emp 
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre))))) ”
  &&  emp
).

Definition mm_copy_forward_return_wit_2_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))))
.

Definition mm_copy_forward_return_wit_2_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))))
.

Definition mm_copy_forward_partial_solve_wit_1_pure :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (dest_pre <= src_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))) src ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
  &&  “ (mm_in src b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (dest_pre <= src_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ (mm_in src b1 n1 b2 n2 ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
).

Definition mm_copy_forward_partial_solve_wit_1_pure_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (dest_pre <= src_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_1_pure_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (dest_pre <= src_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_1_pure_split_goal_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (dest_pre <= src_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (mm_in src b1 n1 b2 n2 ) ”
.

Definition mm_copy_forward_partial_solve_wit_1_pure_split_goal_4 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (dest_pre <= src_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
.

Definition mm_copy_forward_partial_solve_wit_1_pure_split_goal_5 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (dest_pre <= src_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
.

Definition mm_copy_forward_partial_solve_wit_1_aux :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (dest_pre <= src_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))) src ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
  &&  “ (mm_in src b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ (remaining > 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (remaining = (n_pre - i )) ”
  &&  “ (src = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (dest_pre <= src_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
.

Definition mm_copy_forward_partial_solve_wit_1 := mm_copy_forward_partial_solve_wit_1_pure -> mm_copy_forward_partial_solve_wit_1_aux.

Definition mm_copy_forward_partial_solve_wit_2_pure :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))) src ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
  &&  “ (mm_in src b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ (mm_in src b1 n1 b2 n2 ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
).

Definition mm_copy_forward_partial_solve_wit_2_pure_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_2_pure_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_2_pure_split_goal_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (mm_in src b1 n1 b2 n2 ) ”
.

Definition mm_copy_forward_partial_solve_wit_2_pure_split_goal_4 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
.

Definition mm_copy_forward_partial_solve_wit_2_pure_split_goal_5 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : (remaining >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (remaining = (n_pre - i ))) (PreH9 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH10 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH11 : (0 <= n1)) (PreH12 : (0 <= n2)) (PreH13 : (0 <= src_pre)) (PreH14 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (0 <= dest_pre)) (PreH16 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH18 : (mm_separated b1 n1 b2 n2 )) (PreH19 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
.

Definition mm_copy_forward_partial_solve_wit_2_aux :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (PreH1 : (remaining > 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (remaining = (n_pre - i ))) (PreH5 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH6 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH7 : (0 <= n1)) (PreH8 : (0 <= n2)) (PreH9 : (0 <= src_pre)) (PreH10 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (0 <= dest_pre)) (PreH12 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH14 : (mm_separated b1 n1 b2 n2 )) (PreH15 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))) src ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))) src ) ”
  &&  “ (mm_in src b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (i)))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) )))))) ”
  &&  “ (remaining > 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (remaining = (n_pre - i )) ”
  &&  “ (src = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
.

Definition mm_copy_forward_partial_solve_wit_2 := mm_copy_forward_partial_solve_wit_2_pure -> mm_copy_forward_partial_solve_wit_2_aux.

Definition mm_copy_forward_partial_solve_wit_3_pure :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (dest_pre <= src_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_in dest b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : (dest_pre <= src_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ (mm_in dest b1 n1 b2 n2 ) ”
).

Definition mm_copy_forward_partial_solve_wit_3_pure_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : (dest_pre <= src_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_3_pure_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : (dest_pre <= src_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_3_pure_split_goal_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : (dest_pre <= src_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (mm_in dest b1 n1 b2 n2 ) ”
.

Definition mm_copy_forward_partial_solve_wit_3_aux :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (dest_pre <= src_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_in dest b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= 255) ”
  &&  “ (remaining > 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (remaining = (n_pre - i )) ”
  &&  “ (src = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (dest_pre <= src_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 ))))) )
.

Definition mm_copy_forward_partial_solve_wit_3 := mm_copy_forward_partial_solve_wit_3_pure -> mm_copy_forward_partial_solve_wit_3_aux.

Definition mm_copy_forward_partial_solve_wit_4_pure :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_in dest b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ (mm_in dest b1 n1 b2 n2 ) ”
).

Definition mm_copy_forward_partial_solve_wit_4_pure_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_4_pure_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
.

Definition mm_copy_forward_partial_solve_wit_4_pure_split_goal_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((remaining - 1 ) <= UINT64_MAX)) (PreH2 : (n_pre <= UINT64_MAX)) (PreH3 : ((remaining - 1 ) >= 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (remaining = (n_pre - i ))) (PreH12 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH13 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH14 : (0 <= n1)) (PreH15 : (0 <= n2)) (PreH16 : (0 <= src_pre)) (PreH17 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH18 : (0 <= dest_pre)) (PreH19 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH20 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH21 : (mm_separated b1 n1 b2 n2 )) (PreH22 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "src" ) )) # Ptr  |-> (src + (1 * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (mm_in dest b1 n1 b2 n2 ) ”
.

Definition mm_copy_forward_partial_solve_wit_4_aux :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (i: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (remaining = (n_pre - i ))) (PreH8 : (src = (src_pre + (i * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (i * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining ))))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_in dest b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - (n_pre - i ) ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - ((n_pre - i ) - 1 ) ) - 1 )))))) ”
  &&  “ ((mm_lookup ((mm_snapshot (m) (src_pre) (dest_pre) ((n_pre - remaining )))) (src)) = (Some (retval))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= 255) ”
  &&  “ (remaining > 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (remaining = (n_pre - i )) ”
  &&  “ (src = (src_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (dest = (dest_pre + (i * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (((n_pre - (remaining - 1 ) ) - 1 ))))) )
.

Definition mm_copy_forward_partial_solve_wit_4 := mm_copy_forward_partial_solve_wit_4_pure -> mm_copy_forward_partial_solve_wit_4_aux.

(*----- Function mm_copy_backward -----*)

Definition mm_copy_backward_safety_wit_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (0 <= remaining)) (PreH2 : (remaining <= n_pre)) (PreH3 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH4 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (0 <= n1)) (PreH6 : (0 <= n2)) (PreH7 : (0 <= src_pre)) (PreH8 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH9 : (0 <= dest_pre)) (PreH10 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : (src_pre <= dest_pre)) (PreH12 : (mm_separated b1 n1 b2 n2 )) (PreH13 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mm_copy_backward_safety_wit_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (remaining > 0)) (PreH2 : (0 <= remaining)) (PreH3 : (remaining <= n_pre)) (PreH4 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (src_pre <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_backward_safety_wit_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_backward_safety_wit_4 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> (dest + ((-1) * sizeof(UCHAR))))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mm_copy_backward_entail_wit_1 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1)) (PreH3 : (0 <= n2)) (PreH4 : (0 <= src_pre)) (PreH5 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : (0 <= dest_pre)) (PreH7 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH8 : (src_pre <= dest_pre)) (PreH9 : (mm_separated b1 n1 b2 n2 )) (PreH10 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre <= n_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) = (src_pre + (n_pre * sizeof(UCHAR)))) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) = (dest_pre + (n_pre * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (src_pre <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (n_pre * sizeof(UCHAR)))) ((dest_pre + (n_pre * sizeof(UCHAR)))) ((n_pre - n_pre ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (n_pre * sizeof(UCHAR)))) ((dest_pre + (n_pre * sizeof(UCHAR)))) ((n_pre - n_pre ))))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1)) (PreH3 : (0 <= n2)) (PreH4 : (0 <= src_pre)) (PreH5 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : (0 <= dest_pre)) (PreH7 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH8 : (src_pre <= dest_pre)) (PreH9 : (mm_separated b1 n1 b2 n2 )) (PreH10 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  TT && emp 
|--
  “ ((mm_cells (b1) (n1) (m)) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (n_pre * sizeof(UCHAR)))) ((dest_pre + (n_pre * sizeof(UCHAR)))) ((n_pre - n_pre )))))) ”
  &&  “ ((mm_cells (b2) (n2) (m)) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (n_pre * sizeof(UCHAR)))) ((dest_pre + (n_pre * sizeof(UCHAR)))) ((n_pre - n_pre )))))) ”
  &&  emp
).

Definition mm_copy_backward_entail_wit_1_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1)) (PreH3 : (0 <= n2)) (PreH4 : (0 <= src_pre)) (PreH5 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : (0 <= dest_pre)) (PreH7 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH8 : (src_pre <= dest_pre)) (PreH9 : (mm_separated b1 n1 b2 n2 )) (PreH10 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b1) (n1) (m)) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (n_pre * sizeof(UCHAR)))) ((dest_pre + (n_pre * sizeof(UCHAR)))) ((n_pre - n_pre ))))))
.

Definition mm_copy_backward_entail_wit_1_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1)) (PreH3 : (0 <= n2)) (PreH4 : (0 <= src_pre)) (PreH5 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : (0 <= dest_pre)) (PreH7 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH8 : (src_pre <= dest_pre)) (PreH9 : (mm_separated b1 n1 b2 n2 )) (PreH10 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b2) (n2) (m)) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (n_pre * sizeof(UCHAR)))) ((dest_pre + (n_pre * sizeof(UCHAR)))) ((n_pre - n_pre ))))))
.

Definition mm_copy_backward_entail_wit_2 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))) ((dest + ((-1) * sizeof(UCHAR)))) ((Some (retval)))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))) ((dest + ((-1) * sizeof(UCHAR)))) ((Some (retval)))))) )
|--
  “ (0 <= (remaining - 1 )) ”
  &&  “ ((remaining - 1 ) <= n_pre) ”
  &&  “ ((src + ((-1) * sizeof(UCHAR))) = (src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ”
  &&  “ ((dest + ((-1) * sizeof(UCHAR))) = (dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (src_pre <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((n_pre - (remaining - 1 ) ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((n_pre - (remaining - 1 ) ))))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  TT && emp 
|--
  “ ((dest + ((-1) * sizeof(UCHAR))) = (dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ”
  &&  “ ((src + ((-1) * sizeof(UCHAR))) = (src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))) ((dest + ((-1) * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((n_pre - (remaining - 1 ) )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))) ((dest + ((-1) * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((n_pre - (remaining - 1 ) )))))) ”
  &&  emp
).

Definition mm_copy_backward_entail_wit_2_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((dest + ((-1) * sizeof(UCHAR))) = (dest_pre + ((remaining - 1 ) * sizeof(UCHAR))))
.

Definition mm_copy_backward_entail_wit_2_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((src + ((-1) * sizeof(UCHAR))) = (src_pre + ((remaining - 1 ) * sizeof(UCHAR))))
.

Definition mm_copy_backward_entail_wit_2_split_goal_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b1) (n1) ((mm_write ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))) ((dest + ((-1) * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((n_pre - (remaining - 1 ) ))))))
.

Definition mm_copy_backward_entail_wit_2_split_goal_4 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b2) (n2) ((mm_write ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))) ((dest + ((-1) * sizeof(UCHAR)))) ((Some (retval)))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((dest_pre + ((remaining - 1 ) * sizeof(UCHAR)))) ((n_pre - (remaining - 1 ) ))))))
.

Definition mm_copy_backward_return_wit_1 :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= remaining)) (PreH3 : (remaining <= n_pre)) (PreH4 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (src_pre <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= remaining)) (PreH3 : (remaining <= n_pre)) (PreH4 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (src_pre <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  TT && emp 
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre))))) ”
  &&  emp
).

Definition mm_copy_backward_return_wit_1_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= remaining)) (PreH3 : (remaining <= n_pre)) (PreH4 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (src_pre <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b1) (n1) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))))
.

Definition mm_copy_backward_return_wit_1_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (remaining <= 0)) (PreH2 : (0 <= remaining)) (PreH3 : (remaining <= n_pre)) (PreH4 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (src_pre <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((mm_cells (b2) (n2) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))))
.

Definition mm_copy_backward_partial_solve_wit_1_pure :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (remaining > 0)) (PreH2 : (0 <= remaining)) (PreH3 : (remaining <= n_pre)) (PreH4 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (src_pre <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_initialized (mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src) (dest) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
  &&  “ (mm_in (src + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (remaining <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : (remaining >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= remaining)) (PreH7 : (remaining <= n_pre)) (PreH8 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (src_pre <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (mm_in (src + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src) (dest) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src) (dest) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
).

Definition mm_copy_backward_partial_solve_wit_1_pure_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (remaining <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : (remaining >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= remaining)) (PreH7 : (remaining <= n_pre)) (PreH8 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (src_pre <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (mm_in (src + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
.

Definition mm_copy_backward_partial_solve_wit_1_pure_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (remaining <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : (remaining >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= remaining)) (PreH7 : (remaining <= n_pre)) (PreH8 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (src_pre <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (mm_initialized (mm_snapshot (m) (src) (dest) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
.

Definition mm_copy_backward_partial_solve_wit_1_pure_split_goal_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (remaining <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : (remaining >= 0)) (PreH5 : (remaining > 0)) (PreH6 : (0 <= remaining)) (PreH7 : (remaining <= n_pre)) (PreH8 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH10 : (0 <= n1)) (PreH11 : (0 <= n2)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH16 : (src_pre <= dest_pre)) (PreH17 : (mm_separated b1 n1 b2 n2 )) (PreH18 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "remaining" ) )) # UInt64  |-> remaining)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> dest)
  **  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (mm_initialized (mm_snapshot (m) (src) (dest) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
.

Definition mm_copy_backward_partial_solve_wit_1_aux :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (PreH1 : (remaining > 0)) (PreH2 : (0 <= remaining)) (PreH3 : (remaining <= n_pre)) (PreH4 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH5 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH6 : (0 <= n1)) (PreH7 : (0 <= n2)) (PreH8 : (0 <= src_pre)) (PreH9 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : (0 <= dest_pre)) (PreH11 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : (src_pre <= dest_pre)) (PreH13 : (mm_separated b1 n1 b2 n2 )) (PreH14 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_initialized (mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
  &&  “ (mm_initialized (mm_snapshot (m) (src) (dest) ((n_pre - remaining ))) (src + ((-1) * sizeof(UCHAR))) ) ”
  &&  “ (mm_in (src + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
  &&  “ (remaining > 0) ”
  &&  “ (0 <= remaining) ”
  &&  “ (remaining <= n_pre) ”
  &&  “ (src = (src_pre + (remaining * sizeof(UCHAR)))) ”
  &&  “ (dest = (dest_pre + (remaining * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (src_pre <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
.

Definition mm_copy_backward_partial_solve_wit_1 := mm_copy_backward_partial_solve_wit_1_pure -> mm_copy_backward_partial_solve_wit_1_aux.

Definition mm_copy_backward_partial_solve_wit_2_pure :=
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> (dest + ((-1) * sizeof(UCHAR))))
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_in (dest + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
) \/
(
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : ((remaining - 1 ) <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : ((remaining - 1 ) >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= remaining)) (PreH10 : (remaining <= n_pre)) (PreH11 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH12 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH13 : (0 <= n1)) (PreH14 : (0 <= n2)) (PreH15 : (0 <= src_pre)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (0 <= dest_pre)) (PreH18 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH19 : (src_pre <= dest_pre)) (PreH20 : (mm_separated b1 n1 b2 n2 )) (PreH21 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> (dest + ((-1) * sizeof(UCHAR))))
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
  &&  “ (mm_in (dest + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
).

Definition mm_copy_backward_partial_solve_wit_2_pure_split_goal_1 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : ((remaining - 1 ) <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : ((remaining - 1 ) >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= remaining)) (PreH10 : (remaining <= n_pre)) (PreH11 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH12 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH13 : (0 <= n1)) (PreH14 : (0 <= n2)) (PreH15 : (0 <= src_pre)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (0 <= dest_pre)) (PreH18 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH19 : (src_pre <= dest_pre)) (PreH20 : (mm_separated b1 n1 b2 n2 )) (PreH21 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> (dest + ((-1) * sizeof(UCHAR))))
|--
  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
.

Definition mm_copy_backward_partial_solve_wit_2_pure_split_goal_2 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : ((remaining - 1 ) <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : ((remaining - 1 ) >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= remaining)) (PreH10 : (remaining <= n_pre)) (PreH11 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH12 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH13 : (0 <= n1)) (PreH14 : (0 <= n2)) (PreH15 : (0 <= src_pre)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (0 <= dest_pre)) (PreH18 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH19 : (src_pre <= dest_pre)) (PreH20 : (mm_separated b1 n1 b2 n2 )) (PreH21 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> (dest + ((-1) * sizeof(UCHAR))))
|--
  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
.

Definition mm_copy_backward_partial_solve_wit_2_pure_split_goal_3 :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : ((remaining - 1 ) <= UINT64_MAX)) (PreH3 : (n_pre >= 0)) (PreH4 : ((remaining - 1 ) >= 0)) (PreH5 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 255)) (PreH8 : (remaining > 0)) (PreH9 : (0 <= remaining)) (PreH10 : (remaining <= n_pre)) (PreH11 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH12 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH13 : (0 <= n1)) (PreH14 : (0 <= n2)) (PreH15 : (0 <= src_pre)) (PreH16 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH17 : (0 <= dest_pre)) (PreH18 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH19 : (src_pre <= dest_pre)) (PreH20 : (mm_separated b1 n1 b2 n2 )) (PreH21 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  ((( &( "x" ) )) # UChar  |-> retval)
  **  ((( &( "remaining" ) )) # UInt64  |-> (remaining - 1 ))
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> (src + ((-1) * sizeof(UCHAR))))
  **  ((( &( "dest" ) )) # Ptr  |-> (dest + ((-1) * sizeof(UCHAR))))
|--
  “ (mm_in (dest + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
.

Definition mm_copy_backward_partial_solve_wit_2_aux :=
forall (m: mm_memory) (n2: Z) (b2: Z) (n1: Z) (b1: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (dest: Z) (src: Z) (remaining: Z) (retval: Z) (PreH1 : ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 255)) (PreH4 : (remaining > 0)) (PreH5 : (0 <= remaining)) (PreH6 : (remaining <= n_pre)) (PreH7 : (src = (src_pre + (remaining * sizeof(UCHAR))))) (PreH8 : (dest = (dest_pre + (remaining * sizeof(UCHAR))))) (PreH9 : (0 <= n1)) (PreH10 : (0 <= n2)) (PreH11 : (0 <= src_pre)) (PreH12 : ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH13 : (0 <= dest_pre)) (PreH14 : ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX)) (PreH15 : (src_pre <= dest_pre)) (PreH16 : (mm_separated b1 n1 b2 n2 )) (PreH17 : (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 )),
  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining ))))) )
|--
  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_in (dest + ((-1) * sizeof(UCHAR))) b1 n1 b2 n2 ) ”
  &&  “ ((mm_cells (b1) (n1) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
  &&  “ ((mm_cells (b2) (n2) ((mm_snapshot (m) (src) (dest) ((n_pre - remaining ))))) = (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) )))))) ”
  &&  “ ((mm_lookup ((mm_snapshot (m) ((src_pre + (remaining * sizeof(UCHAR)))) ((dest_pre + (remaining * sizeof(UCHAR)))) ((n_pre - remaining )))) ((src + ((-1) * sizeof(UCHAR))))) = (Some (retval))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= 255) ”
  &&  “ (remaining > 0) ”
  &&  “ (0 <= remaining) ”
  &&  “ (remaining <= n_pre) ”
  &&  “ (src = (src_pre + (remaining * sizeof(UCHAR)))) ”
  &&  “ (dest = (dest_pre + (remaining * sizeof(UCHAR)))) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (src_pre <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) ))))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) ((src_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((dest_pre + (((remaining - 1 ) + 1 ) * sizeof(UCHAR)))) ((n_pre - ((remaining - 1 ) + 1 ) ))))) )
.

Definition mm_copy_backward_partial_solve_wit_2 := mm_copy_backward_partial_solve_wit_2_pure -> mm_copy_backward_partial_solve_wit_2_aux.

(* Shallow FunAssertion specs for mm_copy_forward. *)
Definition mm_copy_forward_sig : FuncSig := ([ * u8;  * u8; u64], void)%ctype.

Definition mm_copy_forward_default : Spec mm_copy_forward_sig :=
  fun F =>
ALL (b1: Z),
ALL (n1: Z),
ALL (b2: Z),
ALL (n2: Z),
ALL (m: mm_memory),
HoareFun ([ * u8;  * u8; u64], void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (dest_pre <= src_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) ))))
  (fun '(dest_pre, (src_pre, n_pre)) (_retval : unit) =>
  ((UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )))
  F.

Definition mm_copy_forward_direction_spec : Spec mm_copy_forward_sig :=
  fun F =>
ALL (b1: Z),
ALL (n1: Z),
ALL (b2: Z),
ALL (n2: Z),
ALL (m: mm_memory),
HoareFun ([ * u8;  * u8; u64], void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (mm_forward_ok src_pre dest_pre n_pre ) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )))
  (fun '(dest_pre, (src_pre, n_pre)) (_retval : unit) =>
  ((UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )))
  F.

Definition mm_copy_forward_default_entail_direction_spec :=
forall (dest_pre: Z) (src_pre: Z) (n_pre: Z) (b1_direction_spec: Z) (n1_direction_spec: Z) (b2_direction_spec: Z) (n2_direction_spec: Z) (m_direction_spec: mm_memory),
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_direction_spec) ”
  &&  “ (0 <= n2_direction_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (mm_forward_ok src_pre dest_pre n_pre ) ”
  &&  “ (mm_separated b1_direction_spec n1_direction_spec b2_direction_spec n2_direction_spec ) ”
  &&  “ (mm_access m_direction_spec src_pre dest_pre n_pre b1_direction_spec n1_direction_spec b2_direction_spec n2_direction_spec ) ”
  &&  (UCharArray.mixed_full b1_direction_spec n1_direction_spec (mm_cells (b1_direction_spec) (n1_direction_spec) (m_direction_spec)) )
  **  (UCharArray.mixed_full b2_direction_spec n2_direction_spec (mm_cells (b2_direction_spec) (n2_direction_spec) (m_direction_spec)) ))
|--
EX (b1: Z)(n1: Z)(b2: Z)(n2: Z)(m: mm_memory),
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (dest_pre <= src_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= dest_pre) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) )))
  **
  (  ((UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) ))
  -*
  ((UCharArray.mixed_full b1_direction_spec n1_direction_spec (mm_cells (b1_direction_spec) (n1_direction_spec) ((mm_snapshot (m_direction_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_direction_spec n2_direction_spec (mm_cells (b2_direction_spec) (n2_direction_spec) ((mm_snapshot (m_direction_spec) (src_pre) (dest_pre) (n_pre)))) )))
.

Module Type VC_Correct.


Axiom proof_of_mm_copy_forward_safety_wit_1 : mm_copy_forward_safety_wit_1.
Axiom proof_of_mm_copy_forward_safety_wit_2 : mm_copy_forward_safety_wit_2.
Axiom proof_of_mm_copy_forward_safety_wit_3 : mm_copy_forward_safety_wit_3.
Axiom proof_of_mm_copy_forward_safety_wit_4 : mm_copy_forward_safety_wit_4.
Axiom proof_of_mm_copy_forward_safety_wit_5 : mm_copy_forward_safety_wit_5.
Axiom proof_of_mm_copy_forward_safety_wit_6 : mm_copy_forward_safety_wit_6.
Axiom proof_of_mm_copy_forward_safety_wit_7 : mm_copy_forward_safety_wit_7.
Axiom proof_of_mm_copy_forward_safety_wit_8 : mm_copy_forward_safety_wit_8.
Axiom proof_of_mm_copy_forward_entail_wit_1_1 : mm_copy_forward_entail_wit_1_1.
Axiom proof_of_mm_copy_forward_entail_wit_1_2 : mm_copy_forward_entail_wit_1_2.
Axiom proof_of_mm_copy_forward_entail_wit_2_1 : mm_copy_forward_entail_wit_2_1.
Axiom proof_of_mm_copy_forward_entail_wit_2_2 : mm_copy_forward_entail_wit_2_2.
Axiom proof_of_mm_copy_forward_return_wit_1 : mm_copy_forward_return_wit_1.
Axiom proof_of_mm_copy_forward_return_wit_2 : mm_copy_forward_return_wit_2.
Axiom proof_of_mm_copy_forward_partial_solve_wit_1_pure : mm_copy_forward_partial_solve_wit_1_pure.
Axiom proof_of_mm_copy_forward_partial_solve_wit_1 : mm_copy_forward_partial_solve_wit_1.
Axiom proof_of_mm_copy_forward_partial_solve_wit_2_pure : mm_copy_forward_partial_solve_wit_2_pure.
Axiom proof_of_mm_copy_forward_partial_solve_wit_2 : mm_copy_forward_partial_solve_wit_2.
Axiom proof_of_mm_copy_forward_partial_solve_wit_3_pure : mm_copy_forward_partial_solve_wit_3_pure.
Axiom proof_of_mm_copy_forward_partial_solve_wit_3 : mm_copy_forward_partial_solve_wit_3.
Axiom proof_of_mm_copy_forward_partial_solve_wit_4_pure : mm_copy_forward_partial_solve_wit_4_pure.
Axiom proof_of_mm_copy_forward_partial_solve_wit_4 : mm_copy_forward_partial_solve_wit_4.
Axiom proof_of_mm_copy_backward_safety_wit_1 : mm_copy_backward_safety_wit_1.
Axiom proof_of_mm_copy_backward_safety_wit_2 : mm_copy_backward_safety_wit_2.
Axiom proof_of_mm_copy_backward_safety_wit_3 : mm_copy_backward_safety_wit_3.
Axiom proof_of_mm_copy_backward_safety_wit_4 : mm_copy_backward_safety_wit_4.
Axiom proof_of_mm_copy_backward_entail_wit_1 : mm_copy_backward_entail_wit_1.
Axiom proof_of_mm_copy_backward_entail_wit_2 : mm_copy_backward_entail_wit_2.
Axiom proof_of_mm_copy_backward_return_wit_1 : mm_copy_backward_return_wit_1.
Axiom proof_of_mm_copy_backward_partial_solve_wit_1_pure : mm_copy_backward_partial_solve_wit_1_pure.
Axiom proof_of_mm_copy_backward_partial_solve_wit_1 : mm_copy_backward_partial_solve_wit_1.
Axiom proof_of_mm_copy_backward_partial_solve_wit_2_pure : mm_copy_backward_partial_solve_wit_2_pure.
Axiom proof_of_mm_copy_backward_partial_solve_wit_2 : mm_copy_backward_partial_solve_wit_2.
Axiom proof_of_mm_copy_forward_default_entail_direction_spec : mm_copy_forward_default_entail_direction_spec.

End VC_Correct.
