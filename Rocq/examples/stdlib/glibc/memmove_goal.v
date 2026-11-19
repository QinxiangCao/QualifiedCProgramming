From SimpleC.Verification Require Import VCPrelude.
Import Snaive_C_Rules64.
Require Import SimpleC.EE.stdlib.glibc.memmove_lib.
Require Import SimpleC.EE.stdlib.glibc.memmove_contract_lib.
Local Open Scope sac.

(*----- Function memmove -----*)

Definition memmove_safety_wit_1 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1_byte_memory_spec)) (PreH3 : (0 <= n2_byte_memory_spec)) (PreH4 : (n_pre = 0)) (PreH5 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH6 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_2 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= n1_byte_memory_spec)) (PreH3 : (0 <= n2_byte_memory_spec)) (PreH4 : (0 <= src_pre)) (PreH5 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH6 : (0 <= dest_pre)) (PreH7 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH8 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH9 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memmove_safety_wit_3 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (n_pre = 0)) (PreH6 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH7 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ False ”
.

Definition memmove_return_wit_1 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) >= n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= n1_byte_memory_spec)) (PreH5 : (0 <= n2_byte_memory_spec)) (PreH6 : (0 <= src_pre)) (PreH7 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH8 : (0 <= dest_pre)) (PreH9 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH10 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH11 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
|--
  “ (dest_pre = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
.

Definition memmove_return_wit_2 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) < n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= n1_byte_memory_spec)) (PreH5 : (0 <= n2_byte_memory_spec)) (PreH6 : (0 <= src_pre)) (PreH7 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH8 : (0 <= dest_pre)) (PreH9 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH10 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH11 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
|--
  “ (dest_pre = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
.

Definition memmove_return_wit_3 :=
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (n_pre = 0)) (PreH6 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH7 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (dest_pre = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
) \/
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (n_pre = 0)) (PreH6 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH7 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  TT && emp 
|--
  “ ((mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0))))) ”
  &&  “ ((mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0))))) ”
  &&  emp
).

Definition memmove_return_wit_3_split_goal_1 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (n_pre = 0)) (PreH6 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH7 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0)))))
.

Definition memmove_return_wit_3_split_goal_2 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (n_pre = 0)) (PreH6 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH7 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0)))))
.

Definition memmove_return_wit_4 :=
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (0 <= src_pre)) (PreH6 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH7 : (0 <= dest_pre)) (PreH8 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH9 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH10 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (dest_pre = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
) \/
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (0 <= src_pre)) (PreH6 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH7 : (0 <= dest_pre)) (PreH8 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH9 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH10 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  TT && emp 
|--
  “ ((mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0))))) ”
  &&  “ ((mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0))))) ”
  &&  emp
).

Definition memmove_return_wit_4_split_goal_1 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (0 <= src_pre)) (PreH6 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH7 : (0 <= dest_pre)) (PreH8 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH9 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH10 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0)))))
.

Definition memmove_return_wit_4_split_goal_2 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= n1_byte_memory_spec)) (PreH4 : (0 <= n2_byte_memory_spec)) (PreH5 : (0 <= src_pre)) (PreH6 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH7 : (0 <= dest_pre)) (PreH8 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH9 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH10 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) = (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (0)))))
.

Definition memmove_partial_solve_wit_1_pure :=
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) >= n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= n1_byte_memory_spec)) (PreH5 : (0 <= n2_byte_memory_spec)) (PreH6 : (0 <= src_pre)) (PreH7 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH8 : (0 <= dest_pre)) (PreH9 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH10 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH11 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "srcp" ) )) # UInt64  |-> src_pre)
  **  ((( &( "dstp" ) )) # UInt64  |-> dest_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_forward_ok src_pre dest_pre n_pre ) ”
) \/
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (dest_pre <= UINT64_MAX)) (PreH3 : (src_pre <= UINT64_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (dest_pre >= 0)) (PreH6 : (src_pre >= 0)) (PreH7 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) >= n_pre)) (PreH8 : (n_pre <> 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= n1_byte_memory_spec)) (PreH11 : (0 <= n2_byte_memory_spec)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH16 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH17 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "srcp" ) )) # UInt64  |-> src_pre)
  **  ((( &( "dstp" ) )) # UInt64  |-> dest_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (mm_forward_ok src_pre dest_pre n_pre ) ”
).

Definition memmove_partial_solve_wit_1_pure_split_goal_1 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (dest_pre <= UINT64_MAX)) (PreH3 : (src_pre <= UINT64_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (dest_pre >= 0)) (PreH6 : (src_pre >= 0)) (PreH7 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) >= n_pre)) (PreH8 : (n_pre <> 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= n1_byte_memory_spec)) (PreH11 : (0 <= n2_byte_memory_spec)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH16 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH17 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "srcp" ) )) # UInt64  |-> src_pre)
  **  ((( &( "dstp" ) )) # UInt64  |-> dest_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (mm_forward_ok src_pre dest_pre n_pre ) ”
.

Definition memmove_partial_solve_wit_1_aux :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) >= n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= n1_byte_memory_spec)) (PreH5 : (0 <= n2_byte_memory_spec)) (PreH6 : (0 <= src_pre)) (PreH7 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH8 : (0 <= dest_pre)) (PreH9 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH10 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH11 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_forward_ok src_pre dest_pre n_pre ) ”
  &&  “ ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) >= n_pre) ”
  &&  “ (n_pre <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
.

Definition memmove_partial_solve_wit_1 := memmove_partial_solve_wit_1_pure -> memmove_partial_solve_wit_1_aux.

Definition memmove_partial_solve_wit_2_pure :=
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) < n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= n1_byte_memory_spec)) (PreH5 : (0 <= n2_byte_memory_spec)) (PreH6 : (0 <= src_pre)) (PreH7 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH8 : (0 <= dest_pre)) (PreH9 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH10 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH11 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "srcp" ) )) # UInt64  |-> src_pre)
  **  ((( &( "dstp" ) )) # UInt64  |-> dest_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (src_pre <= dest_pre) ”
) \/
(
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (dest_pre <= UINT64_MAX)) (PreH3 : (src_pre <= UINT64_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (dest_pre >= 0)) (PreH6 : (src_pre >= 0)) (PreH7 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) < n_pre)) (PreH8 : (n_pre <> 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= n1_byte_memory_spec)) (PreH11 : (0 <= n2_byte_memory_spec)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH16 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH17 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "srcp" ) )) # UInt64  |-> src_pre)
  **  ((( &( "dstp" ) )) # UInt64  |-> dest_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (src_pre <= dest_pre) ”
).

Definition memmove_partial_solve_wit_2_pure_split_goal_1 :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= UINT64_MAX)) (PreH2 : (dest_pre <= UINT64_MAX)) (PreH3 : (src_pre <= UINT64_MAX)) (PreH4 : (n_pre >= 0)) (PreH5 : (dest_pre >= 0)) (PreH6 : (src_pre >= 0)) (PreH7 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) < n_pre)) (PreH8 : (n_pre <> 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= n1_byte_memory_spec)) (PreH11 : (0 <= n2_byte_memory_spec)) (PreH12 : (0 <= src_pre)) (PreH13 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH14 : (0 <= dest_pre)) (PreH15 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH16 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH17 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  ((( &( "srcp" ) )) # UInt64  |-> src_pre)
  **  ((( &( "dstp" ) )) # UInt64  |-> dest_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # UInt64  |-> n_pre)
  **  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (src_pre <= dest_pre) ”
.

Definition memmove_partial_solve_wit_2_aux :=
forall (m_byte_memory_spec: mm_memory) (n2_byte_memory_spec: Z) (b2_byte_memory_spec: Z) (n1_byte_memory_spec: Z) (b1_byte_memory_spec: Z) (dest_pre: Z) (src_pre: Z) (n_pre: Z) (PreH1 : ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) < n_pre)) (PreH2 : (n_pre <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= n1_byte_memory_spec)) (PreH5 : (0 <= n2_byte_memory_spec)) (PreH6 : (0 <= src_pre)) (PreH7 : ((src_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH8 : (0 <= dest_pre)) (PreH9 : ((dest_pre + (n_pre * 1)) <= UINT64_MAX)) (PreH10 : (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )) (PreH11 : (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec )),
  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
|--
  “ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (src_pre <= dest_pre) ”
  &&  “ ((unsigned_last_nbits ((dest_pre - src_pre )) (64)) < n_pre) ”
  &&  “ (n_pre <> 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )
.

Definition memmove_partial_solve_wit_2 := memmove_partial_solve_wit_2_pure -> memmove_partial_solve_wit_2_aux.

(* Shallow FunAssertion specs for memmove. *)
Definition memmove_sig : FuncSig := ([ * void;  * void; u64],  * void)%ctype.

Definition memmove_byte_memory_spec : Spec memmove_sig :=
  fun F =>
ALL (b1: Z),
ALL (n1: Z),
ALL (b2: Z),
ALL (n2: Z),
ALL (m: mm_memory),
HoareFun ([ * void;  * void; u64],  * void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (n_pre = 0) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1) ”
  &&  “ (0 <= n2) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1 n1 b2 n2 ) ”
  &&  “ (mm_access m src_pre dest_pre n_pre b1 n1 b2 n2 ) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) (m)) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) (m)) ))))
  (fun '(dest_pre, (src_pre, n_pre)) retval =>
  (“ (retval = dest_pre) ”
  &&  (UCharArray.mixed_full b1 n1 (mm_cells (b1) (n1) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2 n2 (mm_cells (b2) (n2) ((mm_snapshot (m) (src_pre) (dest_pre) (n_pre)))) )))
  F.

Definition memmove_empty_copy : Spec memmove_sig :=
  fun F =>
HoareFun ([ * void;  * void; u64],  * void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
  (“ (n_pre = 0) ”
  &&  emp))
  (fun '(dest_pre, (src_pre, n_pre)) retval =>
  (“ (retval = dest_pre) ”
  &&  emp))
  F.

Definition memmove_same_range : Spec memmove_sig :=
  fun F =>
ALL (xs: (@list Z)),
HoareFun ([ * void;  * void; u64],  * void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
  (“ (0 <= n_pre) ”
  &&  “ ((Zlength (xs)) = n_pre) ”
  &&  “ (dest_pre = src_pre) ”
  &&  “ (0 <= src_pre) ”
  &&  “ (src_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.full src_pre n_pre xs )))
  (fun '(dest_pre, (src_pre, n_pre)) retval =>
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full src_pre n_pre xs )))
  F.

Definition memmove_right_overlap : Spec memmove_sig :=
  fun F =>
ALL (xs: (@list Z)),
ALL (h: Z),
HoareFun ([ * void;  * void; u64],  * void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
  (“ ((Zlength (xs)) = n_pre) ”
  &&  “ (0 < h) ”
  &&  “ (h < n_pre) ”
  &&  “ (dest_pre = (src_pre + (h * sizeof(UCHAR)))) ”
  &&  “ (0 <= src_pre) ”
  &&  “ (dest_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.full src_pre n_pre xs )
  **  (UCharArray.undef_full (src_pre + (n_pre * sizeof(UCHAR))) h )))
  (fun '(dest_pre, (src_pre, n_pre)) retval =>
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full src_pre h (sublist (0) (h) (xs)) )
  **  (UCharArray.full dest_pre n_pre xs )))
  F.

Definition memmove_left_overlap : Spec memmove_sig :=
  fun F =>
ALL (xs: (@list Z)),
ALL (h: Z),
HoareFun ([ * void;  * void; u64],  * void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
  (“ ((Zlength (xs)) = n_pre) ”
  &&  “ (0 < h) ”
  &&  “ (h < n_pre) ”
  &&  “ (src_pre = (dest_pre + (h * sizeof(UCHAR)))) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ (src_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.undef_full dest_pre h )
  **  (UCharArray.full src_pre n_pre xs )))
  (fun '(dest_pre, (src_pre, n_pre)) retval =>
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full dest_pre n_pre xs )
  **  (UCharArray.full (dest_pre + (n_pre * sizeof(UCHAR))) h (sublist ((n_pre - h )) (n_pre) (xs)) )))
  F.

Definition memmove_separated : Spec memmove_sig :=
  fun F =>
ALL (xs: (@list Z)),
HoareFun ([ * void;  * void; u64],  * void)%ctype
  (fun '(dest_pre, (src_pre, n_pre)) =>
  (“ (0 <= n_pre) ”
  &&  “ ((Zlength (xs)) = n_pre) ”
  &&  “ (0 <= src_pre) ”
  &&  “ (src_pre <= (UINT64_MAX - n_pre )) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ (dest_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.full src_pre n_pre xs )
  **  (UCharArray.undef_full dest_pre n_pre )))
  (fun '(dest_pre, (src_pre, n_pre)) retval =>
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full src_pre n_pre xs )
  **  (UCharArray.full dest_pre n_pre xs )))
  F.

Definition memmove_byte_memory_spec_entail_empty_copy :=
forall (dest_pre: Z) (src_pre: Z) (n_pre: Z),
  (“ (n_pre = 0) ”
  &&  emp)
|--
EX (b1_byte_memory_spec: Z)(n1_byte_memory_spec: Z)(b2_byte_memory_spec: Z)(n2_byte_memory_spec: Z)(m_byte_memory_spec: mm_memory),
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (n_pre = 0) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )))
  **
  (ALL (retval: Z),
  (“ (retval = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) ))
  -*
  (“ (retval = dest_pre) ”
  &&  emp))
.

Definition memmove_byte_memory_spec_entail_same_range :=
forall (dest_pre: Z) (src_pre: Z) (n_pre: Z) (xs_same_range: (@list Z)),
  (“ (0 <= n_pre) ”
  &&  “ ((Zlength (xs_same_range)) = n_pre) ”
  &&  “ (dest_pre = src_pre) ”
  &&  “ (0 <= src_pre) ”
  &&  “ (src_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.full src_pre n_pre xs_same_range ))
|--
EX (b1_byte_memory_spec: Z)(n1_byte_memory_spec: Z)(b2_byte_memory_spec: Z)(n2_byte_memory_spec: Z)(m_byte_memory_spec: mm_memory),
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (n_pre = 0) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )))
  **
  (ALL (retval: Z),
  (“ (retval = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) ))
  -*
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full src_pre n_pre xs_same_range )))
.

Definition memmove_byte_memory_spec_entail_right_overlap :=
forall (dest_pre: Z) (src_pre: Z) (n_pre: Z) (xs_right_overlap: (@list Z)) (h_right_overlap: Z),
  (“ ((Zlength (xs_right_overlap)) = n_pre) ”
  &&  “ (0 < h_right_overlap) ”
  &&  “ (h_right_overlap < n_pre) ”
  &&  “ (dest_pre = (src_pre + (h_right_overlap * sizeof(UCHAR)))) ”
  &&  “ (0 <= src_pre) ”
  &&  “ (dest_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.full src_pre n_pre xs_right_overlap )
  **  (UCharArray.undef_full (src_pre + (n_pre * sizeof(UCHAR))) h_right_overlap ))
|--
EX (b1_byte_memory_spec: Z)(n1_byte_memory_spec: Z)(b2_byte_memory_spec: Z)(n2_byte_memory_spec: Z)(m_byte_memory_spec: mm_memory),
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (n_pre = 0) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )))
  **
  (ALL (retval: Z),
  (“ (retval = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) ))
  -*
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full src_pre h_right_overlap (sublist (0) (h_right_overlap) (xs_right_overlap)) )
  **  (UCharArray.full dest_pre n_pre xs_right_overlap )))
.

Definition memmove_byte_memory_spec_entail_left_overlap :=
forall (dest_pre: Z) (src_pre: Z) (n_pre: Z) (xs_left_overlap: (@list Z)) (h_left_overlap: Z),
  (“ ((Zlength (xs_left_overlap)) = n_pre) ”
  &&  “ (0 < h_left_overlap) ”
  &&  “ (h_left_overlap < n_pre) ”
  &&  “ (src_pre = (dest_pre + (h_left_overlap * sizeof(UCHAR)))) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ (src_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.undef_full dest_pre h_left_overlap )
  **  (UCharArray.full src_pre n_pre xs_left_overlap ))
|--
EX (b1_byte_memory_spec: Z)(n1_byte_memory_spec: Z)(b2_byte_memory_spec: Z)(n2_byte_memory_spec: Z)(m_byte_memory_spec: mm_memory),
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (n_pre = 0) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )))
  **
  (ALL (retval: Z),
  (“ (retval = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) ))
  -*
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full dest_pre n_pre xs_left_overlap )
  **  (UCharArray.full (dest_pre + (n_pre * sizeof(UCHAR))) h_left_overlap (sublist ((n_pre - h_left_overlap )) (n_pre) (xs_left_overlap)) )))
.

Definition memmove_byte_memory_spec_entail_separated :=
forall (dest_pre: Z) (src_pre: Z) (n_pre: Z) (xs_separated: (@list Z)),
  (“ (0 <= n_pre) ”
  &&  “ ((Zlength (xs_separated)) = n_pre) ”
  &&  “ (0 <= src_pre) ”
  &&  “ (src_pre <= (UINT64_MAX - n_pre )) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ (dest_pre <= (UINT64_MAX - n_pre )) ”
  &&  (UCharArray.full src_pre n_pre xs_separated )
  **  (UCharArray.undef_full dest_pre n_pre ))
|--
EX (b1_byte_memory_spec: Z)(n1_byte_memory_spec: Z)(b2_byte_memory_spec: Z)(n2_byte_memory_spec: Z)(m_byte_memory_spec: mm_memory),
(orp
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (n_pre = 0) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) ))
  (“ (0 <= n_pre) ”
  &&  “ (0 <= n1_byte_memory_spec) ”
  &&  “ (0 <= n2_byte_memory_spec) ”
  &&  “ (0 <= src_pre) ”
  &&  “ ((src_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (0 <= dest_pre) ”
  &&  “ ((dest_pre + (n_pre * 1)) <= UINT64_MAX) ”
  &&  “ (mm_separated b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  “ (mm_access m_byte_memory_spec src_pre dest_pre n_pre b1_byte_memory_spec n1_byte_memory_spec b2_byte_memory_spec n2_byte_memory_spec ) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) (m_byte_memory_spec)) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) (m_byte_memory_spec)) )))
  **
  (ALL (retval: Z),
  (“ (retval = dest_pre) ”
  &&  (UCharArray.mixed_full b1_byte_memory_spec n1_byte_memory_spec (mm_cells (b1_byte_memory_spec) (n1_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) )
  **  (UCharArray.mixed_full b2_byte_memory_spec n2_byte_memory_spec (mm_cells (b2_byte_memory_spec) (n2_byte_memory_spec) ((mm_snapshot (m_byte_memory_spec) (src_pre) (dest_pre) (n_pre)))) ))
  -*
  (“ (retval = dest_pre) ”
  &&  (UCharArray.full src_pre n_pre xs_separated )
  **  (UCharArray.full dest_pre n_pre xs_separated )))
.

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


Axiom proof_of_memmove_safety_wit_1 : memmove_safety_wit_1.
Axiom proof_of_memmove_safety_wit_2 : memmove_safety_wit_2.
Axiom proof_of_memmove_safety_wit_3 : memmove_safety_wit_3.
Axiom proof_of_memmove_return_wit_1 : memmove_return_wit_1.
Axiom proof_of_memmove_return_wit_2 : memmove_return_wit_2.
Axiom proof_of_memmove_return_wit_3 : memmove_return_wit_3.
Axiom proof_of_memmove_return_wit_4 : memmove_return_wit_4.
Axiom proof_of_memmove_partial_solve_wit_1_pure : memmove_partial_solve_wit_1_pure.
Axiom proof_of_memmove_partial_solve_wit_1 : memmove_partial_solve_wit_1.
Axiom proof_of_memmove_partial_solve_wit_2_pure : memmove_partial_solve_wit_2_pure.
Axiom proof_of_memmove_partial_solve_wit_2 : memmove_partial_solve_wit_2.
Axiom proof_of_memmove_byte_memory_spec_entail_empty_copy : memmove_byte_memory_spec_entail_empty_copy.
Axiom proof_of_memmove_byte_memory_spec_entail_same_range : memmove_byte_memory_spec_entail_same_range.
Axiom proof_of_memmove_byte_memory_spec_entail_right_overlap : memmove_byte_memory_spec_entail_right_overlap.
Axiom proof_of_memmove_byte_memory_spec_entail_left_overlap : memmove_byte_memory_spec_entail_left_overlap.
Axiom proof_of_memmove_byte_memory_spec_entail_separated : memmove_byte_memory_spec_entail_separated.
Axiom proof_of_mm_copy_forward_default_entail_direction_spec : mm_copy_forward_default_entail_direction_spec.

End VC_Correct.
