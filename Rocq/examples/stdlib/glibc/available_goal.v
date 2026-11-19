From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.two_way_dynamic_lib.
Local Open Scope sac.

(*----- Function available -----*)

Definition available_safety_wit_1 :=
forall (known: Z) (total: Z) (bytes: (@list Z)) (h_pre: Z) (h_l_pre: Z) (j_pre: Z) (n_l_pre: Z) (PreH1 : ((j_pre + n_l_pre ) <= known)) (PreH2 : (0 <= known)) (PreH3 : (known <= total)) (PreH4 : (total <= INT_MAX)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre <= known)) (PreH7 : (0 < n_l_pre)) (PreH8 : (n_l_pre <= INT_MAX)) (PreH9 : (tw_nonzero_bytes bytes )),
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "h_l" ) )) # Ptr  |-> h_l_pre)
  **  ((( &( "j" ) )) # UInt64  |-> j_pre)
  **  ((( &( "n_l" ) )) # UInt64  |-> n_l_pre)
  **  ((h_l_pre) # UInt64  |-> known)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition available_safety_wit_2 :=
forall (known: Z) (total: Z) (bytes: (@list Z)) (h_pre: Z) (h_l_pre: Z) (j_pre: Z) (n_l_pre: Z) (PreH1 : ((j_pre + n_l_pre ) > known)) (PreH2 : (0 <= known)) (PreH3 : (known <= total)) (PreH4 : (total <= INT_MAX)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre <= known)) (PreH7 : (0 < n_l_pre)) (PreH8 : (n_l_pre <= INT_MAX)) (PreH9 : (tw_nonzero_bytes bytes )),
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "h_l" ) )) # Ptr  |-> h_l_pre)
  **  ((( &( "j" ) )) # UInt64  |-> j_pre)
  **  ((( &( "n_l" ) )) # UInt64  |-> n_l_pre)
  **  ((h_l_pre) # UInt64  |-> known)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
|--
  “ (512 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 512) ”
.

Definition available_return_wit_1 :=
forall (known: Z) (total: Z) (bytes: (@list Z)) (h_pre: Z) (h_l_pre: Z) (j_pre: Z) (n_l_pre: Z) (retval: Z) (PreH1 : ((j_pre + n_l_pre ) > (known + retval ))) (PreH2 : (tw_probe_result total known (n_l_pre + 512 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= (n_l_pre + 512 ))) (PreH5 : ((known + retval ) <= total)) (PreH6 : ((retval < (n_l_pre + 512 )) -> ((known + retval ) = total))) (PreH7 : ((j_pre + n_l_pre ) > known)) (PreH8 : (0 <= known)) (PreH9 : (known <= total)) (PreH10 : (total <= INT_MAX)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre <= known)) (PreH13 : (0 < n_l_pre)) (PreH14 : (n_l_pre <= INT_MAX)) (PreH15 : (tw_nonzero_bytes bytes )),
  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
  **  ((h_l_pre) # UInt64  |-> (known + retval ))
|--
  EX (next: Z),
  “ (known <= next) ”
  &&  “ (next <= total) ”
  &&  “ (0 = 0) ”
  &&  “ (next = total) ”
  &&  “ (total < (j_pre + n_l_pre )) ”
  &&  ((h_l_pre) # UInt64  |-> next)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
.

Definition available_return_wit_2 :=
forall (known: Z) (total: Z) (bytes: (@list Z)) (h_pre: Z) (h_l_pre: Z) (j_pre: Z) (n_l_pre: Z) (retval: Z) (PreH1 : ((j_pre + n_l_pre ) <= (known + retval ))) (PreH2 : (tw_probe_result total known (n_l_pre + 512 ) retval )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= (n_l_pre + 512 ))) (PreH5 : ((known + retval ) <= total)) (PreH6 : ((retval < (n_l_pre + 512 )) -> ((known + retval ) = total))) (PreH7 : ((j_pre + n_l_pre ) > known)) (PreH8 : (0 <= known)) (PreH9 : (known <= total)) (PreH10 : (total <= INT_MAX)) (PreH11 : (0 <= j_pre)) (PreH12 : (j_pre <= known)) (PreH13 : (0 < n_l_pre)) (PreH14 : (n_l_pre <= INT_MAX)) (PreH15 : (tw_nonzero_bytes bytes )),
  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
  **  ((h_l_pre) # UInt64  |-> (known + retval ))
|--
  EX (next: Z),
  “ (known <= next) ”
  &&  “ (next <= total) ”
  &&  “ (1 = 1) ”
  &&  “ ((j_pre + n_l_pre ) <= next) ”
  &&  ((h_l_pre) # UInt64  |-> next)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
.

Definition available_return_wit_3 :=
forall (known: Z) (total: Z) (bytes: (@list Z)) (h_pre: Z) (h_l_pre: Z) (j_pre: Z) (n_l_pre: Z) (PreH1 : ((j_pre + n_l_pre ) <= known)) (PreH2 : (0 <= known)) (PreH3 : (known <= total)) (PreH4 : (total <= INT_MAX)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre <= known)) (PreH7 : (0 < n_l_pre)) (PreH8 : (n_l_pre <= INT_MAX)) (PreH9 : (tw_nonzero_bytes bytes )),
  ((h_l_pre) # UInt64  |-> known)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
|--
  EX (next: Z),
  “ (known <= next) ”
  &&  “ (next <= total) ”
  &&  “ (1 = 1) ”
  &&  “ ((j_pre + n_l_pre ) <= next) ”
  &&  ((h_l_pre) # UInt64  |-> next)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
.

Definition available_partial_solve_wit_1_pure :=
forall (known: Z) (total: Z) (bytes: (@list Z)) (h_pre: Z) (h_l_pre: Z) (j_pre: Z) (n_l_pre: Z) (PreH1 : ((j_pre + n_l_pre ) > known)) (PreH2 : (0 <= known)) (PreH3 : (known <= total)) (PreH4 : (total <= INT_MAX)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre <= known)) (PreH7 : (0 < n_l_pre)) (PreH8 : (n_l_pre <= INT_MAX)) (PreH9 : (tw_nonzero_bytes bytes )),
  ((( &( "h" ) )) # Ptr  |-> h_pre)
  **  ((( &( "h_l" ) )) # Ptr  |-> h_l_pre)
  **  ((( &( "j" ) )) # UInt64  |-> j_pre)
  **  ((( &( "n_l" ) )) # UInt64  |-> n_l_pre)
  **  ((h_l_pre) # UInt64  |-> known)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
|--
  “ ((h_pre + (known * sizeof(UCHAR))) = (h_pre + known )) ”
  &&  “ (0 <= known) ”
  &&  “ (known <= total) ”
  &&  “ (total <= INT_MAX) ”
  &&  “ (0 <= (n_l_pre + 512 )) ”
  &&  “ ((n_l_pre + 512 ) <= UINT64_MAX) ”
  &&  “ (tw_nonzero_bytes bytes ) ”
.

Definition available_partial_solve_wit_1_aux :=
forall (known: Z) (total: Z) (bytes: (@list Z)) (h_pre: Z) (h_l_pre: Z) (j_pre: Z) (n_l_pre: Z) (PreH1 : ((j_pre + n_l_pre ) > known)) (PreH2 : (0 <= known)) (PreH3 : (known <= total)) (PreH4 : (total <= INT_MAX)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre <= known)) (PreH7 : (0 < n_l_pre)) (PreH8 : (n_l_pre <= INT_MAX)) (PreH9 : (tw_nonzero_bytes bytes )),
  ((h_l_pre) # UInt64  |-> known)
  **  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
|--
  “ ((h_pre + (known * sizeof(UCHAR))) = (h_pre + known )) ”
  &&  “ (0 <= known) ”
  &&  “ (known <= total) ”
  &&  “ (total <= INT_MAX) ”
  &&  “ (0 <= (n_l_pre + 512 )) ”
  &&  “ ((n_l_pre + 512 ) <= UINT64_MAX) ”
  &&  “ (tw_nonzero_bytes bytes ) ”
  &&  “ ((j_pre + n_l_pre ) > known) ”
  &&  “ (0 <= known) ”
  &&  “ (known <= total) ”
  &&  “ (total <= INT_MAX) ”
  &&  “ (0 <= j_pre) ”
  &&  “ (j_pre <= known) ”
  &&  “ (0 < n_l_pre) ”
  &&  “ (n_l_pre <= INT_MAX) ”
  &&  “ (tw_nonzero_bytes bytes ) ”
  &&  (UCharArray.full h_pre total bytes )
  **  (tw_terminator h_pre total )
  **  ((h_l_pre) # UInt64  |-> known)
.

Definition available_partial_solve_wit_1 := available_partial_solve_wit_1_pure -> available_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_available_safety_wit_1 : available_safety_wit_1.
Axiom proof_of_available_safety_wit_2 : available_safety_wit_2.
Axiom proof_of_available_return_wit_1 : available_return_wit_1.
Axiom proof_of_available_return_wit_2 : available_return_wit_2.
Axiom proof_of_available_return_wit_3 : available_return_wit_3.
Axiom proof_of_available_partial_solve_wit_1_pure : available_partial_solve_wit_1_pure.
Axiom proof_of_available_partial_solve_wit_1 : available_partial_solve_wit_1.

End VC_Correct.
