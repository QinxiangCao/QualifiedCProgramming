/* Coq predicates of the vectors of vec_qcp.h (vec_qcp_lib.v): Veci holds int elements, Vecp pointers.
   Included by vec_qcp.h and by vec_qcp.strategies; it mentions nothing of the solver. */
#ifndef vec_qcp_def_h
#define vec_qcp_def_h

/*@ Import Coq Require Import SimpleC.EE.Applications_human.minisat.vec_qcp_lib */

/*@ Extern Coq
      (vec_buf_ok : Z -> Z -> Prop)
      (UndefStructPredveci_t : Z -> Assertion)
      (UndefStructPredvecp_t : Z -> Assertion)
      (Veci::shell : Z -> Assertion)
      (Veci::rep : Z -> list Z -> Assertion)
      (Veci::rep_ptr : Z -> Z -> list Z -> Assertion)
      (Veci::header : Z -> Z -> Z -> Z -> Assertion)
      (Vecp::shell : Z -> Assertion)
      (Vecp::rep : Z -> list Z -> Assertion)
      (Vecp::rep_ptr : Z -> Z -> list Z -> Assertion)
      (Vecp::header : Z -> Z -> Z -> Z -> Assertion)
      (Vecp::slot : Z -> Z -> Z)
      (VecpArray::full : Z -> Z -> list (list Z) -> Assertion)
      (VecpArray::missing_i : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (VecpArray::missing2 : Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (VecpArray::undef_seg : Z -> Z -> Z -> Assertion)
      (In : {A} -> A -> list A -> Prop)
      (first_occurrence : {A} -> A -> list A -> Z -> Prop)
      (remove_nth : {A} -> Z -> list A -> list A)
      (vecp_remove_scan_inv : Z -> list Z -> Z -> Prop)
      (vecp_remove_shift_inv : Z -> list Z -> Z -> Z -> list Z -> Prop)
 */

#endif
