Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_neg -----*)

Definition mpz_neg_safety_wit_1_eq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (rop_pre = op_pre)) (PreH2 : (same_sign z_eq size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <> (INT_MIN)) ”
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (rop_pre = op_pre)) (PreH2 : (same_sign z_eq size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <> (INT_MIN)) ”
).

Definition mpz_neg_safety_wit_1_eq_split_goal_1 := 
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (rop_pre = op_pre)) (PreH2 : (same_sign z_eq size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <> (INT_MIN)) ”
.

Definition mpz_neg_safety_wit_2_neq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg optr (Zabs (osize)) ocap )
|--
  “ (rsize <> (INT_MIN)) ”
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg optr (Zabs (osize)) ocap )
|--
  “ (rsize <> (INT_MIN)) ”
).

Definition mpz_neg_safety_wit_2_neq_split_goal_1 := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg optr (Zabs (osize)) ocap )
|--
  “ (rsize <> (INT_MIN)) ”
.

Definition mpz_neg_entail_wit_1_eq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (PreH1 : (rop_pre = op_pre)) (PreH2 : (rop_pre = op_pre)) ,
  (store_Z op_pre z_eq )
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (rop_pre = op_pre) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (PreH1 : (rop_pre = op_pre)) (PreH2 : (rop_pre = op_pre)) ,
  (store_Z op_pre z_eq )
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (rop_pre = op_pre) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
).

Definition mpz_neg_entail_wit_2_neq := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) ,
  (store_Z rop_pre z_neq )
  **  (store_Z op_pre z_neq )
|--
  EX (optr: Z)  (rptr: Z)  (ocap: Z)  (osize: Z)  (rcap: Z)  (rsize: Z) ,
  “ (same_sign z_neq rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign z_neq osize ) ” 
  &&  “ ((Zabs (osize)) <= ocap) ”
  &&  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg optr (Zabs (osize)) ocap )
.

Definition mpz_neg_return_wit_1_eq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (rop_pre = op_pre)) (PreH2 : (same_sign z_eq size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-size))
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (rop_pre = op_pre) ”
  &&  (store_Z op_pre (-z_eq) )
) \/
(
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((-size) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((-size) >= INT_MIN)) (PreH5 : (rop_pre = op_pre)) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-size))
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  (store_Z op_pre (-z_eq) )
).

Definition mpz_neg_return_wit_1_eq_split_goal_spatial := 
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((-size) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((-size) >= INT_MIN)) (PreH5 : (rop_pre = op_pre)) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-size))
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  (store_Z op_pre (-z_eq) )
.

Definition mpz_neg_return_wit_2_neq := 
(
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rsize))
  **  ((&((rop_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> optr)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> osize)
  **  ((&((op_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> ocap)
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg optr (Zabs (osize)) ocap )
|--
  (store_Z rop_pre (-z_neq) )
  **  (store_Z op_pre z_neq )
) \/
(
forall (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
|--
  “ ((Zabs ((-rsize))) <= rcap) ” 
  &&  “ (same_sign (-z_neq) (-rsize) ) ”
  &&  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg rptr (Zabs ((-rsize))) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs ((-z_neq))) (Zabs ((-rsize))) )
).

Definition mpz_neg_return_wit_2_neq_split_goal_1 := 
forall (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
|--
  “ ((Zabs ((-rsize))) <= rcap) ”
.

Definition mpz_neg_return_wit_2_neq_split_goal_2 := 
forall (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
|--
  “ (same_sign (-z_neq) (-rsize) ) ”
.

Definition mpz_neg_return_wit_2_neq_split_goal_spatial := 
forall (z_neq: Z) (rptr: Z) (rsize: Z) (rcap: Z) (optr: Z) (osize: Z) (ocap: Z) (PreH1 : (same_sign z_neq rsize )) (PreH2 : ((Zabs (rsize)) <= rcap)) (PreH3 : (same_sign z_neq osize )) (PreH4 : ((Zabs (osize)) <= ocap)) ,
  (mpd_store_Z_compact UINT_MOD rptr (Zabs (z_neq)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
|--
  (mpd_store_Z_compact UINT_MOD optr (Zabs (z_neq)) (Zabs (osize)) )
  **  (UIntArray.undef_seg rptr (Zabs ((-rsize))) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs ((-z_neq))) (Zabs ((-rsize))) )
.

Definition mpz_neg_partial_solve_wit_1_eq_pure := 
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (PreH1 : (rop_pre = op_pre)) ,
  ((( &( "rop" ) )) # Ptr  |-> rop_pre)
  **  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_Z op_pre z_eq )
|--
  “ (rop_pre = op_pre) ”
.

Definition mpz_neg_partial_solve_wit_1_eq_aux := 
forall (op_pre: Z) (rop_pre: Z) (z_eq: Z) (PreH1 : (rop_pre = op_pre)) ,
  (store_Z op_pre z_eq )
|--
  “ (rop_pre = op_pre) ” 
  &&  “ (rop_pre = op_pre) ”
  &&  (store_Z op_pre z_eq )
.

Definition mpz_neg_partial_solve_wit_1_eq := mpz_neg_partial_solve_wit_1_eq_pure -> mpz_neg_partial_solve_wit_1_eq_aux.

Definition mpz_neg_partial_solve_wit_2_neq := 
forall (op_pre: Z) (rop_pre: Z) (z_neq: Z) (old_neq: Z) ,
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
|--
  (store_Z rop_pre old_neq )
  **  (store_Z op_pre z_neq )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_neg_safety_wit_1_eq : mpz_neg_safety_wit_1_eq.
Axiom proof_of_mpz_neg_safety_wit_2_neq : mpz_neg_safety_wit_2_neq.
Axiom proof_of_mpz_neg_entail_wit_1_eq : mpz_neg_entail_wit_1_eq.
Axiom proof_of_mpz_neg_entail_wit_2_neq : mpz_neg_entail_wit_2_neq.
Axiom proof_of_mpz_neg_return_wit_1_eq : mpz_neg_return_wit_1_eq.
Axiom proof_of_mpz_neg_return_wit_2_neq : mpz_neg_return_wit_2_neq.
Axiom proof_of_mpz_neg_partial_solve_wit_1_eq_pure : mpz_neg_partial_solve_wit_1_eq_pure.
Axiom proof_of_mpz_neg_partial_solve_wit_1_eq : mpz_neg_partial_solve_wit_1_eq.
Axiom proof_of_mpz_neg_partial_solve_wit_2_neq : mpz_neg_partial_solve_wit_2_neq.

End VC_Correct.
