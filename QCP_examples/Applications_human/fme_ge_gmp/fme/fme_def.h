#include "fme_ge_gmp/gmp/gmp_def.h"

/*@ Import Coq Require Import SimpleC.EE.Applications_human.fme_ge_gmp.fme.fme_gmp_lib */
/*@ Import Coq Local Open Scope monad */

/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
               (bind : {Sigma} {A} {B} -> program Sigma A -> (A -> program Sigma B) -> program Sigma B)
               (return : {Sigma} {A} -> A -> program Sigma A)
               (applyf : {A} {B} -> (A -> B) -> A -> B)
               (equiv : {T} -> T -> T -> Prop)
               (ATrue : {A} -> A -> Prop)
               (tt : unit) */

/*@ Printing Coq Name program := MonadErr.M */
/*@ Printing Strategy Name program := MonadErr.M */
/*@ Printing Strategy No @ bind */

/*@ Extern Coq (Constraint :: *) */
/*@ Extern Coq (BP :: *) */
/*@ Extern Coq (makepair : Z -> list Constraint -> (Z * (list Constraint)))
               (list_Constraint : list Z -> Constraint)
               (coef_Znth : Z -> Constraint -> Z -> Z)
               (coef_Zlength : Constraint -> Z)
               (coef_replace_Znth : Z -> Z -> Constraint -> Constraint)
               (coef_pre_eq : Z -> Constraint -> Constraint -> Prop) */

/*@ Extern Coq (mpz_coef_array : Z -> Z -> Constraint -> Assertion)
               (mpz_coef_array_missing_i_rec : Z -> Z -> Z -> Z -> Constraint -> Assertion)
               (coef_array : Z -> Z -> Constraint -> Assertion)
               (coef_array_missing_i_rec : Z -> Z -> Z -> Z -> Constraint -> Assertion)
               (InequList : Z -> Z -> list Constraint -> Assertion)
               (InequList_seg : Z -> Z -> Z -> list Constraint -> Assertion)
               (InequList_nth_pos : Z -> list Constraint -> Prop)
               (InequList_nth_neg : Z -> list Constraint -> Prop)
               (InequList_nth_zero : Z -> list Constraint -> Prop) */

/*@ Extern Coq (BoundPair : Z -> Z -> BP -> Assertion)
               (empty_bp : BP)
               (add_upper : Constraint -> BP -> BP)
               (add_lower : Constraint -> BP -> BP)
               (add_remain : Constraint -> BP -> BP)
               (eliminate_xn : Z -> list Constraint -> BP -> Prop)
               (eliminate_prog : Z -> list Constraint -> program unit BP)
               (eliminate_from : Z -> list Constraint -> BP -> program unit BP)
               (generate_new_constraint : Z -> Constraint -> Constraint -> Constraint -> Prop)
               (generate_new_constraints : Z -> list Constraint -> list Constraint -> list Constraint -> Prop)
               (generate_new_constr_prog : Z -> Constraint -> Constraint -> program unit Constraint)
               (generate_new_constr_from : Z -> Z -> Constraint -> Constraint -> Z -> list Z -> program unit Constraint)
               (generate_new_constraints_inner_loop : Z -> Constraint -> list Constraint -> list Constraint -> program unit (list Constraint))
               (generate_new_constraint_list_loop : Z -> list Constraint -> list Constraint -> list Constraint -> program unit (list Constraint))
               (generate_new_constraints_after_one : Z -> Constraint -> list Constraint -> list Constraint -> list Constraint -> list Constraint -> Constraint -> program unit (list Constraint))
               (generate_new_constraint_list_prog : Z -> list Constraint -> list Constraint -> list Constraint -> program unit (list Constraint))
               (real_shadow_prog : Z -> list Constraint -> program unit (list Constraint))
               (real_shadow_loop_prog : Z -> list Constraint -> program unit (list Constraint))
               (real_shadow_after_eliminate : Z -> BP -> program unit (list Constraint))
               (real_shadow_after_generate : Z -> list Constraint -> program unit (list Constraint))
               (lia_deduction_prog : Z -> list Constraint -> program unit (Z * (list Constraint)))
               (lia_deduction_scan_from : list Constraint -> list Constraint -> bool -> program unit (Z * (list Constraint)))
               (lia_deduction_scan_from_false : list Constraint -> list Constraint -> program unit (Z * (list Constraint)))
               (lia_deduction_after_real_shadow : list Constraint -> program unit (Z * (list Constraint)))
               (form_BP : list Constraint -> list Constraint -> list Constraint -> BP -> Prop)
               (LP_implies : list Constraint -> list Constraint -> Prop)
               (InequList_Zeros : list Constraint -> Z -> Z -> Prop)
               (UNSAT : list Constraint -> Prop)
               (NonPos : list Constraint -> Prop) */

/*@ include strategies "fme_gmp.strategies" */
/*@ include strategies "safeexec_fme_gmp.strategies" */
