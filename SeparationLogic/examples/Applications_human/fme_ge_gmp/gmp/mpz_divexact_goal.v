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

(*----- Function mpz_divexact -----*)

Definition mpz_divexact_safety_wit_1 := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (old: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z q_pre old )
  **  (optional_store_Z 0 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_divexact_safety_wit_2 := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (old: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z q_pre old )
  **  (optional_store_Z 0 0 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpz_divexact_entail_wit_1 := 
(
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (old: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z q_pre old )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
|--
  “ (q_pre <> 0) ” 
  &&  “ (zd <> 0) ” 
  &&  “ (zn = ((zn ÷ zd ) * zd )) ”
  &&  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z q_pre old )
  **  (optional_store_Z 0 0 )
) \/
(
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (old: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z q_pre old )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
|--
  (store_Z q_pre old )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z 0 0 )
).

Definition mpz_divexact_entail_wit_1_split_goal_spatial := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (old: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z q_pre old )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
|--
  (store_Z q_pre old )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z 0 0 )
.

Definition mpz_divexact_entail_wit_2 := 
(
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (qv_2: Z) (rv_2: Z) (retval: Z) (PreH1 : (mpz_div_qr_math 2 zn zd qv_2 rv_2 )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (mpz_div_qr_ret_ok retval rv_2 )) (PreH5 : (q_pre <> 0)) (PreH6 : (zd <> 0)) (PreH7 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z q_pre qv_2 )
  **  (optional_store_Z 0 rv_2 )
|--
  EX (rv: Z)  (qv: Z) ,
  “ (q_pre <> 0) ” 
  &&  “ (zd <> 0) ” 
  &&  “ (zn = ((zn ÷ zd ) * zd )) ” 
  &&  “ (qv = (zn ÷ zd )) ” 
  &&  “ (rv = 0) ” 
  &&  “ (mpz_div_qr_math 2 zn zd qv rv ) ”
  &&  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (store_Z q_pre qv )
  **  (optional_store_Z 0 rv )
) \/
(
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (qv_2: Z) (rv_2: Z) (retval: Z) (PreH1 : (mpz_div_qr_math 2 zn zd qv_2 rv_2 )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (mpz_div_qr_ret_ok retval rv_2 )) (PreH5 : (q_pre <> 0)) (PreH6 : (zd <> 0)) (PreH7 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z q_pre qv_2 )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z 0 rv_2 )
|--
  “ (mpz_div_qr_math 2 zn zd (zn ÷ zd ) 0 ) ”
  &&  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (store_Z q_pre (zn ÷ zd ) )
  **  (optional_store_Z 0 0 )
).

Definition mpz_divexact_entail_wit_2_split_goal_1 := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (qv_2: Z) (rv_2: Z) (retval: Z) (PreH1 : (mpz_div_qr_math 2 zn zd qv_2 rv_2 )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (mpz_div_qr_ret_ok retval rv_2 )) (PreH5 : (q_pre <> 0)) (PreH6 : (zd <> 0)) (PreH7 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z q_pre qv_2 )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z 0 rv_2 )
|--
  “ (mpz_div_qr_math 2 zn zd (zn ÷ zd ) 0 ) ”
.

Definition mpz_divexact_entail_wit_2_split_goal_spatial := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (qv_2: Z) (rv_2: Z) (retval: Z) (PreH1 : (mpz_div_qr_math 2 zn zd qv_2 rv_2 )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (mpz_div_qr_ret_ok retval rv_2 )) (PreH5 : (q_pre <> 0)) (PreH6 : (zd <> 0)) (PreH7 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z q_pre qv_2 )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z 0 rv_2 )
|--
  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (store_Z q_pre (zn ÷ zd ) )
  **  (optional_store_Z 0 0 )
.

Definition mpz_divexact_return_wit_1 := 
(
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (qv: Z) (rv: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) (PreH4 : (qv = (zn ÷ zd ))) (PreH5 : (rv = 0)) (PreH6 : (mpz_div_qr_math 2 zn zd qv rv )) ,
  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (store_Z q_pre qv )
  **  (optional_store_Z 0 rv )
|--
  (store_Z q_pre (zn ÷ zd ) )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
) \/
(
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (qv: Z) (rv: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) (PreH4 : (qv = (zn ÷ zd ))) (PreH5 : (rv = 0)) (PreH6 : (mpz_div_qr_math 2 zn zd qv rv )) ,
  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (store_Z q_pre qv )
  **  (optional_store_Z 0 rv )
|--
  (store_Z q_pre (zn ÷ zd ) )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
).

Definition mpz_divexact_return_wit_1_split_goal_spatial := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (qv: Z) (rv: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) (PreH4 : (qv = (zn ÷ zd ))) (PreH5 : (rv = 0)) (PreH6 : (mpz_div_qr_math 2 zn zd qv rv )) ,
  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (store_Z q_pre qv )
  **  (optional_store_Z 0 rv )
|--
  (store_Z q_pre (zn ÷ zd ) )
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
.

Definition mpz_divexact_partial_solve_wit_1_pure := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (old: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "num" ) )) # Ptr  |-> num_pre)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z q_pre old )
  **  (optional_store_Z 0 0 )
|--
  “ (q_pre = q_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (num_pre = num_pre) ” 
  &&  “ (den_pre = den_pre) ” 
  &&  “ (2 = 2) ” 
  &&  “ (zd <> 0) ” 
  &&  “ (2 = 2) ”
.

Definition mpz_divexact_partial_solve_wit_1_aux := 
forall (den_pre: Z) (num_pre: Z) (q_pre: Z) (zd: Z) (zn: Z) (old: Z) (PreH1 : (q_pre <> 0)) (PreH2 : (zd <> 0)) (PreH3 : (zn = ((zn ÷ zd ) * zd ))) ,
  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z q_pre old )
  **  (optional_store_Z 0 0 )
|--
  “ (q_pre = q_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (num_pre = num_pre) ” 
  &&  “ (den_pre = den_pre) ” 
  &&  “ (2 = 2) ” 
  &&  “ (zd <> 0) ” 
  &&  “ (2 = 2) ” 
  &&  “ (q_pre <> 0) ” 
  &&  “ (zd <> 0) ” 
  &&  “ (zn = ((zn ÷ zd ) * zd )) ”
  &&  (store_Z num_pre zn )
  **  (store_Z den_pre zd )
  **  (optional_store_Z q_pre old )
  **  (optional_store_Z 0 0 )
.

Definition mpz_divexact_partial_solve_wit_1 := mpz_divexact_partial_solve_wit_1_pure -> mpz_divexact_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_divexact_safety_wit_1 : mpz_divexact_safety_wit_1.
Axiom proof_of_mpz_divexact_safety_wit_2 : mpz_divexact_safety_wit_2.
Axiom proof_of_mpz_divexact_entail_wit_1 : mpz_divexact_entail_wit_1.
Axiom proof_of_mpz_divexact_entail_wit_2 : mpz_divexact_entail_wit_2.
Axiom proof_of_mpz_divexact_return_wit_1 : mpz_divexact_return_wit_1.
Axiom proof_of_mpz_divexact_partial_solve_wit_1_pure : mpz_divexact_partial_solve_wit_1_pure.
Axiom proof_of_mpz_divexact_partial_solve_wit_1 : mpz_divexact_partial_solve_wit_1.

End VC_Correct.
