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
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import ge_gmp_array_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import ge_gmp_array_strategy_proof.

(*----- Function mod_norm_gmp -----*)

Definition mod_norm_gmp_safety_wit_1 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (rv < 0)) (PreH2 : (retval = (-1))) (PreH3 : (zp_low_level_spec > 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (rv = 0)) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |->_)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition mod_norm_gmp_safety_wit_2 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (rv > 0)) (PreH2 : (retval = 1)) (PreH3 : (zp_low_level_spec > 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (rv = 0)) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |->_)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition mod_norm_gmp_safety_wit_3 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (rv = 0)) (PreH2 : (retval = 0)) (PreH3 : (zp_low_level_spec > 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (rv = 0)) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mod_norm_gmp_safety_wit_4 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (rv < 0)) (PreH2 : (retval = (-1))) (PreH3 : (zp_low_level_spec > 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mod_norm_gmp_safety_wit_5 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (rv = 0)) (PreH2 : (retval = 0)) (PreH3 : (zp_low_level_spec > 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mod_norm_gmp_safety_wit_6 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (rv > 0)) (PreH2 : (retval = 1)) (PreH3 : (zp_low_level_spec > 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mod_norm_gmp_safety_wit_7 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (rv = 0)) (PreH3 : (retval = 0)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (rv = 0)) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition mod_norm_gmp_safety_wit_8 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (rv < 0)) (PreH3 : (retval = (-1))) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition mod_norm_gmp_safety_wit_9 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (rv = 0)) (PreH3 : (retval = 0)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition mod_norm_gmp_safety_wit_10 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (rv > 0)) (PreH3 : (retval = 1)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "s" ) )) # Int  |-> retval)
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ False ”
.

Definition mod_norm_gmp_safety_wit_11 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (rv = 0)) ,
  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z x_pre zx_low_level_spec )
|--
  “ False ”
.

Definition mod_norm_gmp_entail_wit_1_1 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (rv_2: Z) (qv_2: Z) (PreH1 : (r_pre = r_pre)) (PreH2 : (zp_low_level_spec <> 0)) (PreH3 : (zx_low_level_spec = ((qv_2 * zp_low_level_spec ) + rv_2 ))) (PreH4 : ((Zabs (rv_2)) < (Zabs (zp_low_level_spec)))) (PreH5 : (rv_2 = 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (zp_low_level_spec > 0)) ,
  (store_Z r_pre rv_2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
|--
  (EX (rv: Z)  (qv: Z) ,
  “ (zp_low_level_spec > 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (rv = 0) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
  ||
  (EX (rv: Z)  (qv: Z) ,
  “ (zp_low_level_spec > 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
.

Definition mod_norm_gmp_entail_wit_1_2 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (rv_2: Z) (qv_2: Z) (PreH1 : (r_pre = r_pre)) (PreH2 : (zp_low_level_spec <> 0)) (PreH3 : (zx_low_level_spec = ((qv_2 * zp_low_level_spec ) + rv_2 ))) (PreH4 : ((Zabs (rv_2)) < (Zabs (zp_low_level_spec)))) (PreH5 : (same_sign rv_2 zx_low_level_spec )) (PreH6 : (r_pre <> 0)) (PreH7 : (zp_low_level_spec > 0)) ,
  (store_Z r_pre rv_2 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
|--
  (EX (rv: Z)  (qv: Z) ,
  “ (zp_low_level_spec > 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (rv = 0) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
  ||
  (EX (rv: Z)  (qv: Z) ,
  “ (zp_low_level_spec > 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
.

Definition mod_norm_gmp_entail_wit_2 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (rv < 0)) (PreH3 : (retval = (-1))) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval = (-1)) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (rv < 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_entail_wit_3 := 
(
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
|--
  “ (s = (-1)) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec (rv + zp_low_level_spec ) ) ”
  &&  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
) \/
(
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec (rv + zp_low_level_spec ) ) ”
  &&  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
).

Definition mod_norm_gmp_entail_wit_3_split_goal_1 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec (rv + zp_low_level_spec ) ) ”
.

Definition mod_norm_gmp_entail_wit_3_split_goal_spatial := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
|--
  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_entail_wit_4_1 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (rv = 0)) (PreH3 : (retval = 0)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (rv = 0)) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (“ (retval >= 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ” 
  &&  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec rv ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
  ||
  (“ (retval >= 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (rv = 0) ” 
  &&  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec rv ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
.

Definition mod_norm_gmp_entail_wit_4_2 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (rv = 0)) (PreH3 : (retval = 0)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (“ (retval >= 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ” 
  &&  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec rv ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
  ||
  (“ (retval >= 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (rv = 0) ” 
  &&  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec rv ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec ))
.

Definition mod_norm_gmp_entail_wit_4_3 := 
(
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (rv > 0)) (PreH3 : (retval = 1)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval >= 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (0 <= rv) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ” 
  &&  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec rv ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
) \/
(
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (rv > 0)) (PreH3 : (retval = 1)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec rv ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
).

Definition mod_norm_gmp_entail_wit_4_3_split_goal_1 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (rv > 0)) (PreH3 : (retval = 1)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec rv ) ”
.

Definition mod_norm_gmp_entail_wit_4_3_split_goal_spatial := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (rv > 0)) (PreH3 : (retval = 1)) (PreH4 : (zp_low_level_spec > 0)) (PreH5 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH6 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH7 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_return_wit_1 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (mod_norm_spec zp_low_level_spec zx_low_level_spec (rv + zp_low_level_spec ) )) ,
  (store_Z r_pre (rv + zp_low_level_spec ) )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  EX (out: Z) ,
  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec out ) ”
  &&  (store_Z r_pre out )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_return_wit_2 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s >= 0)) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (0 <= rv)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) (PreH7 : (mod_norm_spec zp_low_level_spec zx_low_level_spec rv )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  EX (out: Z) ,
  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec out ) ”
  &&  (store_Z r_pre out )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_return_wit_3 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s >= 0)) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (0 <= rv)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (rv = 0)) (PreH7 : (mod_norm_spec zp_low_level_spec zx_low_level_spec rv )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  EX (out: Z) ,
  “ (mod_norm_spec zp_low_level_spec zx_low_level_spec out ) ”
  &&  (store_Z r_pre out )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_partial_solve_wit_1 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (old_low_level_spec: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zp_low_level_spec > 0)) ,
  (store_Z r_pre old_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_partial_solve_wit_2_pure := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zp_low_level_spec > 0)) ,
  (store_Z r_pre zx_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre = r_pre) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (zp_low_level_spec <> 0) ”
.

Definition mod_norm_gmp_partial_solve_wit_2_aux := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zp_low_level_spec > 0)) ,
  (store_Z r_pre zx_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre = r_pre) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (zp_low_level_spec <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ”
  &&  (store_Z r_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
.

Definition mod_norm_gmp_partial_solve_wit_2 := mod_norm_gmp_partial_solve_wit_2_pure -> mod_norm_gmp_partial_solve_wit_2_aux.

Definition mod_norm_gmp_partial_solve_wit_3 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (PreH1 : (zp_low_level_spec > 0)) (PreH2 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH3 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH4 : (rv = 0)) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (zp_low_level_spec > 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (rv = 0) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_partial_solve_wit_4 := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (PreH1 : (zp_low_level_spec > 0)) (PreH2 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH3 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH4 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (zp_low_level_spec > 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_norm_gmp_partial_solve_wit_5_pure := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (rv = 0)) ,
  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre = r_pre) ”
.

Definition mod_norm_gmp_partial_solve_wit_5_aux := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (rv = 0)) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre = r_pre) ” 
  &&  “ (s = (-1)) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (rv < 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (rv = 0) ”
  &&  (store_Z r_pre rv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
.

Definition mod_norm_gmp_partial_solve_wit_5 := mod_norm_gmp_partial_solve_wit_5_pure -> mod_norm_gmp_partial_solve_wit_5_aux.

Definition mod_norm_gmp_partial_solve_wit_6_pure := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre = r_pre) ”
.

Definition mod_norm_gmp_partial_solve_wit_6_aux := 
forall (p_pre: Z) (x_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (zx_low_level_spec: Z) (qv: Z) (rv: Z) (s: Z) (PreH1 : (s = (-1))) (PreH2 : (zp_low_level_spec > 0)) (PreH3 : (rv < 0)) (PreH4 : (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv ))) (PreH5 : ((Zabs (rv)) < (Zabs (zp_low_level_spec)))) (PreH6 : (same_sign rv zx_low_level_spec )) ,
  (store_Z r_pre rv )
  **  (store_Z x_pre zx_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre = r_pre) ” 
  &&  “ (s = (-1)) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (rv < 0) ” 
  &&  “ (zx_low_level_spec = ((qv * zp_low_level_spec ) + rv )) ” 
  &&  “ ((Zabs (rv)) < (Zabs (zp_low_level_spec))) ” 
  &&  “ (same_sign rv zx_low_level_spec ) ”
  &&  (store_Z r_pre rv )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z x_pre zx_low_level_spec )
.

Definition mod_norm_gmp_partial_solve_wit_6 := mod_norm_gmp_partial_solve_wit_6_pure -> mod_norm_gmp_partial_solve_wit_6_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.

Axiom proof_of_mod_norm_gmp_safety_wit_1 : mod_norm_gmp_safety_wit_1.
Axiom proof_of_mod_norm_gmp_safety_wit_2 : mod_norm_gmp_safety_wit_2.
Axiom proof_of_mod_norm_gmp_safety_wit_3 : mod_norm_gmp_safety_wit_3.
Axiom proof_of_mod_norm_gmp_safety_wit_4 : mod_norm_gmp_safety_wit_4.
Axiom proof_of_mod_norm_gmp_safety_wit_5 : mod_norm_gmp_safety_wit_5.
Axiom proof_of_mod_norm_gmp_safety_wit_6 : mod_norm_gmp_safety_wit_6.
Axiom proof_of_mod_norm_gmp_safety_wit_7 : mod_norm_gmp_safety_wit_7.
Axiom proof_of_mod_norm_gmp_safety_wit_8 : mod_norm_gmp_safety_wit_8.
Axiom proof_of_mod_norm_gmp_safety_wit_9 : mod_norm_gmp_safety_wit_9.
Axiom proof_of_mod_norm_gmp_safety_wit_10 : mod_norm_gmp_safety_wit_10.
Axiom proof_of_mod_norm_gmp_safety_wit_11 : mod_norm_gmp_safety_wit_11.
Axiom proof_of_mod_norm_gmp_entail_wit_1_1 : mod_norm_gmp_entail_wit_1_1.
Axiom proof_of_mod_norm_gmp_entail_wit_1_2 : mod_norm_gmp_entail_wit_1_2.
Axiom proof_of_mod_norm_gmp_entail_wit_2 : mod_norm_gmp_entail_wit_2.
Axiom proof_of_mod_norm_gmp_entail_wit_3 : mod_norm_gmp_entail_wit_3.
Axiom proof_of_mod_norm_gmp_entail_wit_4_1 : mod_norm_gmp_entail_wit_4_1.
Axiom proof_of_mod_norm_gmp_entail_wit_4_2 : mod_norm_gmp_entail_wit_4_2.
Axiom proof_of_mod_norm_gmp_entail_wit_4_3 : mod_norm_gmp_entail_wit_4_3.
Axiom proof_of_mod_norm_gmp_return_wit_1 : mod_norm_gmp_return_wit_1.
Axiom proof_of_mod_norm_gmp_return_wit_2 : mod_norm_gmp_return_wit_2.
Axiom proof_of_mod_norm_gmp_return_wit_3 : mod_norm_gmp_return_wit_3.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_1 : mod_norm_gmp_partial_solve_wit_1.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_2_pure : mod_norm_gmp_partial_solve_wit_2_pure.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_2 : mod_norm_gmp_partial_solve_wit_2.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_3 : mod_norm_gmp_partial_solve_wit_3.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_4 : mod_norm_gmp_partial_solve_wit_4.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_5_pure : mod_norm_gmp_partial_solve_wit_5_pure.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_5 : mod_norm_gmp_partial_solve_wit_5.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_6_pure : mod_norm_gmp_partial_solve_wit_6_pure.
Axiom proof_of_mod_norm_gmp_partial_solve_wit_6 : mod_norm_gmp_partial_solve_wit_6.

End VC_Correct.
