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
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import fme_gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import safeexec_fme_gmp_strategy_proof.

(*----- Function NilInequList -----*)

Definition NilInequList_safety_wit_1 := 
  TT && emp 
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition NilInequList_return_wit_1 := 
  TT && emp 
|--
  “ (0 = 0) ”
  &&  emp
.

(*----- Function ConsInequList -----*)

Definition ConsInequList_return_wit_1 := 
forall (l_pre: Z) (c_pre: Z) (l0: (@list Constraint)) (c0: Constraint) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (c_pre <> 0)) ,
  ((&((retval)  # "InequList" ->ₛ "coef")) # Ptr  |-> c_pre)
  **  ((&((retval)  # "InequList" ->ₛ "next")) # Ptr  |-> l_pre)
  **  (mpz_coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
|--
  “ (retval <> 0) ”
  &&  (InequList retval n (cons (c0) (l0)) )
.

Definition ConsInequList_partial_solve_wit_1 := 
forall (l_pre: Z) (c_pre: Z) (l0: (@list Constraint)) (c0: Constraint) (n: Z) (PreH1 : (c_pre <> 0)) ,
  (mpz_coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
|--
  “ (c_pre <> 0) ”
  &&  (mpz_coef_array c_pre n c0 )
  **  (InequList l_pre n l0 )
.

(*----- Function free_InequList -----*)

Definition free_InequList_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (InequList p_pre n l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_InequList_safety_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (l = (cons (x) (l0)))) (PreH3 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (mpz_coef_array h n x )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_InequList_safety_wit_3 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h = 0)) (PreH2 : (h <> 0)) (PreH3 : (l = (cons (x) (l0)))) (PreH4 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (mpz_coef_array h n x )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ False ”
.

Definition free_InequList_safety_wit_4 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (h <> 0)) (PreH3 : (l = (cons (x) (l0)))) (PreH4 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_InequList_return_wit_1 := 
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre = 0)) ,
  (InequList p_pre n l )
|--
  TT && emp 
) \/
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre = 0)) ,
  (InequList p_pre n l )
|--
  TT && emp 
).

Definition free_InequList_return_wit_1_split_goal_spatial := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre = 0)) ,
  (InequList p_pre n l )
|--
  TT && emp 
.

Definition free_InequList_return_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  TT && emp 
|--
  TT && emp 
.

Definition free_InequList_return_wit_3 := 
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  (InequList y n l0 )
|--
  TT && emp 
) \/
(
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  (InequList y n l0 )
|--
  TT && emp 
).

Definition free_InequList_return_wit_3_split_goal_spatial := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  (InequList y n l0 )
|--
  TT && emp 
.

Definition free_InequList_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (PreH1 : (p_pre <> 0)) ,
  (InequList p_pre n l )
|--
  EX (h: Z)  (y: Z)  (l0: (@list Constraint))  (x: Constraint) ,
  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (mpz_coef_array h n x )
.

Definition free_InequList_partial_solve_wit_2 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (h <> 0)) (PreH3 : (l = (cons (x) (l0)))) (PreH4 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (mpz_coef_array h n x )
|--
  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  (mpz_coef_array h n x )
  **  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_3 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (y <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_4 := 
forall (p_pre: Z) (l: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y <> 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (y <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
.

Definition free_InequList_partial_solve_wit_5 := 
forall (p_pre: Z) (l: (@list Constraint)) (n: Z) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (y = 0)) (PreH2 : (h <> 0)) (PreH3 : (h <> 0)) (PreH4 : (l = (cons (x) (l0)))) (PreH5 : (p_pre <> 0)) ,
  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y n l0 )
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (y = 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (h <> 0) ” 
  &&  “ (l = (cons (x) (l0))) ” 
  &&  “ (p_pre <> 0) ”
  &&  ((&((p_pre)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p_pre)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n l0 )
.

(*----- Function eliminate -----*)

Definition eliminate_safety_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (PreH1 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH2 : (form_BP up lo re b )) (PreH3 : (1 <= num_pre)) (PreH4 : (num_pre < n_low_level_spec)) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  (InequList cur n_low_level_spec todo )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_2 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : ((coef_Znth (num_pre) (x) (0)) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (h <> 0)) (PreH4 : (todo = (cons (x) (l0)))) (PreH5 : (cur <> 0)) (PreH6 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH7 : (form_BP up lo re b )) (PreH8 : (1 <= num_pre)) (PreH9 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_3 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : ((coef_Znth (num_pre) (x) (0)) = 0)) (PreH2 : (retval = 0)) (PreH3 : (h <> 0)) (PreH4 : (todo = (cons (x) (l0)))) (PreH5 : (cur <> 0)) (PreH6 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH7 : (form_BP up lo re b )) (PreH8 : (1 <= num_pre)) (PreH9 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_4 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH2 : (retval = 1)) (PreH3 : (h <> 0)) (PreH4 : (todo = (cons (x) (l0)))) (PreH5 : (cur <> 0)) (PreH6 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH7 : (form_BP up lo re b )) (PreH8 : (1 <= num_pre)) (PreH9 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_5 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (h <> 0)) (PreH5 : (todo = (cons (x) (l0)))) (PreH6 : (cur <> 0)) (PreH7 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH8 : (form_BP up lo re b )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ False ”
.

Definition eliminate_safety_wit_6 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (h <> 0)) (PreH5 : (todo = (cons (x) (l0)))) (PreH6 : (cur <> 0)) (PreH7 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH8 : (form_BP up lo re b )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ False ”
.

Definition eliminate_safety_wit_7 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (h <> 0)) (PreH5 : (todo = (cons (x) (l0)))) (PreH6 : (cur <> 0)) (PreH7 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH8 : (form_BP up lo re b )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ False ”
.

Definition eliminate_safety_wit_8 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (h <> 0)) (PreH5 : (todo = (cons (x) (l0)))) (PreH6 : (cur <> 0)) (PreH7 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH8 : (form_BP up lo re b )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_9 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (h <> 0)) (PreH5 : (todo = (cons (x) (l0)))) (PreH6 : (cur <> 0)) (PreH7 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH8 : (form_BP up lo re b )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eliminate_safety_wit_10 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval <> 0)) (PreH3 : ((coef_Znth (num_pre) (x) (0)) < 0)) (PreH4 : (retval = (-1))) (PreH5 : (h <> 0)) (PreH6 : (todo = (cons (x) (l0)))) (PreH7 : (cur <> 0)) (PreH8 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH9 : (form_BP up lo re b )) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ False ”
.

Definition eliminate_safety_wit_11 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (retval <> 0)) (PreH3 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH4 : (retval = 1)) (PreH5 : (h <> 0)) (PreH6 : (todo = (cons (x) (l0)))) (PreH7 : (cur <> 0)) (PreH8 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH9 : (form_BP up lo re b )) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "sign" ) )) # Int  |-> retval)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "upper" ) )) # Ptr  |-> upper)
  **  (InequList upper n_low_level_spec up )
  **  ((( &( "lower" ) )) # Ptr  |-> lower)
  **  (InequList lower n_low_level_spec lo )
  **  ((( &( "remain" ) )) # Ptr  |-> remain)
  **  (InequList remain n_low_level_spec re )
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
|--
  “ False ”
.

Definition eliminate_entail_wit_1 := 
(
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (l_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval = 0)) (PreH4 : (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec )) (PreH5 : (1 <= num_pre)) (PreH6 : (num_pre < n_low_level_spec)) (PreH7 : (BP0 <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec )
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (todo: (@list Constraint))  (b: BP) ,
  “ (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList retval n_low_level_spec up )
  **  (InequList retval_2 n_low_level_spec lo )
  **  (InequList retval_3 n_low_level_spec re )
  **  (InequList r_pre n_low_level_spec todo )
) \/
(
forall (num_pre: Z) (l_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (BP0: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval = 0)) (PreH4 : (1 <= num_pre)) (PreH5 : (num_pre < n_low_level_spec)) (PreH6 : (BP0 <> 0)) ,
  TT && emp 
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (b: BP) ,
  “ (equiv (eliminate_prog (num_pre) (l_low_level_spec)) (eliminate_from (num_pre) (l_low_level_spec) (b)) ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  (InequList retval n_low_level_spec up )
  **  (InequList retval_2 n_low_level_spec lo )
  **  (InequList retval_3 n_low_level_spec re )
).

Definition eliminate_entail_wit_2_1 := 
(
forall (num_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo_2: (@list Constraint)) (b_2: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval <> 0)) (PreH3 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH4 : (retval = 1)) (PreH5 : (h <> 0)) (PreH6 : (todo_2 = (cons (x) (l0)))) (PreH7 : (cur <> 0)) (PreH8 : (safeExec ATrue (eliminate_from (num_pre) (todo_2) (b_2)) X_low_level_spec )) (PreH9 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> upper)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up_2 )
  **  (InequList lower n_low_level_spec lo_2 )
  **  (InequList remain n_low_level_spec re_2 )
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (todo: (@list Constraint))  (b: BP) ,
  “ (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList cur n_low_level_spec up )
  **  (InequList lower n_low_level_spec lo )
  **  (InequList remain n_low_level_spec re )
  **  (InequList y n_low_level_spec todo )
) \/
(
forall (num_pre: Z) (n_low_level_spec: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo_2: (@list Constraint)) (b_2: BP) (x: Constraint) (l0: (@list Constraint)) (h: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval <> 0)) (PreH3 : ((coef_Znth (num_pre) (x) (0)) > 0)) (PreH4 : (retval = 1)) (PreH5 : (h <> 0)) (PreH6 : (todo_2 = (cons (x) (l0)))) (PreH7 : (cur <> 0)) (PreH8 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  TT && emp 
|--
  EX (b: BP) ,
  “ (h <> 0) ” 
  &&  “ (equiv (eliminate_from (num_pre) (todo_2) (b_2)) (eliminate_from (num_pre) (l0) (b)) ) ” 
  &&  “ (form_BP (cons (x) (up_2)) lo_2 re_2 b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  emp
).

Definition eliminate_entail_wit_2_2 := 
(
forall (num_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo_2: (@list Constraint)) (b_2: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (retval <> 0)) (PreH3 : ((coef_Znth (num_pre) (x) (0)) < 0)) (PreH4 : (retval = (-1))) (PreH5 : (h <> 0)) (PreH6 : (todo_2 = (cons (x) (l0)))) (PreH7 : (cur <> 0)) (PreH8 : (safeExec ATrue (eliminate_from (num_pre) (todo_2) (b_2)) X_low_level_spec )) (PreH9 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH10 : (1 <= num_pre)) (PreH11 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> lower)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up_2 )
  **  (InequList lower n_low_level_spec lo_2 )
  **  (InequList remain n_low_level_spec re_2 )
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (todo: (@list Constraint))  (b: BP) ,
  “ (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up )
  **  (InequList cur n_low_level_spec lo )
  **  (InequList remain n_low_level_spec re )
  **  (InequList y n_low_level_spec todo )
) \/
(
forall (num_pre: Z) (n_low_level_spec: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo_2: (@list Constraint)) (b_2: BP) (x: Constraint) (l0: (@list Constraint)) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (retval <> 0)) (PreH3 : ((coef_Znth (num_pre) (x) (0)) < 0)) (PreH4 : (retval = (-1))) (PreH5 : (h <> 0)) (PreH6 : (todo_2 = (cons (x) (l0)))) (PreH7 : (cur <> 0)) (PreH8 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  TT && emp 
|--
  EX (b: BP) ,
  “ (h <> 0) ” 
  &&  “ (equiv (eliminate_from (num_pre) (todo_2) (b_2)) (eliminate_from (num_pre) (l0) (b)) ) ” 
  &&  “ (form_BP up_2 (cons (x) (lo_2)) re_2 b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  emp
).

Definition eliminate_entail_wit_2_3 := 
(
forall (num_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo_2: (@list Constraint)) (b_2: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (h <> 0)) (PreH5 : (todo_2 = (cons (x) (l0)))) (PreH6 : (cur <> 0)) (PreH7 : (safeExec ATrue (eliminate_from (num_pre) (todo_2) (b_2)) X_low_level_spec )) (PreH8 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH9 : (1 <= num_pre)) (PreH10 : (num_pre < n_low_level_spec)) ,
  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> remain)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |-> y)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up_2 )
  **  (InequList lower n_low_level_spec lo_2 )
  **  (InequList remain n_low_level_spec re_2 )
|--
  EX (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (todo: (@list Constraint))  (b: BP) ,
  “ (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "cur_next" ) )) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up )
  **  (InequList lower n_low_level_spec lo )
  **  (InequList cur n_low_level_spec re )
  **  (InequList y n_low_level_spec todo )
) \/
(
forall (num_pre: Z) (n_low_level_spec: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo_2: (@list Constraint)) (b_2: BP) (x: Constraint) (l0: (@list Constraint)) (h: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((coef_Znth (num_pre) (x) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (h <> 0)) (PreH5 : (todo_2 = (cons (x) (l0)))) (PreH6 : (cur <> 0)) (PreH7 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH8 : (1 <= num_pre)) (PreH9 : (num_pre < n_low_level_spec)) ,
  TT && emp 
|--
  EX (b: BP) ,
  “ (h <> 0) ” 
  &&  “ (equiv (eliminate_from (num_pre) (todo_2) (b_2)) (eliminate_from (num_pre) (l0) (b)) ) ” 
  &&  “ (form_BP up_2 lo_2 (cons (x) (re_2)) b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  emp
).

Definition eliminate_return_wit_1 := 
(
forall (num_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo: (@list Constraint)) (b_2: BP) (PreH1 : (cur = 0)) (PreH2 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b_2)) X_low_level_spec )) (PreH3 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH4 : (1 <= num_pre)) (PreH5 : (num_pre < n_low_level_spec)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> remain)
  **  (InequList upper n_low_level_spec up_2 )
  **  (InequList lower n_low_level_spec lo_2 )
  **  (InequList remain n_low_level_spec re_2 )
  **  (InequList cur n_low_level_spec todo )
|--
  EX (BP0_remain: Z)  (BP0_lower: Z)  (BP0_upper: Z)  (up: (@list Constraint))  (lo: (@list Constraint))  (re: (@list Constraint))  (b: BP) ,
  “ (safeExec ATrue (return (b)) X_low_level_spec ) ” 
  &&  “ (form_BP up lo re b ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper n_low_level_spec up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower n_low_level_spec lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain n_low_level_spec re )
) \/
(
forall (num_pre: Z) (n_low_level_spec: Z) (cur: Z) (up_2: (@list Constraint)) (lo_2: (@list Constraint)) (re_2: (@list Constraint)) (todo: (@list Constraint)) (b_2: BP) (PreH1 : (cur = 0)) (PreH2 : (form_BP up_2 lo_2 re_2 b_2 )) (PreH3 : (1 <= num_pre)) (PreH4 : (num_pre < n_low_level_spec)) ,
  (InequList cur n_low_level_spec todo )
|--
  EX (b: BP) ,
  “ (equiv (eliminate_from (num_pre) (todo) (b_2)) (return (b)) ) ” 
  &&  “ (form_BP up_2 lo_2 re_2 b ) ”
  &&  emp
).

Definition eliminate_partial_solve_wit_1 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (l_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (BP0: Z) (PreH1 : (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec )) (PreH2 : (1 <= num_pre)) (PreH3 : (num_pre < n_low_level_spec)) (PreH4 : (BP0 <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec )
|--
  “ (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ” 
  &&  “ (BP0 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec )
.

Definition eliminate_partial_solve_wit_2 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (l_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (BP0: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec )) (PreH3 : (1 <= num_pre)) (PreH4 : (num_pre < n_low_level_spec)) (PreH5 : (BP0 <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec )
|--
  “ (retval = 0) ” 
  &&  “ (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ” 
  &&  “ (BP0 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec )
.

Definition eliminate_partial_solve_wit_3 := 
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (l_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (BP0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval = 0)) (PreH3 : (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec )) (PreH4 : (1 <= num_pre)) (PreH5 : (num_pre < n_low_level_spec)) (PreH6 : (BP0 <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec )
|--
  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ” 
  &&  “ (BP0 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec )
.

Definition eliminate_partial_solve_wit_4 := 
forall (num_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (PreH1 : (cur <> 0)) (PreH2 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH3 : (form_BP up lo re b )) (PreH4 : (1 <= num_pre)) (PreH5 : (num_pre < n_low_level_spec)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up )
  **  (InequList lower n_low_level_spec lo )
  **  (InequList remain n_low_level_spec re )
  **  (InequList cur n_low_level_spec todo )
|--
  EX (h: Z)  (y: Z)  (l0: (@list Constraint))  (x: Constraint) ,
  “ (h <> 0) ” 
  &&  “ (todo = (cons (x) (l0))) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up )
  **  (InequList lower n_low_level_spec lo )
  **  (InequList remain n_low_level_spec re )
.

Definition eliminate_partial_solve_wit_5 := 
forall (num_pre: Z) (X_low_level_spec: (BP -> (unit -> Prop))) (n_low_level_spec: Z) (BP0: Z) (cur: Z) (remain: Z) (lower: Z) (upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (todo: (@list Constraint)) (b: BP) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (todo = (cons (x) (l0)))) (PreH3 : (cur <> 0)) (PreH4 : (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec )) (PreH5 : (form_BP up lo re b )) (PreH6 : (1 <= num_pre)) (PreH7 : (num_pre < n_low_level_spec)) ,
  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  (mpz_coef_array h n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up )
  **  (InequList lower n_low_level_spec lo )
  **  (InequList remain n_low_level_spec re )
|--
  “ (h <> 0) ” 
  &&  “ (todo = (cons (x) (l0))) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (safeExec ATrue (eliminate_from (num_pre) (todo) (b)) X_low_level_spec ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ”
  &&  (store_Z (h + (num_pre * sizeof( "__mpz_struct" ))) (coef_Znth (num_pre) (x) (0)) )
  **  (mpz_coef_array_missing_i_rec h num_pre 0 n_low_level_spec x )
  **  ((&((cur)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  ((&((cur)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList upper n_low_level_spec up )
  **  (InequList lower n_low_level_spec lo )
  **  (InequList remain n_low_level_spec re )
.

(*----- Function generate_new_constr -----*)

Definition generate_new_constr_safety_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval_5)
  **  ((( &( "m1" ) )) # Ptr  |-> retval_4)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_3)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_2)
  **  ((( &( "an" ) )) # Ptr  |-> retval)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ ((num_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num_pre + 1 )) ”
.

Definition generate_new_constr_safety_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval_5)
  **  ((( &( "m1" ) )) # Ptr  |-> retval_4)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_3)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_2)
  **  ((( &( "an" ) )) # Ptr  |-> retval)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition generate_new_constr_safety_wit_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (l: Constraint) (retval_7: Z) (PreH1 : (retval_7 <> 0)) (PreH2 : ((coef_Zlength (l)) = (num_pre + 1 ))) (PreH3 : (retval_6 <> 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval <> 0)) (PreH9 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH10 : (1 <= cur_num_pre)) (PreH11 : (cur_num_pre < (num_pre + 1 ))) (PreH12 : (num_pre <= (INT_MAX - 1 ))) (PreH13 : (r1_pre <> 0)) (PreH14 : (r2_pre <> 0)) ,
  (mpz_coef_array retval_7 (num_pre + 1 ) l )
  **  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |-> retval_7)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval_5)
  **  ((( &( "m1" ) )) # Ptr  |-> retval_4)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_3)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_2)
  **  ((( &( "an" ) )) # Ptr  |-> retval)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constr_safety_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i <= num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z (res + (i * sizeof( "__mpz_struct" ))) ((m1_v * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (store_Z tmp ((m1_v * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (mpz_coef_array_missing_i_rec res i 0 (num_pre + 1 ) c3 )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (store_Z m2 m2_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z m1 m1_v )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  ((( &( "an" ) )) # Ptr  |-> an)
  **  (store_Z an an_v )
  **  ((( &( "bn" ) )) # Ptr  |-> bn)
  **  (store_Z bn bn_v )
  **  ((( &( "gcd_val" ) )) # Ptr  |-> gcd_val)
  **  (store_Z gcd_val g_v )
  **  ((( &( "m1" ) )) # Ptr  |-> m1)
  **  ((( &( "m2" ) )) # Ptr  |-> m2)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition generate_new_constr_entail_wit_1 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (l: Constraint) (retval_7: Z) (PreH1 : (retval_7 <> 0)) (PreH2 : ((coef_Zlength (l)) = (num_pre + 1 ))) (PreH3 : (retval_6 <> 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval <> 0)) (PreH9 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH10 : (1 <= cur_num_pre)) (PreH11 : (cur_num_pre < (num_pre + 1 ))) (PreH12 : (num_pre <= (INT_MAX - 1 ))) (PreH13 : (r1_pre <> 0)) (PreH14 : (r2_pre <> 0)) ,
  (mpz_coef_array retval_7 (num_pre + 1 ) l )
  **  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
|--
  EX (tmp_v: Z)  (c3: Constraint)  (g_v: Z)  (bn_v: Z)  (an_v: Z)  (m1_v: Z)  (m2_v: Z)  (prefix: (@list Z)) ,
  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (0) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (num_pre + 1 )) ” 
  &&  “ (0 = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq 0 c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z retval an_v )
  **  (store_Z retval_2 bn_v )
  **  (store_Z retval_3 g_v )
  **  (store_Z retval_4 m1_v )
  **  (store_Z retval_5 m2_v )
  **  (store_Z retval_6 tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array retval_7 (num_pre + 1 ) c3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (l: Constraint) (retval_7: Z) (PreH1 : (retval_7 <> 0)) (PreH2 : ((coef_Zlength (l)) = (num_pre + 1 ))) (PreH3 : (retval_6 <> 0)) (PreH4 : (retval_5 <> 0)) (PreH5 : (retval_4 <> 0)) (PreH6 : (retval_3 <> 0)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval <> 0)) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < (num_pre + 1 ))) (PreH11 : (num_pre <= (INT_MAX - 1 ))) (PreH12 : (r1_pre <> 0)) (PreH13 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_6 0 )
|--
  EX (tmp_v: Z)  (prefix: (@list Z)) ,
  “ (equiv (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) (generate_new_constr_from (((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) (((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) (c1_low_level_spec) (c2_low_level_spec) (0) (prefix)) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (num_pre + 1 )) ” 
  &&  “ (0 = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (retval_7 <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (l)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq 0 l (list_Constraint (prefix)) ) ”
  &&  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_6 tmp_v )
).

Definition generate_new_constr_entail_wit_2 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3_2: Constraint) (res: Z) (g_v_2: Z) (bn_v_2: Z) (an_v_2: Z) (m1_v_2: Z) (m2_v_2: Z) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i <= num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v_2) (m2_v_2) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix_2)) X_low_level_spec )) (PreH3 : (an_v_2 = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v_2 = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v_2 = (Zgcd (an_v_2) (bn_v_2)))) (PreH6 : (m1_v_2 = (bn_v_2 ÷ g_v_2 ))) (PreH7 : (m2_v_2 = (an_v_2 ÷ g_v_2 ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix_2)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3_2)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3_2 (list_Constraint (prefix_2)) )) ,
  (store_Z (res + (i * sizeof( "__mpz_struct" ))) ((m1_v_2 * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v_2 * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (store_Z tmp ((m1_v_2 * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v_2 * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (mpz_coef_array_missing_i_rec res i 0 (num_pre + 1 ) c3_2 )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (store_Z m2 m2_v_2 )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z m1 m1_v_2 )
  **  (store_Z an an_v_2 )
  **  (store_Z bn bn_v_2 )
  **  (store_Z gcd_val g_v_2 )
|--
  EX (tmp_v: Z)  (c3: Constraint)  (g_v: Z)  (bn_v: Z)  (an_v: Z)  (m1_v: Z)  (m2_v: Z)  (prefix: (@list Z)) ,
  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) ((i + 1 )) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (num_pre + 1 )) ” 
  &&  “ ((i + 1 ) = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq (i + 1 ) c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3_2: Constraint) (res: Z) (g_v_2: Z) (bn_v_2: Z) (an_v_2: Z) (m1_v_2: Z) (m2_v_2: Z) (i: Z) (prefix_2: (@list Z)) (PreH1 : (i <= num_pre)) (PreH2 : (an_v_2 = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH3 : (bn_v_2 = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH4 : (g_v_2 = (Zgcd (an_v_2) (bn_v_2)))) (PreH5 : (m1_v_2 = (bn_v_2 ÷ g_v_2 ))) (PreH6 : (m2_v_2 = (an_v_2 ÷ g_v_2 ))) (PreH7 : (0 <= i)) (PreH8 : (i <= (num_pre + 1 ))) (PreH9 : (i = (Zlength (prefix_2)))) (PreH10 : (1 <= cur_num_pre)) (PreH11 : (cur_num_pre < (num_pre + 1 ))) (PreH12 : (num_pre <= (INT_MAX - 1 ))) (PreH13 : (r1_pre <> 0)) (PreH14 : (r2_pre <> 0)) (PreH15 : (res <> 0)) (PreH16 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH17 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c3_2)) = (num_pre + 1 ))) (PreH19 : (coef_pre_eq i c3_2 (list_Constraint (prefix_2)) )) ,
  (store_Z (res + (i * sizeof( "__mpz_struct" ))) ((m1_v_2 * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v_2 * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (store_Z tmp ((m1_v_2 * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v_2 * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (mpz_coef_array_missing_i_rec res i 0 (num_pre + 1 ) c3_2 )
  **  (store_Z m2 m2_v_2 )
  **  (store_Z m1 m1_v_2 )
  **  (store_Z an an_v_2 )
  **  (store_Z bn bn_v_2 )
  **  (store_Z gcd_val g_v_2 )
|--
  EX (tmp_v: Z)  (c3: Constraint)  (prefix: (@list Z)) ,
  “ (equiv (generate_new_constr_from (m1_v_2) (m2_v_2) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix_2)) (generate_new_constr_from (((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) (((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) (c1_low_level_spec) (c2_low_level_spec) ((i + 1 )) (prefix)) ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (num_pre + 1 )) ” 
  &&  “ ((i + 1 ) = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq (i + 1 ) c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z an (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z bn (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z gcd_val (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z m1 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z m2 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
).

Definition generate_new_constr_return_wit_1 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (c3_2: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3_2)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3_2 (list_Constraint (prefix)) )) ,
  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3_2 )
|--
  EX (c3: Constraint) ,
  “ (res <> 0) ” 
  &&  “ (safeExec ATrue (return (c3)) X_low_level_spec ) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (c3_2: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH3 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH4 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH5 : (m1_v = (bn_v ÷ g_v ))) (PreH6 : (m2_v = (an_v ÷ g_v ))) (PreH7 : (0 <= i)) (PreH8 : (i <= (num_pre + 1 ))) (PreH9 : (i = (Zlength (prefix)))) (PreH10 : (1 <= cur_num_pre)) (PreH11 : (cur_num_pre < (num_pre + 1 ))) (PreH12 : (num_pre <= (INT_MAX - 1 ))) (PreH13 : (r1_pre <> 0)) (PreH14 : (r2_pre <> 0)) (PreH15 : (res <> 0)) (PreH16 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH17 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c3_2)) = (num_pre + 1 ))) (PreH19 : (coef_pre_eq i c3_2 (list_Constraint (prefix)) )) ,
  TT && emp 
|--
  “ (equiv (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) (return (c3_2)) ) ”
  &&  emp
).

Definition generate_new_constr_return_wit_1_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (c3_2: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH3 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH4 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH5 : (m1_v = (bn_v ÷ g_v ))) (PreH6 : (m2_v = (an_v ÷ g_v ))) (PreH7 : (0 <= i)) (PreH8 : (i <= (num_pre + 1 ))) (PreH9 : (i = (Zlength (prefix)))) (PreH10 : (1 <= cur_num_pre)) (PreH11 : (cur_num_pre < (num_pre + 1 ))) (PreH12 : (num_pre <= (INT_MAX - 1 ))) (PreH13 : (r1_pre <> 0)) (PreH14 : (r2_pre <> 0)) (PreH15 : (res <> 0)) (PreH16 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH17 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c3_2)) = (num_pre + 1 ))) (PreH19 : (coef_pre_eq i c3_2 (list_Constraint (prefix)) )) ,
  (equiv (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) (return (c3_2)) )
.

Definition generate_new_constr_partial_solve_wit_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (PreH1 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < (num_pre + 1 ))) (PreH4 : (num_pre <= (INT_MAX - 1 ))) (PreH5 : (r1_pre <> 0)) (PreH6 : (r2_pre <> 0)) ,
  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < (num_pre + 1 ))) (PreH5 : (num_pre <= (INT_MAX - 1 ))) (PreH6 : (r1_pre <> 0)) (PreH7 : (r2_pre <> 0)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < (num_pre + 1 ))) (PreH6 : (num_pre <= (INT_MAX - 1 ))) (PreH7 : (r1_pre <> 0)) (PreH8 : (r2_pre <> 0)) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_4 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH5 : (1 <= cur_num_pre)) (PreH6 : (cur_num_pre < (num_pre + 1 ))) (PreH7 : (num_pre <= (INT_MAX - 1 ))) (PreH8 : (r1_pre <> 0)) (PreH9 : (r2_pre <> 0)) ,
  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_5 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH6 : (1 <= cur_num_pre)) (PreH7 : (cur_num_pre < (num_pre + 1 ))) (PreH8 : (num_pre <= (INT_MAX - 1 ))) (PreH9 : (r1_pre <> 0)) (PreH10 : (r2_pre <> 0)) ,
  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_6 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (retval_4 <> 0)) (PreH3 : (retval_3 <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH7 : (1 <= cur_num_pre)) (PreH8 : (cur_num_pre < (num_pre + 1 ))) (PreH9 : (num_pre <= (INT_MAX - 1 ))) (PreH10 : (r1_pre <> 0)) (PreH11 : (r2_pre <> 0)) ,
  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_7 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_8 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_9 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_10 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_11 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_5)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_12 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_6)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_13 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (store_Z retval 0 )
  **  (store_Z (r1_pre + (cur_num_pre * sizeof( "__mpz_struct" ))) (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array_missing_i_rec r1_pre cur_num_pre 0 (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
.

Definition generate_new_constr_partial_solve_wit_14 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (store_Z retval_2 0 )
  **  (store_Z (r2_pre + (cur_num_pre * sizeof( "__mpz_struct" ))) (coef_Znth (cur_num_pre) (c2_low_level_spec) (0)) )
  **  (mpz_coef_array_missing_i_rec r2_pre cur_num_pre 0 (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
.

Definition generate_new_constr_partial_solve_wit_15 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (store_Z retval_3 0 )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval_4 0 )
.

Definition generate_new_constr_partial_solve_wit_16_pure := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval_5)
  **  ((( &( "m1" ) )) # Ptr  |-> retval)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ (retval <> 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) = (((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ” 
  &&  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (retval_6 <> 0)) (PreH6 : (retval_5 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_3 <> 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < (num_pre + 1 ))) (PreH14 : (num_pre <= (INT_MAX - 1 ))) (PreH15 : (r1_pre <> 0)) (PreH16 : (r2_pre <> 0)) ,
  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval_5)
  **  ((( &( "m1" ) )) # Ptr  |-> retval)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) = (((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ”
).

Definition generate_new_constr_partial_solve_wit_16_pure_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (retval_6 <> 0)) (PreH6 : (retval_5 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_3 <> 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < (num_pre + 1 ))) (PreH14 : (num_pre <= (INT_MAX - 1 ))) (PreH15 : (r1_pre <> 0)) (PreH16 : (r2_pre <> 0)) ,
  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval_5)
  **  ((( &( "m1" ) )) # Ptr  |-> retval)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ”
.

Definition generate_new_constr_partial_solve_wit_16_pure_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (retval_6 <> 0)) (PreH6 : (retval_5 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_3 <> 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < (num_pre + 1 ))) (PreH14 : (num_pre <= (INT_MAX - 1 ))) (PreH15 : (r1_pre <> 0)) (PreH16 : (r2_pre <> 0)) ,
  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval_5)
  **  ((( &( "m1" ) )) # Ptr  |-> retval)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) = (((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ”
.

Definition generate_new_constr_partial_solve_wit_16_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
  **  (store_Z retval 0 )
|--
  “ (retval <> 0) ” 
  &&  “ ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) = (((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ” 
  &&  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ” 
  &&  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (store_Z retval 0 )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval_5 0 )
.

Definition generate_new_constr_partial_solve_wit_16 := generate_new_constr_partial_solve_wit_16_pure -> generate_new_constr_partial_solve_wit_16_aux.

Definition generate_new_constr_partial_solve_wit_17_pure := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval)
  **  ((( &( "m1" ) )) # Ptr  |-> retval_5)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ (retval <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) = (((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ” 
  &&  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ”
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_6: Z) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (retval_6 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (retval_5 <> 0)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_3 <> 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < (num_pre + 1 ))) (PreH14 : (num_pre <= (INT_MAX - 1 ))) (PreH15 : (r1_pre <> 0)) (PreH16 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval)
  **  ((( &( "m1" ) )) # Ptr  |-> retval_5)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) = (((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ”
).

Definition generate_new_constr_partial_solve_wit_17_pure_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_6: Z) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (retval_6 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (retval_5 <> 0)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_3 <> 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < (num_pre + 1 ))) (PreH14 : (num_pre <= (INT_MAX - 1 ))) (PreH15 : (r1_pre <> 0)) (PreH16 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval)
  **  ((( &( "m1" ) )) # Ptr  |-> retval_5)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ”
.

Definition generate_new_constr_partial_solve_wit_17_pure_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_6: Z) (PreH1 : (cur_num_pre <= INT_MAX)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (cur_num_pre >= INT_MIN)) (PreH4 : (num_pre >= INT_MIN)) (PreH5 : (retval_6 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (retval_5 <> 0)) (PreH8 : (retval_4 <> 0)) (PreH9 : (retval_3 <> 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < (num_pre + 1 ))) (PreH14 : (num_pre <= (INT_MAX - 1 ))) (PreH15 : (r1_pre <> 0)) (PreH16 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval 0 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_6)
  **  ((( &( "m2" ) )) # Ptr  |-> retval)
  **  ((( &( "m1" ) )) # Ptr  |-> retval_5)
  **  ((( &( "gcd_val" ) )) # Ptr  |-> retval_4)
  **  ((( &( "bn" ) )) # Ptr  |-> retval_3)
  **  ((( &( "an" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
|--
  “ ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) = (((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ”
.

Definition generate_new_constr_partial_solve_wit_17_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_5 <> 0)) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
  **  (store_Z retval 0 )
|--
  “ (retval <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) = (((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) * (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )) ” 
  &&  “ ((Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) <> 0) ” 
  &&  “ (retval_6 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (store_Z retval 0 )
  **  (store_Z retval_2 (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_4 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_5 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_3 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
.

Definition generate_new_constr_partial_solve_wit_17 := generate_new_constr_partial_solve_wit_17_pure -> generate_new_constr_partial_solve_wit_17_aux.

Definition generate_new_constr_partial_solve_wit_18 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (retval_5 <> 0)) (PreH3 : (retval_4 <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec )) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < (num_pre + 1 ))) (PreH10 : (num_pre <= (INT_MAX - 1 ))) (PreH11 : (r1_pre <> 0)) (PreH12 : (r2_pre <> 0)) ,
  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (retval_5 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (store_Z retval_5 ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)) )
  **  (store_Z retval_3 (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) )
  **  (store_Z retval_4 ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) ÷ (Zgcd ((coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ((-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) ) )
  **  (store_Z retval_2 (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))) )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z retval_6 0 )
.

Definition generate_new_constr_partial_solve_wit_19 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i <= num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i <= num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z tmp tmp_v )
  **  (store_Z m1 m1_v )
  **  (store_Z (r1_pre + (i * sizeof( "__mpz_struct" ))) (coef_Znth (i) (c1_low_level_spec) (0)) )
  **  (mpz_coef_array_missing_i_rec r1_pre i 0 (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m2 m2_v )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_20 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i <= num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z tmp (m1_v * (coef_Znth (i) (c1_low_level_spec) (0)) ) )
  **  (store_Z m1 m1_v )
  **  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m2 m2_v )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i <= num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z tmp (m1_v * (coef_Znth (i) (c1_low_level_spec) (0)) ) )
  **  (store_Z m2 m2_v )
  **  (store_Z (r2_pre + (i * sizeof( "__mpz_struct" ))) (coef_Znth (i) (c2_low_level_spec) (0)) )
  **  (mpz_coef_array_missing_i_rec r2_pre i 0 (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z m1 m1_v )
  **  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_21 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i <= num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (store_Z tmp ((m1_v * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (store_Z m2 m2_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z m1 m1_v )
  **  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i <= num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z (res + (i * sizeof( "__mpz_struct" ))) (coef_Znth (i) (c3) (0)) )
  **  (store_Z tmp ((m1_v * (coef_Znth (i) (c1_low_level_spec) (0)) ) + (m2_v * (coef_Znth (i) (c2_low_level_spec) (0)) ) ) )
  **  (mpz_coef_array_missing_i_rec res i 0 (num_pre + 1 ) c3 )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (store_Z m2 m2_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (store_Z m1 m1_v )
  **  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
.

Definition generate_new_constr_partial_solve_wit_22 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z an an_v )
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_23 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (an: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  ((&((an)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((an)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((an)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  ((&((an)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((an)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((an)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_24 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z bn bn_v )
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_25 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (gcd_val: Z) (bn: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  ((&((bn)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((bn)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((bn)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  ((&((bn)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((bn)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((bn)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_26 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (gcd_val: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z gcd_val g_v )
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_27 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (gcd_val: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  ((&((gcd_val)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((gcd_val)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((gcd_val)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  ((&((gcd_val)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((gcd_val)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((gcd_val)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_28 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z m1 m1_v )
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_29 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (m1: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  ((&((m1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((m1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  ((&((m1)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((m1)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m1)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_30 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z m2 m2_v )
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_31 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (m2: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  ((&((m2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((m2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  ((&((m2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((m2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_32 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (tmp_v: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  (store_Z tmp tmp_v )
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

Definition generate_new_constr_partial_solve_wit_33 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: (Constraint -> (unit -> Prop))) (c2_low_level_spec: Constraint) (c1_low_level_spec: Constraint) (tmp: Z) (c3: Constraint) (res: Z) (g_v: Z) (bn_v: Z) (an_v: Z) (m1_v: Z) (m2_v: Z) (i: Z) (prefix: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (i > num_pre)) (PreH2 : (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec )) (PreH3 : (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0)))) (PreH4 : (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0))))) (PreH5 : (g_v = (Zgcd (an_v) (bn_v)))) (PreH6 : (m1_v = (bn_v ÷ g_v ))) (PreH7 : (m2_v = (an_v ÷ g_v ))) (PreH8 : (0 <= i)) (PreH9 : (i <= (num_pre + 1 ))) (PreH10 : (i = (Zlength (prefix)))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < (num_pre + 1 ))) (PreH13 : (num_pre <= (INT_MAX - 1 ))) (PreH14 : (r1_pre <> 0)) (PreH15 : (r2_pre <> 0)) (PreH16 : (res <> 0)) (PreH17 : ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 ))) (PreH18 : ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 ))) (PreH19 : ((coef_Zlength (c3)) = (num_pre + 1 ))) (PreH20 : (coef_pre_eq i c3 (list_Constraint (prefix)) )) ,
  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
|--
  “ (i > num_pre) ” 
  &&  “ (safeExec ATrue (generate_new_constr_from (m1_v) (m2_v) (c1_low_level_spec) (c2_low_level_spec) (i) (prefix)) X_low_level_spec ) ” 
  &&  “ (an_v = (coef_Znth (cur_num_pre) (c1_low_level_spec) (0))) ” 
  &&  “ (bn_v = (-(coef_Znth (cur_num_pre) (c2_low_level_spec) (0)))) ” 
  &&  “ (g_v = (Zgcd (an_v) (bn_v))) ” 
  &&  “ (m1_v = (bn_v ÷ g_v )) ” 
  &&  “ (m2_v = (an_v ÷ g_v )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (num_pre + 1 )) ” 
  &&  “ (i = (Zlength (prefix))) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ (res <> 0) ” 
  &&  “ ((coef_Zlength (c1_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c2_low_level_spec)) = (num_pre + 1 )) ” 
  &&  “ ((coef_Zlength (c3)) = (num_pre + 1 )) ” 
  &&  “ (coef_pre_eq i c3 (list_Constraint (prefix)) ) ”
  &&  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array res (num_pre + 1 ) c3 )
.

(*----- Function generate_new_constraint_list -----*)

Definition generate_new_constraint_list_safety_wit_1 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (res: Z) (p1: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (acc: (@list Constraint)) (PreH1 : (safeExec ATrue (generate_new_constraint_list_loop (cur_num_pre) (l12) (l2_low_level_spec) (acc)) X_low_level_spec )) (PreH2 : (l1_low_level_spec = (app (l11) (l12)))) (PreH3 : (n_low_level_spec = (num_pre + 1 ))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < n_low_level_spec)) (PreH6 : (num_pre <= (INT_MAX - 1 ))) ,
  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n_low_level_spec acc )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constraint_list_safety_wit_2 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (res: Z) (p2: Z) (p1: Z) (l21: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (c1_cur: Constraint) (l22: (@list Constraint)) (acc: (@list Constraint)) (l12_tail: (@list Constraint)) (PreH1 : (safeExec ATrue (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l22) (acc))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (l1_low_level_spec = (app (l11) (l12)))) (PreH3 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH4 : (l2_low_level_spec = (app (l21) (l22)))) (PreH5 : (p1 <> 0)) (PreH6 : (n_low_level_spec = (num_pre + 1 ))) (PreH7 : (1 <= cur_num_pre)) (PreH8 : (cur_num_pre < n_low_level_spec)) (PreH9 : (num_pre <= (INT_MAX - 1 ))) ,
  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (InequList p2 n_low_level_spec l22 )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n_low_level_spec acc )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition generate_new_constraint_list_entail_wit_1 := 
(
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l_init_low_level_spec: (@list Constraint)) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (PreH1 : (safeExec ATrue (generate_new_constraint_list_prog (cur_num_pre) (l1_low_level_spec) (l2_low_level_spec) (l_init_low_level_spec)) X_low_level_spec )) (PreH2 : (n_low_level_spec = (num_pre + 1 ))) (PreH3 : (1 <= cur_num_pre)) (PreH4 : (cur_num_pre < n_low_level_spec)) (PreH5 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList r1_pre n_low_level_spec l1_low_level_spec )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList init_pre n_low_level_spec l_init_low_level_spec )
|--
  EX (l11: (@list Constraint))  (l12: (@list Constraint))  (acc: (@list Constraint)) ,
  “ (safeExec ATrue (generate_new_constraint_list_loop (cur_num_pre) (l12) (l2_low_level_spec) (acc)) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg r1_pre r1_pre n_low_level_spec l11 )
  **  (InequList r1_pre n_low_level_spec l12 )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList init_pre n_low_level_spec acc )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (l_init_low_level_spec: (@list Constraint)) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (PreH1 : (n_low_level_spec = (num_pre + 1 ))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < n_low_level_spec)) (PreH4 : (num_pre <= (INT_MAX - 1 ))) ,
  TT && emp 
|--
  “ (l1_low_level_spec = (app ((@nil Constraint)) (l1_low_level_spec))) ” 
  &&  “ (equiv (generate_new_constraint_list_prog (cur_num_pre) (l1_low_level_spec) (l2_low_level_spec) (l_init_low_level_spec)) (generate_new_constraint_list_loop (cur_num_pre) (l1_low_level_spec) (l2_low_level_spec) (l_init_low_level_spec)) ) ”
  &&  emp
).

Definition generate_new_constraint_list_entail_wit_1_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (PreH1 : (n_low_level_spec = (num_pre + 1 ))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < n_low_level_spec)) (PreH4 : (num_pre <= (INT_MAX - 1 ))) ,
  (l1_low_level_spec = (app ((@nil Constraint)) (l1_low_level_spec)))
.

Definition generate_new_constraint_list_entail_wit_1_split_goal_2 := 
forall (cur_num_pre: Z) (num_pre: Z) (l_init_low_level_spec: (@list Constraint)) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (PreH1 : (n_low_level_spec = (num_pre + 1 ))) (PreH2 : (1 <= cur_num_pre)) (PreH3 : (cur_num_pre < n_low_level_spec)) (PreH4 : (num_pre <= (INT_MAX - 1 ))) ,
  (equiv (generate_new_constraint_list_prog (cur_num_pre) (l1_low_level_spec) (l2_low_level_spec) (l_init_low_level_spec)) (generate_new_constraint_list_loop (cur_num_pre) (l1_low_level_spec) (l2_low_level_spec) (l_init_low_level_spec)) )
.

Definition generate_new_constraint_list_entail_wit_2 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (res: Z) (p1: Z) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (acc_2: (@list Constraint)) (PreH1 : (p1 <> 0)) (PreH2 : (safeExec ATrue (generate_new_constraint_list_loop (cur_num_pre) (l12_2) (l2_low_level_spec) (acc_2)) X_low_level_spec )) (PreH3 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH4 : (n_low_level_spec = (num_pre + 1 ))) (PreH5 : (1 <= cur_num_pre)) (PreH6 : (cur_num_pre < n_low_level_spec)) (PreH7 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg r1_pre p1 n_low_level_spec l11_2 )
  **  (InequList p1 n_low_level_spec l12_2 )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList res n_low_level_spec acc_2 )
|--
  EX (l21: (@list Constraint))  (l11: (@list Constraint))  (l12: (@list Constraint))  (c1_cur: Constraint)  (l22: (@list Constraint))  (acc: (@list Constraint))  (l12_tail: (@list Constraint)) ,
  “ (safeExec ATrue (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l22) (acc))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (l12 = (cons (c1_cur) (l12_tail))) ” 
  &&  “ (l2_low_level_spec = (app (l21) (l22))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
  **  (InequList_seg r2_pre r2_pre n_low_level_spec l21 )
  **  (InequList r2_pre n_low_level_spec l22 )
  **  (InequList res n_low_level_spec acc )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (p1: Z) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (acc_2: (@list Constraint)) (PreH1 : (p1 <> 0)) (PreH2 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH3 : (n_low_level_spec = (num_pre + 1 ))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < n_low_level_spec)) (PreH6 : (num_pre <= (INT_MAX - 1 ))) ,
  TT && emp 
|--
  EX (c1_cur: Constraint)  (l12_tail: (@list Constraint)) ,
  “ (equiv (generate_new_constraint_list_loop (cur_num_pre) (l12_2) (l2_low_level_spec) (acc_2)) (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l2_low_level_spec) (acc_2))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) ) ” 
  &&  “ (l12_2 = (cons (c1_cur) (l12_tail))) ” 
  &&  “ (l1_low_level_spec = (app (l11_2) ((cons (c1_cur) (l12_tail))))) ” 
  &&  “ (l2_low_level_spec = (app ((@nil Constraint)) (l2_low_level_spec))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  emp
).

Definition generate_new_constraint_list_entail_wit_3 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (res: Z) (p2: Z) (p1: Z) (l21_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (c1_cur_2: Constraint) (l22_2: (@list Constraint)) (acc_2: (@list Constraint)) (l12_tail_2: (@list Constraint)) (PreH1 : (p2 <> 0)) (PreH2 : (safeExec ATrue (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur_2) (l22_2) (acc_2))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail_2) (l2_low_level_spec)))) X_low_level_spec )) (PreH3 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH4 : (l12_2 = (cons (c1_cur_2) (l12_tail_2)))) (PreH5 : (l2_low_level_spec = (app (l21_2) (l22_2)))) (PreH6 : (p1 <> 0)) (PreH7 : (n_low_level_spec = (num_pre + 1 ))) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < n_low_level_spec)) (PreH10 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg r1_pre p1 n_low_level_spec l11_2 )
  **  (InequList p1 n_low_level_spec l12_2 )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21_2 )
  **  (InequList p2 n_low_level_spec l22_2 )
  **  (InequList res n_low_level_spec acc_2 )
|--
  EX (p2_next: Z)  (p1_next: Z)  (p2_coef: Z)  (p1_coef: Z)  (l21: (@list Constraint))  (l22: (@list Constraint))  (l11: (@list Constraint))  (l12: (@list Constraint))  (c2_cur: Constraint)  (c1_cur: Constraint)  (l22_tail: (@list Constraint))  (acc: (@list Constraint))  (l12_tail: (@list Constraint)) ,
  “ (safeExec ATrue (bind ((generate_new_constr_prog (cur_num_pre) (c1_cur) (c2_cur))) ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (l12 = (cons (c1_cur) (l12_tail))) ” 
  &&  “ (l2_low_level_spec = (app (l21) (l22))) ” 
  &&  “ (l22 = (cons (c2_cur) (l22_tail))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (mpz_coef_array p1_coef n_low_level_spec c1_cur )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (mpz_coef_array p2_coef n_low_level_spec c2_cur )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  (InequList res n_low_level_spec acc )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (p2: Z) (p1: Z) (l21_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (c1_cur_2: Constraint) (l22_2: (@list Constraint)) (acc_2: (@list Constraint)) (l12_tail_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (h: Z) (x_2: Constraint) (l0_2: (@list Constraint)) (h_2: Z) (PreH1 : (h_2 <> 0)) (PreH2 : (l22_2 = (cons (x_2) (l0_2)))) (PreH3 : (h <> 0)) (PreH4 : (l12_2 = (cons (x) (l0)))) (PreH5 : (p2 <> 0)) (PreH6 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH7 : (l12_2 = (cons (c1_cur_2) (l12_tail_2)))) (PreH8 : (l2_low_level_spec = (app (l21_2) (l22_2)))) (PreH9 : (p1 <> 0)) (PreH10 : (n_low_level_spec = (num_pre + 1 ))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < n_low_level_spec)) (PreH13 : (num_pre <= (INT_MAX - 1 ))) ,
  TT && emp 
|--
  “ (equiv (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur_2) (l22_2) (acc_2))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail_2) (l2_low_level_spec)))) (bind ((generate_new_constr_prog (cur_num_pre) (x) (x_2))) ((generate_new_constraints_after_one (cur_num_pre) (x) (l0_2) (acc_2) (l0) (l2_low_level_spec)))) ) ”
  &&  emp
).

Definition generate_new_constraint_list_entail_wit_3_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (p2: Z) (p1: Z) (l21_2: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (c1_cur_2: Constraint) (l22_2: (@list Constraint)) (acc_2: (@list Constraint)) (l12_tail_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (h: Z) (x_2: Constraint) (l0_2: (@list Constraint)) (h_2: Z) (PreH1 : (h_2 <> 0)) (PreH2 : (l22_2 = (cons (x_2) (l0_2)))) (PreH3 : (h <> 0)) (PreH4 : (l12_2 = (cons (x) (l0)))) (PreH5 : (p2 <> 0)) (PreH6 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH7 : (l12_2 = (cons (c1_cur_2) (l12_tail_2)))) (PreH8 : (l2_low_level_spec = (app (l21_2) (l22_2)))) (PreH9 : (p1 <> 0)) (PreH10 : (n_low_level_spec = (num_pre + 1 ))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < n_low_level_spec)) (PreH13 : (num_pre <= (INT_MAX - 1 ))) ,
  (equiv (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur_2) (l22_2) (acc_2))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail_2) (l2_low_level_spec)))) (bind ((generate_new_constr_prog (cur_num_pre) (x) (x_2))) ((generate_new_constraints_after_one (cur_num_pre) (x) (l0_2) (acc_2) (l0) (l2_low_level_spec)))) )
.

Definition generate_new_constraint_list_entail_wit_4 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (l12_tail_2: (@list Constraint)) (c1_cur_2: Constraint) (l21_2: (@list Constraint)) (l22_2: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc_2: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p1_next: Z) (p2_next: Z) (c3: Constraint) (retval_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (safeExec ATrue (applyf ((generate_new_constraints_after_one (cur_num_pre) (c1_cur_2) (l22_tail) (acc_2) (l12_tail_2) (l2_low_level_spec))) (c3)) X_low_level_spec )) (PreH4 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH5 : (l12_2 = (cons (c1_cur_2) (l12_tail_2)))) (PreH6 : (l2_low_level_spec = (app (l21_2) (l22_2)))) (PreH7 : (l22_2 = (cons (c2_cur) (l22_tail)))) (PreH8 : (p1 <> 0)) (PreH9 : (p2 <> 0)) (PreH10 : (p1_coef <> 0)) (PreH11 : (p2_coef <> 0)) (PreH12 : (n_low_level_spec = (num_pre + 1 ))) (PreH13 : (1 <= cur_num_pre)) (PreH14 : (cur_num_pre < n_low_level_spec)) (PreH15 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList retval (num_pre + 1 ) (cons (c3) (acc_2)) )
  **  (mpz_coef_array p1_coef (num_pre + 1 ) c1_cur_2 )
  **  (mpz_coef_array p2_coef (num_pre + 1 ) c2_cur )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11_2 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail_2 )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21_2 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
|--
  EX (l21: (@list Constraint))  (l11: (@list Constraint))  (l12: (@list Constraint))  (c1_cur: Constraint)  (l22: (@list Constraint))  (acc: (@list Constraint))  (l12_tail: (@list Constraint)) ,
  “ (safeExec ATrue (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l22) (acc))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (l12 = (cons (c1_cur) (l12_tail))) ” 
  &&  “ (l2_low_level_spec = (app (l21) (l22))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
  **  (InequList_seg r2_pre p2_next n_low_level_spec l21 )
  **  (InequList p2_next n_low_level_spec l22 )
  **  (InequList retval n_low_level_spec acc )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (l12_tail_2: (@list Constraint)) (c1_cur_2: Constraint) (l21_2: (@list Constraint)) (l22_2: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc_2: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p2_next: Z) (c3: Constraint) (retval_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH4 : (l12_2 = (cons (c1_cur_2) (l12_tail_2)))) (PreH5 : (l2_low_level_spec = (app (l21_2) (l22_2)))) (PreH6 : (l22_2 = (cons (c2_cur) (l22_tail)))) (PreH7 : (p1 <> 0)) (PreH8 : (p2 <> 0)) (PreH9 : (p1_coef <> 0)) (PreH10 : (p2_coef <> 0)) (PreH11 : (n_low_level_spec = (num_pre + 1 ))) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < n_low_level_spec)) (PreH14 : (num_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array p2_coef (num_pre + 1 ) c2_cur )
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r2_pre p2 n_low_level_spec l21_2 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
|--
  EX (l21: (@list Constraint)) ,
  “ ((num_pre + 1 ) = n_low_level_spec) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (equiv (applyf ((generate_new_constraints_after_one (cur_num_pre) (c1_cur_2) (l22_tail) (acc_2) (l12_tail_2) (l2_low_level_spec))) (c3)) (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur_2) (l22_tail) ((cons (c3) (acc_2))))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail_2) (l2_low_level_spec)))) ) ” 
  &&  “ ((num_pre + 1 ) = n_low_level_spec) ” 
  &&  “ (l1_low_level_spec = (app (l11_2) ((cons (c1_cur_2) (l12_tail_2))))) ” 
  &&  “ (l2_low_level_spec = (app (l21) (l22_tail))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg r2_pre p2_next n_low_level_spec l21 )
).

Definition generate_new_constraint_list_entail_wit_5 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (res: Z) (p2: Z) (p1: Z) (l21: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (c1_cur: Constraint) (l22: (@list Constraint)) (acc_2: (@list Constraint)) (l12_tail: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (l12_2 = (cons (x) (l0)))) (PreH3 : (p2 = 0)) (PreH4 : (safeExec ATrue (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l22) (acc_2))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) X_low_level_spec )) (PreH5 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH6 : (l12_2 = (cons (c1_cur) (l12_tail)))) (PreH7 : (l2_low_level_spec = (app (l21) (l22)))) (PreH8 : (p1 <> 0)) (PreH9 : (n_low_level_spec = (num_pre + 1 ))) (PreH10 : (1 <= cur_num_pre)) (PreH11 : (cur_num_pre < n_low_level_spec)) (PreH12 : (num_pre <= (INT_MAX - 1 ))) ,
  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  (mpz_coef_array h n_low_level_spec x )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11_2 )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (InequList p2 n_low_level_spec l22 )
  **  (InequList res n_low_level_spec acc_2 )
|--
  EX (l11: (@list Constraint))  (l12: (@list Constraint))  (acc: (@list Constraint)) ,
  “ (safeExec ATrue (generate_new_constraint_list_loop (cur_num_pre) (l12) (l2_low_level_spec) (acc)) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg r1_pre y n_low_level_spec l11 )
  **  (InequList y n_low_level_spec l12 )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList res n_low_level_spec acc )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (p2: Z) (p1: Z) (l21: (@list Constraint)) (l11_2: (@list Constraint)) (l12_2: (@list Constraint)) (c1_cur: Constraint) (l22: (@list Constraint)) (acc_2: (@list Constraint)) (l12_tail: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (l12_2 = (cons (x) (l0)))) (PreH3 : (p2 = 0)) (PreH4 : (l1_low_level_spec = (app (l11_2) (l12_2)))) (PreH5 : (l12_2 = (cons (c1_cur) (l12_tail)))) (PreH6 : (l2_low_level_spec = (app (l21) (l22)))) (PreH7 : (p1 <> 0)) (PreH8 : (n_low_level_spec = (num_pre + 1 ))) (PreH9 : (1 <= cur_num_pre)) (PreH10 : (cur_num_pre < n_low_level_spec)) (PreH11 : (num_pre <= (INT_MAX - 1 ))) ,
  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (mpz_coef_array h n_low_level_spec x )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11_2 )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (InequList p2 n_low_level_spec l22 )
|--
  EX (l11: (@list Constraint)) ,
  “ (equiv (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l22) (acc_2))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) (generate_new_constraint_list_loop (cur_num_pre) (l0) (l2_low_level_spec) (acc_2)) ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l0))) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg r1_pre y n_low_level_spec l11 )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
).

Definition generate_new_constraint_list_return_wit_1 := 
(
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (res: Z) (p1: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (acc: (@list Constraint)) (PreH1 : (p1 = 0)) (PreH2 : (safeExec ATrue (generate_new_constraint_list_loop (cur_num_pre) (l12) (l2_low_level_spec) (acc)) X_low_level_spec )) (PreH3 : (l1_low_level_spec = (app (l11) (l12)))) (PreH4 : (n_low_level_spec = (num_pre + 1 ))) (PreH5 : (1 <= cur_num_pre)) (PreH6 : (cur_num_pre < n_low_level_spec)) (PreH7 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList res n_low_level_spec acc )
|--
  EX (l3: (@list Constraint)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (InequList r1_pre n_low_level_spec l1_low_level_spec )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList res n_low_level_spec l3 )
) \/
(
forall (cur_num_pre: Z) (num_pre: Z) (r1_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (p1: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (acc: (@list Constraint)) (PreH1 : (p1 = 0)) (PreH2 : (l1_low_level_spec = (app (l11) (l12)))) (PreH3 : (n_low_level_spec = (num_pre + 1 ))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < n_low_level_spec)) (PreH6 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
|--
  “ (equiv (generate_new_constraint_list_loop (cur_num_pre) (l12) (l2_low_level_spec) (acc)) (return (acc)) ) ”
  &&  (InequList r1_pre n_low_level_spec l1_low_level_spec )
).

Definition generate_new_constraint_list_return_wit_1_split_goal_1 := 
forall (cur_num_pre: Z) (num_pre: Z) (r1_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (p1: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (acc: (@list Constraint)) (PreH1 : (p1 = 0)) (PreH2 : (l1_low_level_spec = (app (l11) (l12)))) (PreH3 : (n_low_level_spec = (num_pre + 1 ))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < n_low_level_spec)) (PreH6 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
|--
  “ (equiv (generate_new_constraint_list_loop (cur_num_pre) (l12) (l2_low_level_spec) (acc)) (return (acc)) ) ”
.

Definition generate_new_constraint_list_return_wit_1_split_goal_spatial := 
forall (cur_num_pre: Z) (num_pre: Z) (r1_pre: Z) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (p1: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (PreH1 : (p1 = 0)) (PreH2 : (l1_low_level_spec = (app (l11) (l12)))) (PreH3 : (n_low_level_spec = (num_pre + 1 ))) (PreH4 : (1 <= cur_num_pre)) (PreH5 : (cur_num_pre < n_low_level_spec)) (PreH6 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
|--
  (InequList r1_pre n_low_level_spec l1_low_level_spec )
.

Definition generate_new_constraint_list_partial_solve_wit_1_pure := 
(
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (l12_tail: (@list Constraint)) (c1_cur: Constraint) (l21: (@list Constraint)) (l22: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p1_next: Z) (p2_next: Z) (res: Z) (PreH1 : (safeExec ATrue (bind ((generate_new_constr_prog (cur_num_pre) (c1_cur) (c2_cur))) ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (l1_low_level_spec = (app (l11) (l12)))) (PreH3 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH4 : (l2_low_level_spec = (app (l21) (l22)))) (PreH5 : (l22 = (cons (c2_cur) (l22_tail)))) (PreH6 : (p1 <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (p1_coef <> 0)) (PreH9 : (p2_coef <> 0)) (PreH10 : (n_low_level_spec = (num_pre + 1 ))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < n_low_level_spec)) (PreH13 : (num_pre <= (INT_MAX - 1 ))) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (mpz_coef_array p1_coef n_low_level_spec c1_cur )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (mpz_coef_array p2_coef n_low_level_spec c2_cur )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n_low_level_spec acc )
|--
  “ (safeExec ATrue (bind ((generate_new_constr_prog (cur_num_pre) (c1_cur) (c2_cur))) ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (equiv (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) ) ”
) \/
(
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (l12_tail: (@list Constraint)) (c1_cur: Constraint) (l21: (@list Constraint)) (l22: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p1_next: Z) (p2_next: Z) (res: Z) (PreH1 : (num_pre <= INT_MAX)) (PreH2 : (cur_num_pre <= INT_MAX)) (PreH3 : (num_pre >= INT_MIN)) (PreH4 : (cur_num_pre >= INT_MIN)) (PreH5 : (l1_low_level_spec = (app (l11) (l12)))) (PreH6 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH7 : (l2_low_level_spec = (app (l21) (l22)))) (PreH8 : (l22 = (cons (c2_cur) (l22_tail)))) (PreH9 : (p1 <> 0)) (PreH10 : (p2 <> 0)) (PreH11 : (p1_coef <> 0)) (PreH12 : (p2_coef <> 0)) (PreH13 : (n_low_level_spec = (num_pre + 1 ))) (PreH14 : (1 <= cur_num_pre)) (PreH15 : (cur_num_pre < n_low_level_spec)) (PreH16 : (num_pre <= (INT_MAX - 1 ))) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (mpz_coef_array p1_coef n_low_level_spec c1_cur )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (mpz_coef_array p2_coef n_low_level_spec c2_cur )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n_low_level_spec acc )
|--
  “ (equiv (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) ) ”
).

Definition generate_new_constraint_list_partial_solve_wit_1_pure_split_goal_1 := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (l12_tail: (@list Constraint)) (c1_cur: Constraint) (l21: (@list Constraint)) (l22: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p1_next: Z) (p2_next: Z) (res: Z) (PreH1 : (num_pre <= INT_MAX)) (PreH2 : (cur_num_pre <= INT_MAX)) (PreH3 : (num_pre >= INT_MIN)) (PreH4 : (cur_num_pre >= INT_MIN)) (PreH5 : (l1_low_level_spec = (app (l11) (l12)))) (PreH6 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH7 : (l2_low_level_spec = (app (l21) (l22)))) (PreH8 : (l22 = (cons (c2_cur) (l22_tail)))) (PreH9 : (p1 <> 0)) (PreH10 : (p2 <> 0)) (PreH11 : (p1_coef <> 0)) (PreH12 : (p2_coef <> 0)) (PreH13 : (n_low_level_spec = (num_pre + 1 ))) (PreH14 : (1 <= cur_num_pre)) (PreH15 : (cur_num_pre < n_low_level_spec)) (PreH16 : (num_pre <= (INT_MAX - 1 ))) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (mpz_coef_array p1_coef n_low_level_spec c1_cur )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (mpz_coef_array p2_coef n_low_level_spec c2_cur )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n_low_level_spec acc )
|--
  “ (equiv (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) ) ”
.

Definition generate_new_constraint_list_partial_solve_wit_1_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (l12_tail: (@list Constraint)) (c1_cur: Constraint) (l21: (@list Constraint)) (l22: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p1_next: Z) (p2_next: Z) (res: Z) (PreH1 : (safeExec ATrue (bind ((generate_new_constr_prog (cur_num_pre) (c1_cur) (c2_cur))) ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (l1_low_level_spec = (app (l11) (l12)))) (PreH3 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH4 : (l2_low_level_spec = (app (l21) (l22)))) (PreH5 : (l22 = (cons (c2_cur) (l22_tail)))) (PreH6 : (p1 <> 0)) (PreH7 : (p2 <> 0)) (PreH8 : (p1_coef <> 0)) (PreH9 : (p2_coef <> 0)) (PreH10 : (n_low_level_spec = (num_pre + 1 ))) (PreH11 : (1 <= cur_num_pre)) (PreH12 : (cur_num_pre < n_low_level_spec)) (PreH13 : (num_pre <= (INT_MAX - 1 ))) ,
  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (mpz_coef_array p1_coef n_low_level_spec c1_cur )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (mpz_coef_array p2_coef n_low_level_spec c2_cur )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  (InequList res n_low_level_spec acc )
|--
  “ (safeExec ATrue (bind ((generate_new_constr_prog (cur_num_pre) (c1_cur) (c2_cur))) ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (equiv (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) (generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec)) ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (l12 = (cons (c1_cur) (l12_tail))) ” 
  &&  “ (l2_low_level_spec = (app (l21) (l22))) ” 
  &&  “ (l22 = (cons (c2_cur) (l22_tail))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (mpz_coef_array p1_coef (num_pre + 1 ) c1_cur )
  **  (mpz_coef_array p2_coef (num_pre + 1 ) c2_cur )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  (InequList res n_low_level_spec acc )
.

Definition generate_new_constraint_list_partial_solve_wit_1 := generate_new_constraint_list_partial_solve_wit_1_pure -> generate_new_constraint_list_partial_solve_wit_1_aux.

Definition generate_new_constraint_list_partial_solve_wit_2_pure := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (l12_tail: (@list Constraint)) (c1_cur: Constraint) (l21: (@list Constraint)) (l22: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p1_next: Z) (p2_next: Z) (res: Z) (c3: Constraint) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (safeExec ATrue (applyf ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec))) (c3)) X_low_level_spec )) (PreH3 : (l1_low_level_spec = (app (l11) (l12)))) (PreH4 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH5 : (l2_low_level_spec = (app (l21) (l22)))) (PreH6 : (l22 = (cons (c2_cur) (l22_tail)))) (PreH7 : (p1 <> 0)) (PreH8 : (p2 <> 0)) (PreH9 : (p1_coef <> 0)) (PreH10 : (p2_coef <> 0)) (PreH11 : (n_low_level_spec = (num_pre + 1 ))) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < n_low_level_spec)) (PreH14 : (num_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array p1_coef (num_pre + 1 ) c1_cur )
  **  (mpz_coef_array p2_coef (num_pre + 1 ) c2_cur )
  **  (mpz_coef_array retval (num_pre + 1 ) c3 )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval)
  **  ((( &( "cur_num" ) )) # Int  |-> cur_num_pre)
  **  ((( &( "p1" ) )) # Ptr  |-> p1)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  ((( &( "r1" ) )) # Ptr  |-> r1_pre)
  **  ((( &( "r2" ) )) # Ptr  |-> r2_pre)
  **  ((( &( "init" ) )) # Ptr  |-> init_pre)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (InequList res n_low_level_spec acc )
|--
  “ (retval <> 0) ”
.

Definition generate_new_constraint_list_partial_solve_wit_2_aux := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (l11: (@list Constraint)) (l12: (@list Constraint)) (l12_tail: (@list Constraint)) (c1_cur: Constraint) (l21: (@list Constraint)) (l22: (@list Constraint)) (l22_tail: (@list Constraint)) (c2_cur: Constraint) (acc: (@list Constraint)) (p1: Z) (p2: Z) (p1_coef: Z) (p2_coef: Z) (p1_next: Z) (p2_next: Z) (res: Z) (c3: Constraint) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (safeExec ATrue (applyf ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec))) (c3)) X_low_level_spec )) (PreH3 : (l1_low_level_spec = (app (l11) (l12)))) (PreH4 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH5 : (l2_low_level_spec = (app (l21) (l22)))) (PreH6 : (l22 = (cons (c2_cur) (l22_tail)))) (PreH7 : (p1 <> 0)) (PreH8 : (p2 <> 0)) (PreH9 : (p1_coef <> 0)) (PreH10 : (p2_coef <> 0)) (PreH11 : (n_low_level_spec = (num_pre + 1 ))) (PreH12 : (1 <= cur_num_pre)) (PreH13 : (cur_num_pre < n_low_level_spec)) (PreH14 : (num_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array p1_coef (num_pre + 1 ) c1_cur )
  **  (mpz_coef_array p2_coef (num_pre + 1 ) c2_cur )
  **  (mpz_coef_array retval (num_pre + 1 ) c3 )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
  **  (InequList res n_low_level_spec acc )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (applyf ((generate_new_constraints_after_one (cur_num_pre) (c1_cur) (l22_tail) (acc) (l12_tail) (l2_low_level_spec))) (c3)) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (l12 = (cons (c1_cur) (l12_tail))) ” 
  &&  “ (l2_low_level_spec = (app (l21) (l22))) ” 
  &&  “ (l22 = (cons (c2_cur) (l22_tail))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (p2 <> 0) ” 
  &&  “ (p1_coef <> 0) ” 
  &&  “ (p2_coef <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (mpz_coef_array retval (num_pre + 1 ) c3 )
  **  (InequList res (num_pre + 1 ) acc )
  **  (mpz_coef_array p1_coef (num_pre + 1 ) c1_cur )
  **  (mpz_coef_array p2_coef (num_pre + 1 ) c2_cur )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> p1_coef)
  **  ((&((p2)  # "InequList" ->ₛ "coef")) # Ptr  |-> p2_coef)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> p1_next)
  **  (InequList p1_next n_low_level_spec l12_tail )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  ((&((p2)  # "InequList" ->ₛ "next")) # Ptr  |-> p2_next)
  **  (InequList p2_next n_low_level_spec l22_tail )
.

Definition generate_new_constraint_list_partial_solve_wit_2 := generate_new_constraint_list_partial_solve_wit_2_pure -> generate_new_constraint_list_partial_solve_wit_2_aux.

Definition generate_new_constraint_list_partial_solve_wit_3 := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l2_low_level_spec: (@list Constraint)) (l1_low_level_spec: (@list Constraint)) (n_low_level_spec: Z) (res: Z) (p2: Z) (p1: Z) (l21: (@list Constraint)) (l11: (@list Constraint)) (l12: (@list Constraint)) (c1_cur: Constraint) (l22: (@list Constraint)) (acc: (@list Constraint)) (l12_tail: (@list Constraint)) (PreH1 : (p2 = 0)) (PreH2 : (safeExec ATrue (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l22) (acc))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) X_low_level_spec )) (PreH3 : (l1_low_level_spec = (app (l11) (l12)))) (PreH4 : (l12 = (cons (c1_cur) (l12_tail)))) (PreH5 : (l2_low_level_spec = (app (l21) (l22)))) (PreH6 : (p1 <> 0)) (PreH7 : (n_low_level_spec = (num_pre + 1 ))) (PreH8 : (1 <= cur_num_pre)) (PreH9 : (cur_num_pre < n_low_level_spec)) (PreH10 : (num_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList p1 n_low_level_spec l12 )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (InequList p2 n_low_level_spec l22 )
  **  (InequList res n_low_level_spec acc )
|--
  EX (h: Z)  (y: Z)  (l0: (@list Constraint))  (x: Constraint) ,
  “ (h <> 0) ” 
  &&  “ (l12 = (cons (x) (l0))) ” 
  &&  “ (p2 = 0) ” 
  &&  “ (safeExec ATrue (bind ((generate_new_constraints_inner_loop (cur_num_pre) (c1_cur) (l22) (acc))) ((generate_new_constraint_list_loop (cur_num_pre) (l12_tail) (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (app (l11) (l12))) ” 
  &&  “ (l12 = (cons (c1_cur) (l12_tail))) ” 
  &&  “ (l2_low_level_spec = (app (l21) (l22))) ” 
  &&  “ (p1 <> 0) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  ((&((p1)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList y n_low_level_spec l0 )
  **  (mpz_coef_array h n_low_level_spec x )
  **  ((&((p1)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList_seg r1_pre p1 n_low_level_spec l11 )
  **  (InequList_seg r2_pre p2 n_low_level_spec l21 )
  **  (InequList p2 n_low_level_spec l22 )
  **  (InequList res n_low_level_spec acc )
.

(*----- Function real_shadow -----*)

Definition real_shadow_safety_wit_1 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (safeExec ATrue (real_shadow_loop_prog (cnt) (l)) X_low_level_spec )) (PreH2 : (0 <= cnt)) (PreH3 : (cnt <= n_pre)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0 <> 0)) (PreH8 : (pr_pre <> 0)) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition real_shadow_safety_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH2 : (eliminate_xn cnt l b )) (PreH3 : (form_BP up lo re b )) (PreH4 : (cnt >= 1)) (PreH5 : (0 <= cnt)) (PreH6 : (cnt <= n_pre)) (PreH7 : (n_pre >= 1)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0 <> 0)) (PreH11 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain = 0)) (PreH2 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH3 : (eliminate_xn cnt l b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (cnt >= 1)) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= n_pre)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre <= (INT_MAX - 1 ))) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH4 : (eliminate_xn cnt l b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (cnt >= 1)) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= n_pre)) (PreH9 : (n_pre >= 1)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_5 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper <> 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH4 : (eliminate_xn cnt l b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (cnt >= 1)) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= n_pre)) (PreH9 : (n_pre >= 1)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain <> 0)) (PreH2 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH3 : (eliminate_xn cnt l b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (cnt >= 1)) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= n_pre)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre <= (INT_MAX - 1 ))) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain <> 0)) (PreH2 : (BP0_upper <> 0)) (PreH3 : (BP0_remain = 0)) (PreH4 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH5 : (eliminate_xn cnt l b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (cnt >= 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt <= n_pre)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ False ”
.

Definition real_shadow_safety_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain = 0)) (PreH2 : (BP0_remain <> 0)) (PreH3 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH4 : (eliminate_xn cnt l b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (cnt >= 1)) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= n_pre)) (PreH9 : (n_pre >= 1)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ False ”
.

Definition real_shadow_safety_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain = 0)) (PreH2 : (BP0_upper <> 0)) (PreH3 : (BP0_remain = 0)) (PreH4 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH5 : (eliminate_xn cnt l b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (cnt >= 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt <= n_pre)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_10 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition real_shadow_safety_wit_11 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ ((cnt - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt - 1 )) ”
.

Definition real_shadow_safety_wit_12 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> retval)
|--
  “ ((cnt - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt - 1 )) ”
.

Definition real_shadow_entail_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (l1_low_level_spec: (@list Constraint)) (p1_low_level_spec: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (safeExec ATrue (real_shadow_prog (n_pre) (l1_low_level_spec)) X_low_level_spec )) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec )
|--
  EX (l: (@list Constraint)) ,
  “ (safeExec ATrue (real_shadow_loop_prog (n_pre) (l)) X_low_level_spec ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1_low_level_spec: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) ,
  TT && emp 
|--
  “ (equiv (real_shadow_prog (n_pre) (l1_low_level_spec)) (real_shadow_loop_prog (n_pre) (l1_low_level_spec)) ) ”
  &&  emp
).

Definition real_shadow_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1_low_level_spec: (@list Constraint)) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) ,
  (equiv (real_shadow_prog (n_pre) (l1_low_level_spec)) (real_shadow_loop_prog (n_pre) (l1_low_level_spec)) )
.

Definition real_shadow_entail_wit_2_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l_2: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l_2 b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  EX (l: (@list Constraint)) ,
  “ (safeExec ATrue (real_shadow_loop_prog ((cnt - 1 )) (l)) X_low_level_spec ) ” 
  &&  “ (0 <= (cnt - 1 )) ” 
  &&  “ ((cnt - 1 ) <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList retval (n_pre + 1 ) l )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l_2: (@list Constraint)) (BP0_remain: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (BP0_remain <> 0)) (PreH4 : (BP0_remain <> 0)) (PreH5 : (eliminate_xn cnt l_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (cnt >= 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt <= n_pre)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) ,
  TT && emp 
|--
  “ (equiv (applyf ((real_shadow_after_generate (cnt))) (l3)) (real_shadow_loop_prog ((cnt - 1 )) (l3)) ) ”
  &&  emp
).

Definition real_shadow_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l_2: (@list Constraint)) (BP0_remain: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (BP0_remain <> 0)) (PreH4 : (BP0_remain <> 0)) (PreH5 : (eliminate_xn cnt l_2 b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (cnt >= 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt <= n_pre)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) ,
  (equiv (applyf ((real_shadow_after_generate (cnt))) (l3)) (real_shadow_loop_prog ((cnt - 1 )) (l3)) )
.

Definition real_shadow_entail_wit_2_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l_2: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l_2 b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  EX (l: (@list Constraint)) ,
  “ (safeExec ATrue (real_shadow_loop_prog ((cnt - 1 )) (l)) X_low_level_spec ) ” 
  &&  “ (0 <= (cnt - 1 )) ” 
  &&  “ ((cnt - 1 ) <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList retval (n_pre + 1 ) l )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l_2: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (BP0_lower <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (BP0_upper <> 0)) (PreH6 : (BP0_remain = 0)) (PreH7 : (eliminate_xn cnt l_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (cnt >= 1)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= n_pre)) (PreH12 : (n_pre >= 1)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre <= (INT_MAX - 1 ))) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) ,
  TT && emp 
|--
  “ (equiv (applyf ((real_shadow_after_generate (cnt))) (l3)) (real_shadow_loop_prog ((cnt - 1 )) (l3)) ) ”
  &&  emp
).

Definition real_shadow_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l_2: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (PreH1 : (generate_new_constraints cnt up lo l4 )) (PreH2 : (l3 = (app (l4) (re)))) (PreH3 : (BP0_lower <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (BP0_upper <> 0)) (PreH6 : (BP0_remain = 0)) (PreH7 : (eliminate_xn cnt l_2 b )) (PreH8 : (form_BP up lo re b )) (PreH9 : (cnt >= 1)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= n_pre)) (PreH12 : (n_pre >= 1)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre <= (INT_MAX - 1 ))) (PreH15 : (BP0 <> 0)) (PreH16 : (pr_pre <> 0)) ,
  (equiv (applyf ((real_shadow_after_generate (cnt))) (l3)) (real_shadow_loop_prog ((cnt - 1 )) (l3)) )
.

Definition real_shadow_return_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> 0)
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (safeExec ATrue (return (l2)) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (eliminate_xn cnt l b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (cnt >= 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt <= n_pre)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) ,
  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList BP0_remain (n_pre + 1 ) re )
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (return ((@nil Constraint))) ) ”
  &&  emp
).

Definition real_shadow_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (eliminate_xn cnt l b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (cnt >= 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt <= n_pre)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) ,
  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList BP0_remain (n_pre + 1 ) re )
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (return ((@nil Constraint))) ) ”
.

Definition real_shadow_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (eliminate_xn cnt l b )) (PreH6 : (form_BP up lo re b )) (PreH7 : (cnt >= 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt <= n_pre)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) (PreH13 : (BP0 <> 0)) (PreH14 : (pr_pre <> 0)) ,
  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList BP0_remain (n_pre + 1 ) re )
|--
  TT && emp 
.

Definition real_shadow_return_wit_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH4 : (eliminate_xn cnt l b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (cnt >= 1)) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= n_pre)) (PreH9 : (n_pre >= 1)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> 0)
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (safeExec ATrue (return (l2)) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (eliminate_xn cnt l b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (cnt >= 1)) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= n_pre)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre <= (INT_MAX - 1 ))) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) ,
  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_remain (n_pre + 1 ) re )
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (return ((@nil Constraint))) ) ”
  &&  emp
).

Definition real_shadow_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (eliminate_xn cnt l b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (cnt >= 1)) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= n_pre)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre <= (INT_MAX - 1 ))) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) ,
  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_remain (n_pre + 1 ) re )
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (return ((@nil Constraint))) ) ”
.

Definition real_shadow_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (eliminate_xn cnt l b )) (PreH4 : (form_BP up lo re b )) (PreH5 : (cnt >= 1)) (PreH6 : (0 <= cnt)) (PreH7 : (cnt <= n_pre)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (n_pre <= (INT_MAX - 1 ))) (PreH11 : (BP0 <> 0)) (PreH12 : (pr_pre <> 0)) ,
  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_remain (n_pre + 1 ) re )
|--
  TT && emp 
.

Definition real_shadow_return_wit_3 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt < 1)) (PreH2 : (safeExec ATrue (real_shadow_loop_prog (cnt) (l)) X_low_level_spec )) (PreH3 : (0 <= cnt)) (PreH4 : (cnt <= n_pre)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre <= (INT_MAX - 1 ))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> r)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r (n_pre + 1 ) l )
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (safeExec ATrue (return (l2)) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt < 1)) (PreH2 : (0 <= cnt)) (PreH3 : (cnt <= n_pre)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0 <> 0)) (PreH8 : (pr_pre <> 0)) ,
  TT && emp 
|--
  “ (equiv (real_shadow_loop_prog (cnt) (l)) (return (l)) ) ”
  &&  emp
).

Definition real_shadow_return_wit_3_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt < 1)) (PreH2 : (0 <= cnt)) (PreH3 : (cnt <= n_pre)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0 <> 0)) (PreH8 : (pr_pre <> 0)) ,
  (equiv (real_shadow_loop_prog (cnt) (l)) (return (l)) )
.

Definition real_shadow_partial_solve_wit_1_pure := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt >= 1)) (PreH2 : (safeExec ATrue (real_shadow_loop_prog (cnt) (l)) X_low_level_spec )) (PreH3 : (0 <= cnt)) (PreH4 : (cnt <= n_pre)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre <= (INT_MAX - 1 ))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l )
|--
  “ (safeExec ATrue (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) X_low_level_spec ) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (equiv (real_shadow_loop_prog (cnt) (l)) (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) ) ”
) \/
(
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (cnt >= 1)) (PreH5 : (0 <= cnt)) (PreH6 : (cnt <= n_pre)) (PreH7 : (n_pre >= 1)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0 <> 0)) (PreH11 : (pr_pre <> 0)) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l )
|--
  “ (equiv (real_shadow_loop_prog (cnt) (l)) (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) ) ” 
  &&  “ (equiv (real_shadow_loop_prog (cnt) (l)) (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) ) ”
).

Definition real_shadow_partial_solve_wit_1_pure_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (cnt >= 1)) (PreH5 : (0 <= cnt)) (PreH6 : (cnt <= n_pre)) (PreH7 : (n_pre >= 1)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0 <> 0)) (PreH11 : (pr_pre <> 0)) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l )
|--
  “ (equiv (real_shadow_loop_prog (cnt) (l)) (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) ) ”
.

Definition real_shadow_partial_solve_wit_1_pure_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (cnt >= 1)) (PreH5 : (0 <= cnt)) (PreH6 : (cnt <= n_pre)) (PreH7 : (n_pre >= 1)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) (PreH10 : (BP0 <> 0)) (PreH11 : (pr_pre <> 0)) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r)
  **  (InequList r (n_pre + 1 ) l )
|--
  “ (equiv (real_shadow_loop_prog (cnt) (l)) (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) ) ”
.

Definition real_shadow_partial_solve_wit_1_aux := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (PreH1 : (cnt >= 1)) (PreH2 : (safeExec ATrue (real_shadow_loop_prog (cnt) (l)) X_low_level_spec )) (PreH3 : (0 <= cnt)) (PreH4 : (cnt <= n_pre)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (n_pre <= (INT_MAX - 1 ))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r (n_pre + 1 ) l )
|--
  “ (safeExec ATrue (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) X_low_level_spec ) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (equiv (real_shadow_loop_prog (cnt) (l)) (bind ((eliminate_prog (cnt) (l))) ((real_shadow_after_eliminate (cnt)))) ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r (n_pre + 1 ) l )
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_1 := real_shadow_partial_solve_wit_1_pure -> real_shadow_partial_solve_wit_1_aux.

Definition real_shadow_partial_solve_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_upper = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH4 : (eliminate_xn cnt l b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (cnt >= 1)) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= n_pre)) (PreH9 : (n_pre >= 1)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (BP0_upper = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec ) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower = 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (BP0_upper <> 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec ) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_4_pure := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain <> 0)) (PreH2 : (BP0_remain <> 0)) (PreH3 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH4 : (eliminate_xn cnt l b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (cnt >= 1)) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= n_pre)) (PreH9 : (n_pre >= 1)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (safeExec ATrue (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) X_low_level_spec ) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
) \/
(
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
).

Definition real_shadow_partial_solve_wit_4_pure_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
.

Definition real_shadow_partial_solve_wit_4_pure_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (InequList_nth_pos cnt up ) ”
.

Definition real_shadow_partial_solve_wit_4_pure_split_goal_3 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (InequList_nth_neg cnt lo ) ”
.

Definition real_shadow_partial_solve_wit_4_pure_split_goal_4 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
.

Definition real_shadow_partial_solve_wit_4_aux := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_remain <> 0)) (PreH2 : (BP0_remain <> 0)) (PreH3 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH4 : (eliminate_xn cnt l b )) (PreH5 : (form_BP up lo re b )) (PreH6 : (cnt >= 1)) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= n_pre)) (PreH9 : (n_pre >= 1)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) (PreH12 : (BP0 <> 0)) (PreH13 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (safeExec ATrue (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) X_low_level_spec ) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ” 
  &&  “ (BP0_remain <> 0) ” 
  &&  “ (BP0_remain <> 0) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_4 := real_shadow_partial_solve_wit_4_pure -> real_shadow_partial_solve_wit_4_aux.

Definition real_shadow_partial_solve_wit_5_pure := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower <> 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (safeExec ATrue (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) X_low_level_spec ) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
) \/
(
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
).

Definition real_shadow_partial_solve_wit_5_pure_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
.

Definition real_shadow_partial_solve_wit_5_pure_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (InequList_nth_pos cnt up ) ”
.

Definition real_shadow_partial_solve_wit_5_pure_split_goal_3 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (InequList_nth_neg cnt lo ) ”
.

Definition real_shadow_partial_solve_wit_5_pure_split_goal_4 := 
forall (n_pre: Z) (pr_pre: Z) (p1_low_level_spec: Z) (BP0: Z) (r: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (cnt >= INT_MIN)) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  ((( &( "r" ) )) # Ptr  |-> r)
|--
  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ”
.

Definition real_shadow_partial_solve_wit_5_aux := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (PreH1 : (BP0_lower <> 0)) (PreH2 : (BP0_remain = 0)) (PreH3 : (BP0_upper <> 0)) (PreH4 : (BP0_remain = 0)) (PreH5 : (safeExec ATrue (applyf ((real_shadow_after_eliminate (cnt))) (b)) X_low_level_spec )) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper (n_pre + 1 ) up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (safeExec ATrue (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) X_low_level_spec ) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt < (n_pre + 1 )) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (InequList_nth_neg cnt lo ) ” 
  &&  “ (InequList_nth_pos cnt up ) ” 
  &&  “ (equiv (applyf ((real_shadow_after_eliminate (cnt))) (b)) (bind ((generate_new_constraint_list_prog (cnt) (up) (lo) (re))) ((real_shadow_after_generate (cnt)))) ) ” 
  &&  “ (BP0_lower <> 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (BP0_upper <> 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList BP0_remain (n_pre + 1 ) re )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_5 := real_shadow_partial_solve_wit_5_pure -> real_shadow_partial_solve_wit_5_aux.

Definition real_shadow_partial_solve_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec ) ” 
  &&  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (BP0_remain <> 0) ” 
  &&  “ (BP0_remain <> 0) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec ) ” 
  &&  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (BP0_lower <> 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (BP0_upper <> 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_upper (n_pre + 1 ) up )
  **  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_remain <> 0)) (PreH5 : (BP0_remain <> 0)) (PreH6 : (eliminate_xn cnt l b )) (PreH7 : (form_BP up lo re b )) (PreH8 : (cnt >= 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= n_pre)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (n_pre <= (INT_MAX - 1 ))) (PreH14 : (BP0 <> 0)) (PreH15 : (pr_pre <> 0)) ,
  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec ) ” 
  &&  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (BP0_remain <> 0) ” 
  &&  “ (BP0_remain <> 0) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

Definition real_shadow_partial_solve_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (p1_low_level_spec: Z) (BP0: Z) (cnt: Z) (l: (@list Constraint)) (BP0_remain: Z) (BP0_lower: Z) (BP0_upper: Z) (up: (@list Constraint)) (lo: (@list Constraint)) (re: (@list Constraint)) (b: BP) (l4: (@list Constraint)) (l3: (@list Constraint)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec )) (PreH2 : (generate_new_constraints cnt up lo l4 )) (PreH3 : (l3 = (app (l4) (re)))) (PreH4 : (BP0_lower <> 0)) (PreH5 : (BP0_remain = 0)) (PreH6 : (BP0_upper <> 0)) (PreH7 : (BP0_remain = 0)) (PreH8 : (eliminate_xn cnt l b )) (PreH9 : (form_BP up lo re b )) (PreH10 : (cnt >= 1)) (PreH11 : (0 <= cnt)) (PreH12 : (cnt <= n_pre)) (PreH13 : (n_pre >= 1)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre <= (INT_MAX - 1 ))) (PreH16 : (BP0 <> 0)) (PreH17 : (pr_pre <> 0)) ,
  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
|--
  “ (safeExec ATrue (applyf ((real_shadow_after_generate (cnt))) (l3)) X_low_level_spec ) ” 
  &&  “ (generate_new_constraints cnt up lo l4 ) ” 
  &&  “ (l3 = (app (l4) (re))) ” 
  &&  “ (BP0_lower <> 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (BP0_upper <> 0) ” 
  &&  “ (BP0_remain = 0) ” 
  &&  “ (eliminate_xn cnt l b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (cnt >= 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= n_pre) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ”
  &&  (InequList BP0_lower (n_pre + 1 ) lo )
  **  (InequList retval (n_pre + 1 ) l3 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
.

(*----- Function lia_deduction -----*)

Definition lia_deduction_safety_wit_1 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (PreH1 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH2 : (l2 = (app (l_done) (l_todo)))) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
  **  (InequList p (n_pre + 1 ) l_todo )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : ((coef_Znth (0) (x) (0)) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (h <> 0)) (PreH4 : (l_todo = (cons (x) (l0)))) (PreH5 : (p <> 0)) (PreH6 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH7 : (l2 = (app (l_done) (l_todo)))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : ((coef_Znth (0) (x) (0)) = 0)) (PreH2 : (retval = 0)) (PreH3 : (h <> 0)) (PreH4 : (l_todo = (cons (x) (l0)))) (PreH5 : (p <> 0)) (PreH6 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH7 : (l2 = (app (l_done) (l_todo)))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : ((coef_Znth (0) (x) (0)) > 0)) (PreH2 : (retval = 1)) (PreH3 : (h <> 0)) (PreH4 : (l_todo = (cons (x) (l0)))) (PreH5 : (p <> 0)) (PreH6 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH7 : (l2 = (app (l_done) (l_todo)))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_safety_wit_5 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : ((coef_Znth (0) (x) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (h <> 0)) (PreH5 : (l_todo = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH8 : (l2 = (app (l_done) (l_todo)))) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
|--
  “ False ”
.

Definition lia_deduction_safety_wit_6 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : ((coef_Znth (0) (x) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (h <> 0)) (PreH5 : (l_todo = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH8 : (l2 = (app (l_done) (l_todo)))) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
|--
  “ False ”
.

Definition lia_deduction_safety_wit_7 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (h <> 0)) (PreH5 : (l_todo = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH8 : (l2 = (app (l_done) (l_todo)))) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
|--
  “ False ”
.

Definition lia_deduction_safety_wit_8 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (l2: (@list Constraint)) (p2: Z) (p: Z) (PreH1 : (safeExec ATrue (return ((makepair (1) (l2)))) X_low_level_spec )) (PreH2 : (p <> 0)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lia_deduction_safety_wit_9 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (PreH1 : (p = 0)) (PreH2 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH3 : (l2 = (app (l_done) (l_todo)))) (PreH4 : (BP0 <> 0)) (PreH5 : (pr_pre <> 0)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= (INT_MAX - 1 ))) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
  **  (InequList p (n_pre + 1 ) l_todo )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lia_deduction_entail_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (p2: Z) (l2_2: (@list Constraint)) (PreH1 : (safeExec ATrue (applyf (lia_deduction_after_real_shadow) (l2_2)) X_low_level_spec )) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2_2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (p2_2: Z)  (l_done: (@list Constraint))  (l2: (@list Constraint))  (l_todo: (@list Constraint)) ,
  “ (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec ) ” 
  &&  “ (l2 = (app (l_done) (l_todo))) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2_2 p2 (n_pre + 1 ) l_done )
  **  (InequList p2 (n_pre + 1 ) l_todo )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (p2: Z) (l2_2: (@list Constraint)) (PreH1 : (BP0 <> 0)) (PreH2 : (pr_pre <> 0)) (PreH3 : (n_pre >= 1)) (PreH4 : (n_pre <= (INT_MAX - 1 ))) (PreH5 : (BP0_upper = 0)) (PreH6 : (BP0_lower = 0)) (PreH7 : (BP0_remain = 0)) ,
  TT && emp 
|--
  EX (l_done: (@list Constraint)) ,
  “ (equiv (applyf (lia_deduction_after_real_shadow) (l2_2)) (lia_deduction_scan_from_false ((app (l_done) (l2_2))) (l2_2)) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg p2 p2 (n_pre + 1 ) l_done )
).

Definition lia_deduction_entail_wit_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2_2: Z) (l_done: (@list Constraint)) (l2_2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (h <> 0)) (PreH5 : (l_todo = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (safeExec ATrue (lia_deduction_scan_from_false (l2_2) (l_todo)) X_low_level_spec )) (PreH8 : (l2_2 = (app (l_done) (l_todo)))) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2_2 p (n_pre + 1 ) l_done )
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (safeExec ATrue (return ((makepair (1) (l2)))) X_low_level_spec ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList p2 (n_pre + 1 ) l2 )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (p: Z) (p2_2: Z) (l_done: (@list Constraint)) (l2_2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : ((coef_Znth (0) (x) (0)) > 0)) (PreH3 : (retval = 1)) (PreH4 : (h <> 0)) (PreH5 : (l_todo = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (l2_2 = (app (l_done) (l_todo)))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList_seg p2_2 p (n_pre + 1 ) l_done )
|--
  EX (l2: (@list Constraint)) ,
  “ (equiv (lia_deduction_scan_from_false (l2_2) (l_todo)) (return ((makepair (1) (l2)))) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  (InequList p2_2 (n_pre + 1 ) l2 )
).

Definition lia_deduction_entail_wit_3_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2_2: Z) (l_done_2: (@list Constraint)) (l2_2: (@list Constraint)) (l_todo_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : ((coef_Znth (0) (x) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (h <> 0)) (PreH5 : (l_todo_2 = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (safeExec ATrue (lia_deduction_scan_from_false (l2_2) (l_todo_2)) X_low_level_spec )) (PreH8 : (l2_2 = (app (l_done_2) (l_todo_2)))) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2_2 p (n_pre + 1 ) l_done_2 )
|--
  EX (p2: Z)  (l_done: (@list Constraint))  (l2: (@list Constraint))  (l_todo: (@list Constraint)) ,
  “ (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec ) ” 
  &&  “ (l2 = (app (l_done) (l_todo))) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2 y (n_pre + 1 ) l_done )
  **  (InequList y (n_pre + 1 ) l_todo )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (p: Z) (p2_2: Z) (l_done_2: (@list Constraint)) (l2_2: (@list Constraint)) (l_todo_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : ((coef_Znth (0) (x) (0)) < 0)) (PreH3 : (retval = (-1))) (PreH4 : (h <> 0)) (PreH5 : (l_todo_2 = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (l2_2 = (app (l_done_2) (l_todo_2)))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList_seg p2_2 p (n_pre + 1 ) l_done_2 )
|--
  EX (l_done: (@list Constraint)) ,
  “ (equiv (lia_deduction_scan_from_false (l2_2) (l_todo_2)) (lia_deduction_scan_from_false ((app (l_done) (l0))) (l0)) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg p2_2 y (n_pre + 1 ) l_done )
).

Definition lia_deduction_entail_wit_3_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2_2: Z) (l_done_2: (@list Constraint)) (l2_2: (@list Constraint)) (l_todo_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : ((coef_Znth (0) (x) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (h <> 0)) (PreH5 : (l_todo_2 = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (safeExec ATrue (lia_deduction_scan_from_false (l2_2) (l_todo_2)) X_low_level_spec )) (PreH8 : (l2_2 = (app (l_done_2) (l_todo_2)))) (PreH9 : (BP0 <> 0)) (PreH10 : (pr_pre <> 0)) (PreH11 : (n_pre >= 1)) (PreH12 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2_2 p (n_pre + 1 ) l_done_2 )
|--
  EX (p2: Z)  (l_done: (@list Constraint))  (l2: (@list Constraint))  (l_todo: (@list Constraint)) ,
  “ (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec ) ” 
  &&  “ (l2 = (app (l_done) (l_todo))) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2 y (n_pre + 1 ) l_done )
  **  (InequList y (n_pre + 1 ) l_todo )
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (p: Z) (p2_2: Z) (l_done_2: (@list Constraint)) (l2_2: (@list Constraint)) (l_todo_2: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : ((coef_Znth (0) (x) (0)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (h <> 0)) (PreH5 : (l_todo_2 = (cons (x) (l0)))) (PreH6 : (p <> 0)) (PreH7 : (l2_2 = (app (l_done_2) (l_todo_2)))) (PreH8 : (BP0 <> 0)) (PreH9 : (pr_pre <> 0)) (PreH10 : (n_pre >= 1)) (PreH11 : (n_pre <= (INT_MAX - 1 ))) ,
  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (InequList_seg p2_2 p (n_pre + 1 ) l_done_2 )
|--
  EX (l_done: (@list Constraint)) ,
  “ (equiv (lia_deduction_scan_from_false (l2_2) (l_todo_2)) (lia_deduction_scan_from_false ((app (l_done) (l0))) (l0)) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  (InequList_seg p2_2 y (n_pre + 1 ) l_done )
).

Definition lia_deduction_return_wit_1 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2_3: Z) (l_done: (@list Constraint)) (l2_3: (@list Constraint)) (l_todo: (@list Constraint)) (PreH1 : (p = 0)) (PreH2 : (safeExec ATrue (lia_deduction_scan_from_false (l2_3) (l_todo)) X_low_level_spec )) (PreH3 : (l2_3 = (app (l_done) (l_todo)))) (PreH4 : (BP0 <> 0)) (PreH5 : (pr_pre <> 0)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= (INT_MAX - 1 ))) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_3)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2_3 p (n_pre + 1 ) l_done )
  **  (InequList p (n_pre + 1 ) l_todo )
|--
  EX (p2_2: Z)  (l2_2: (@list Constraint)) ,
  “ (0 = 0) ” 
  &&  “ (safeExec ATrue (return ((makepair (0) (l2_2)))) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  (InequList p2_2 (n_pre + 1 ) l2_2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (p: Z) (p2_3: Z) (l_done: (@list Constraint)) (l2_3: (@list Constraint)) (l_todo: (@list Constraint)) (PreH1 : (p = 0)) (PreH2 : (l2_3 = (app (l_done) (l_todo)))) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) ,
  (InequList_seg p2_3 p (n_pre + 1 ) l_done )
  **  (InequList p (n_pre + 1 ) l_todo )
|--
  EX (l2_2: (@list Constraint)) ,
  “ (equiv (lia_deduction_scan_from_false (l2_3) (l_todo)) (return ((makepair (0) (l2_2)))) ) ”
  &&  (InequList p2_3 (n_pre + 1 ) l2_2 )
).

Definition lia_deduction_return_wit_2 := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (l2_3: (@list Constraint)) (p2_3: Z) (p: Z) (PreH1 : (safeExec ATrue (return ((makepair (1) (l2_3)))) X_low_level_spec )) (PreH2 : (p <> 0)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_3)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
|--
  EX (p2: Z)  (l2: (@list Constraint)) ,
  “ (1 = 1) ” 
  &&  “ (safeExec ATrue (return ((makepair (1) (l2)))) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
) \/
(
forall (n_pre: Z) (pr_pre: Z) (BP0: Z) (l2_3: (@list Constraint)) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) ,
  TT && emp 
|--
  EX (l2: (@list Constraint)) ,
  “ (@equiv ((@ MonadErr.M  unit (Z * (@list Constraint)))) _ ((return ((makepair (1) (l2_3))))) ((return ((makepair (1) (l2)))))) ”
  &&  emp
).

Definition lia_deduction_partial_solve_wit_1_pure := 
(
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (l1_low_level_spec: (@list Constraint)) (p1_low_level_spec: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (safeExec ATrue (lia_deduction_prog (n_pre) (l1_low_level_spec)) X_low_level_spec )) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec )
|--
  “ (safeExec ATrue (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) X_low_level_spec ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (equiv (lia_deduction_prog (n_pre) (l1_low_level_spec)) (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) ) ”
) \/
(
forall (n_pre: Z) (pr_pre: Z) (l1_low_level_spec: (@list Constraint)) (p1_low_level_spec: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec )
|--
  “ (equiv (lia_deduction_prog (n_pre) (l1_low_level_spec)) (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) ) ” 
  &&  “ (equiv (lia_deduction_prog (n_pre) (l1_low_level_spec)) (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) ) ”
).

Definition lia_deduction_partial_solve_wit_1_pure_split_goal_1 := 
forall (n_pre: Z) (pr_pre: Z) (l1_low_level_spec: (@list Constraint)) (p1_low_level_spec: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec )
|--
  “ (equiv (lia_deduction_prog (n_pre) (l1_low_level_spec)) (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) ) ”
.

Definition lia_deduction_partial_solve_wit_1_pure_split_goal_2 := 
forall (n_pre: Z) (pr_pre: Z) (l1_low_level_spec: (@list Constraint)) (p1_low_level_spec: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) (PreH7 : (BP0_upper = 0)) (PreH8 : (BP0_lower = 0)) (PreH9 : (BP0_remain = 0)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "pr" ) )) # Ptr  |-> pr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec )
|--
  “ (equiv (lia_deduction_prog (n_pre) (l1_low_level_spec)) (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) ) ”
.

Definition lia_deduction_partial_solve_wit_1_aux := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (l1_low_level_spec: (@list Constraint)) (p1_low_level_spec: Z) (BP0: Z) (BP0_upper: Z) (BP0_lower: Z) (BP0_remain: Z) (PreH1 : (safeExec ATrue (lia_deduction_prog (n_pre) (l1_low_level_spec)) X_low_level_spec )) (PreH2 : (BP0 <> 0)) (PreH3 : (pr_pre <> 0)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= (INT_MAX - 1 ))) (PreH6 : (BP0_upper = 0)) (PreH7 : (BP0_lower = 0)) (PreH8 : (BP0_remain = 0)) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec )
|--
  “ (safeExec ATrue (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) X_low_level_spec ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (equiv (lia_deduction_prog (n_pre) (l1_low_level_spec)) (bind ((real_shadow_prog (n_pre) (l1_low_level_spec))) (lia_deduction_after_real_shadow)) ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> 0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> 0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> 0)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec )
.

Definition lia_deduction_partial_solve_wit_1 := lia_deduction_partial_solve_wit_1_pure -> lia_deduction_partial_solve_wit_1_aux.

Definition lia_deduction_partial_solve_wit_2 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (PreH1 : (p <> 0)) (PreH2 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH3 : (l2 = (app (l_done) (l_todo)))) (PreH4 : (BP0 <> 0)) (PreH5 : (pr_pre <> 0)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= (INT_MAX - 1 ))) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
  **  (InequList p (n_pre + 1 ) l_todo )
|--
  EX (h: Z)  (y: Z)  (l0: (@list Constraint))  (x: Constraint) ,
  “ (h <> 0) ” 
  &&  “ (l_todo = (cons (x) (l0))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec ) ” 
  &&  “ (l2 = (app (l_done) (l_todo))) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
.

Definition lia_deduction_partial_solve_wit_3 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (p: Z) (p2: Z) (l_done: (@list Constraint)) (l2: (@list Constraint)) (l_todo: (@list Constraint)) (x: Constraint) (l0: (@list Constraint)) (y: Z) (h: Z) (PreH1 : (h <> 0)) (PreH2 : (l_todo = (cons (x) (l0)))) (PreH3 : (p <> 0)) (PreH4 : (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec )) (PreH5 : (l2 = (app (l_done) (l_todo)))) (PreH6 : (BP0 <> 0)) (PreH7 : (pr_pre <> 0)) (PreH8 : (n_pre >= 1)) (PreH9 : (n_pre <= (INT_MAX - 1 ))) ,
  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  (mpz_coef_array h (n_pre + 1 ) x )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
|--
  “ (h <> 0) ” 
  &&  “ (l_todo = (cons (x) (l0))) ” 
  &&  “ (p <> 0) ” 
  &&  “ (safeExec ATrue (lia_deduction_scan_from_false (l2) (l_todo)) X_low_level_spec ) ” 
  &&  “ (l2 = (app (l_done) (l_todo))) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  (store_Z h (coef_Znth (0) (x) (0)) )
  **  (mpz_coef_array_missing_i_rec h 0 0 (n_pre + 1 ) x )
  **  ((&((p)  # "InequList" ->ₛ "coef")) # Ptr  |-> h)
  **  (InequList y (n_pre + 1 ) l0 )
  **  ((&((p)  # "InequList" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList_seg p2 p (n_pre + 1 ) l_done )
.

Definition lia_deduction_partial_solve_wit_4 := 
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0: Z) (l2: (@list Constraint)) (p2: Z) (p: Z) (PreH1 : (safeExec ATrue (return ((makepair (1) (l2)))) X_low_level_spec )) (PreH2 : (p <> 0)) (PreH3 : (BP0 <> 0)) (PreH4 : (pr_pre <> 0)) (PreH5 : (n_pre >= 1)) (PreH6 : (n_pre <= (INT_MAX - 1 ))) ,
  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList p2 (n_pre + 1 ) l2 )
|--
  “ (safeExec ATrue (return ((makepair (1) (l2)))) X_low_level_spec ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ”
  &&  (InequList p2 (n_pre + 1 ) l2 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
.

Definition lia_deduction_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((Z * (@list Constraint)) -> (@ MonadErr.M  unit B))) (l1_low_level_spec_aux: (@list Constraint)) (p1_low_level_spec_aux: Z) (BP0: Z) ,
  EX BP0_remain BP0_lower BP0_upper,
  “ (safeExec ATrue (bind ((lia_deduction_prog (n_pre) (l1_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec_aux)
  **  (InequList p1_low_level_spec_aux (n_pre + 1 ) l1_low_level_spec_aux )
|--
EX (p1_low_level_spec: Z) (l1_low_level_spec: (@list Constraint)) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0_2: Z) ,
  (EX BP0_remain_2 BP0_lower_2 BP0_upper_2,
  “ (safeExec ATrue (lia_deduction_prog (n_pre) (l1_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (BP0_2 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper_2 = 0) ” 
  &&  “ (BP0_lower_2 = 0) ” 
  &&  “ (BP0_remain_2 = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec ))
  **
  (((EX p2_3 l2_3 retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (safeExec ATrue (return ((makepair (1) (l2_3)))) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((pr_pre) # Ptr  |-> p2_3)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX p2_4 l2_4 retval_2,
  “ (retval_2 = 0) ” 
  &&  “ (safeExec ATrue (return ((makepair (0) (l2_4)))) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((pr_pre) # Ptr  |-> p2_4)
  **  (InequList p2_4 (n_pre + 1 ) l2_4 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)))
  -*
  ((EX p2 l2 retval,
  “ (retval = 1) ” 
  &&  “ (safeExec ATrue (applyf (c_low_level_spec_aux) ((makepair (1) (l2)))) X_low_level_spec_aux ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX p2_2 l2_2 retval,
  “ (retval = 0) ” 
  &&  “ (safeExec ATrue (applyf (c_low_level_spec_aux) ((makepair (0) (l2_2)))) X_low_level_spec_aux ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  (InequList p2_2 (n_pre + 1 ) l2_2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))))
.

Definition lia_deduction_derive_high_level_spec_by_low_level_spec := 
forall (n_pre: Z) (pr_pre: Z) (l1_high_level_spec: (@list Constraint)) (p1_high_level_spec: Z) ,
  EX BP0_remain BP0_lower BP0_upper BP0,
  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_high_level_spec)
  **  (InequList p1_high_level_spec (n_pre + 1 ) l1_high_level_spec )
|--
EX (p1_low_level_spec: Z) (l1_low_level_spec: (@list Constraint)) (X_low_level_spec: ((Z * (@list Constraint)) -> (unit -> Prop))) (BP0_4: Z) ,
  (EX BP0_remain_2 BP0_lower_2 BP0_upper_2,
  “ (safeExec ATrue (lia_deduction_prog (n_pre) (l1_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (BP0_4 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper_2 = 0) ” 
  &&  “ (BP0_lower_2 = 0) ” 
  &&  “ (BP0_remain_2 = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_4)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec ))
  **
  (((EX p2_3 l2_2 retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (safeExec ATrue (return ((makepair (1) (l2_2)))) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_4)
  **  ((pr_pre) # Ptr  |-> p2_3)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX p2_4 l2_3 retval_2,
  “ (retval_2 = 0) ” 
  &&  “ (safeExec ATrue (return ((makepair (0) (l2_3)))) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_4)
  **  ((pr_pre) # Ptr  |-> p2_4)
  **  (InequList p2_4 (n_pre + 1 ) l2_3 )
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_4)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)))
  -*
  ((EX BP0_2 p2 retval,
  “ (retval = 1) ” 
  &&  “ (UNSAT l1_high_level_spec ) ”
  &&  ((pr_pre) # Ptr  |-> p2)
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  ||
  (EX BP0_3 p2_2 l2 retval,
  “ (retval = 0) ” 
  &&  “ (LP_implies l1_high_level_spec l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ”
  &&  ((pr_pre) # Ptr  |-> p2_2)
  **  (InequList p2_2 (n_pre + 1 ) l2 )
  **  ((( &( "BP0" ) )) # Ptr  |-> BP0_3)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_3)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))))
.

Definition real_shadow_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (n_pre: Z) (pr_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Constraint) -> (@ MonadErr.M  unit B))) (l1_low_level_spec_aux: (@list Constraint)) (p1_low_level_spec_aux: Z) (BP0: Z) ,
  EX BP0_remain BP0_lower BP0_upper,
  “ (safeExec ATrue (bind ((real_shadow_prog (n_pre) (l1_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ” 
  &&  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec_aux)
  **  (InequList p1_low_level_spec_aux (n_pre + 1 ) l1_low_level_spec_aux )
|--
EX (p1_low_level_spec: Z) (l1_low_level_spec: (@list Constraint)) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (BP0_2: Z) ,
  (EX BP0_remain_2 BP0_lower_2 BP0_upper_2,
  “ (safeExec ATrue (real_shadow_prog (n_pre) (l1_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (BP0_2 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper_2 = 0) ” 
  &&  “ (BP0_lower_2 = 0) ” 
  &&  “ (BP0_remain_2 = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec ))
  **
  ((EX p2_2 l2_2,
  “ (safeExec ATrue (return (l2_2)) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  (InequList p2_2 (n_pre + 1 ) l2_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  -*
  (EX p2 l2,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l2)) X_low_level_spec_aux ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)))
.

Definition real_shadow_derive_high_level_spec_by_low_level_spec := 
forall (n_pre: Z) (pr_pre: Z) (l1_high_level_spec: (@list Constraint)) (p1_high_level_spec: Z) (BP0: Z) ,
  EX BP0_remain BP0_lower BP0_upper,
  “ (BP0 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper = 0) ” 
  &&  “ (BP0_lower = 0) ” 
  &&  “ (BP0_remain = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  ((pr_pre) # Ptr  |-> p1_high_level_spec)
  **  (InequList p1_high_level_spec (n_pre + 1 ) l1_high_level_spec )
|--
EX (p1_low_level_spec: Z) (l1_low_level_spec: (@list Constraint)) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) (BP0_2: Z) ,
  (EX BP0_remain_2 BP0_lower_2 BP0_upper_2,
  “ (safeExec ATrue (real_shadow_prog (n_pre) (l1_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (BP0_2 <> 0) ” 
  &&  “ (pr_pre <> 0) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= (INT_MAX - 1 )) ” 
  &&  “ (BP0_upper_2 = 0) ” 
  &&  “ (BP0_lower_2 = 0) ” 
  &&  “ (BP0_remain_2 = 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  ((pr_pre) # Ptr  |-> p1_low_level_spec)
  **  (InequList p1_low_level_spec (n_pre + 1 ) l1_low_level_spec ))
  **
  ((EX p2_2 l2_2,
  “ (safeExec ATrue (return (l2_2)) X_low_level_spec ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((pr_pre) # Ptr  |-> p2_2)
  **  (InequList p2_2 (n_pre + 1 ) l2_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_))
  -*
  (EX p2 l2,
  “ (LP_implies l1_high_level_spec l2 ) ” 
  &&  “ (InequList_Zeros l2 1 (n_pre + 1 ) ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((pr_pre) # Ptr  |-> p2)
  **  (InequList p2 (n_pre + 1 ) l2 )
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)))
.

Definition generate_new_constraint_list_derive_low_level_spec_aux_with_rel_by_low_level_spec := 
forall (B: Type) ,
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec_aux_with_rel: (B -> (unit -> Prop))) (c_low_level_spec_aux_with_rel: ((@list Constraint) -> (@ MonadErr.M  unit B))) (l_init_low_level_spec_aux_with_rel: (@list Constraint)) (l2_low_level_spec_aux_with_rel: (@list Constraint)) (l1_low_level_spec_aux_with_rel: (@list Constraint)) (n_low_level_spec_aux_with_rel: Z) ,
  “ (safeExec ATrue (bind ((generate_new_constraint_list_prog (cur_num_pre) (l1_low_level_spec_aux_with_rel) (l2_low_level_spec_aux_with_rel) (l_init_low_level_spec_aux_with_rel))) (c_low_level_spec_aux_with_rel)) X_low_level_spec_aux_with_rel ) ” 
  &&  “ (n_low_level_spec_aux_with_rel = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec_aux_with_rel) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1_low_level_spec_aux_with_rel ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2_low_level_spec_aux_with_rel ) ”
  &&  (InequList r1_pre n_low_level_spec_aux_with_rel l1_low_level_spec_aux_with_rel )
  **  (InequList r2_pre n_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel )
  **  (InequList init_pre n_low_level_spec_aux_with_rel l_init_low_level_spec_aux_with_rel )
|--
EX (n_low_level_spec: Z) (l1_low_level_spec: (@list Constraint)) (l2_low_level_spec: (@list Constraint)) (l_init_low_level_spec: (@list Constraint)) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (generate_new_constraint_list_prog (cur_num_pre) (l1_low_level_spec) (l2_low_level_spec) (l_init_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList r1_pre n_low_level_spec l1_low_level_spec )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList init_pre n_low_level_spec l_init_low_level_spec ))
  **
  ((EX l3_2 retval_2,
  “ (safeExec ATrue (return (l3_2)) X_low_level_spec ) ”
  &&  (InequList r1_pre n_low_level_spec l1_low_level_spec )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList retval_2 n_low_level_spec l3_2 ))
  -*
  (EX l4 l3 retval,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux_with_rel) (l3)) X_low_level_spec_aux_with_rel ) ” 
  &&  “ (generate_new_constraints cur_num_pre l1_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init_low_level_spec_aux_with_rel))) ”
  &&  (InequList r1_pre n_low_level_spec_aux_with_rel l1_low_level_spec_aux_with_rel )
  **  (InequList r2_pre n_low_level_spec_aux_with_rel l2_low_level_spec_aux_with_rel )
  **  (InequList retval n_low_level_spec_aux_with_rel l3 )))
.

Definition generate_new_constraint_list_derive_high_level_spec_by_low_level_spec := 
forall (init_pre: Z) (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (l_init_high_level_spec: (@list Constraint)) (l2_high_level_spec: (@list Constraint)) (l1_high_level_spec: (@list Constraint)) (n_high_level_spec: Z) ,
  “ (n_high_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_high_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (InequList_nth_pos cur_num_pre l1_high_level_spec ) ” 
  &&  “ (InequList_nth_neg cur_num_pre l2_high_level_spec ) ”
  &&  (InequList r1_pre n_high_level_spec l1_high_level_spec )
  **  (InequList r2_pre n_high_level_spec l2_high_level_spec )
  **  (InequList init_pre n_high_level_spec l_init_high_level_spec )
|--
EX (n_low_level_spec: Z) (l1_low_level_spec: (@list Constraint)) (l2_low_level_spec: (@list Constraint)) (l_init_low_level_spec: (@list Constraint)) (X_low_level_spec: ((@list Constraint) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (generate_new_constraint_list_prog (cur_num_pre) (l1_low_level_spec) (l2_low_level_spec) (l_init_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec = (num_pre + 1 )) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < n_low_level_spec) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ”
  &&  (InequList r1_pre n_low_level_spec l1_low_level_spec )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList init_pre n_low_level_spec l_init_low_level_spec ))
  **
  ((EX l3_2 retval_2,
  “ (safeExec ATrue (return (l3_2)) X_low_level_spec ) ”
  &&  (InequList r1_pre n_low_level_spec l1_low_level_spec )
  **  (InequList r2_pre n_low_level_spec l2_low_level_spec )
  **  (InequList retval_2 n_low_level_spec l3_2 ))
  -*
  (EX l3 l4 retval,
  “ (generate_new_constraints cur_num_pre l1_high_level_spec l2_high_level_spec l4 ) ” 
  &&  “ (l3 = (app (l4) (l_init_high_level_spec))) ”
  &&  (InequList r1_pre n_high_level_spec l1_high_level_spec )
  **  (InequList r2_pre n_high_level_spec l2_high_level_spec )
  **  (InequList retval n_high_level_spec l3 )))
.

Definition generate_new_constr_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: (Constraint -> (@ MonadErr.M  unit B))) (c2_low_level_spec_aux: Constraint) (c1_low_level_spec_aux: Constraint) ,
  “ (safeExec ATrue (bind ((generate_new_constr_prog (cur_num_pre) (c1_low_level_spec_aux) (c2_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec_aux )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec_aux )
|--
EX (c1_low_level_spec: Constraint) (c2_low_level_spec: Constraint) (X_low_level_spec: (Constraint -> (unit -> Prop))) ,
  (“ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec ))
  **
  ((EX c3_2 retval_2,
  “ (retval_2 <> 0) ” 
  &&  “ (safeExec ATrue (return (c3_2)) X_low_level_spec ) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array retval_2 (num_pre + 1 ) c3_2 ))
  -*
  (EX c3 retval,
  “ (retval <> 0) ” 
  &&  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (c3)) X_low_level_spec_aux ) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec_aux )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec_aux )
  **  (mpz_coef_array retval (num_pre + 1 ) c3 )))
.

Definition generate_new_constr_derive_high_level_spec_by_low_level_spec := 
forall (cur_num_pre: Z) (num_pre: Z) (r2_pre: Z) (r1_pre: Z) (c2_high_level_spec: Constraint) (c1_high_level_spec: Constraint) ,
  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c1_high_level_spec) (0)) > 0) ” 
  &&  “ ((coef_Znth (cur_num_pre) (c2_high_level_spec) (0)) < 0) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_high_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_high_level_spec )
|--
EX (c1_low_level_spec: Constraint) (c2_low_level_spec: Constraint) (X_low_level_spec: (Constraint -> (unit -> Prop))) ,
  (“ (safeExec ATrue (generate_new_constr_prog (cur_num_pre) (c1_low_level_spec) (c2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= cur_num_pre) ” 
  &&  “ (cur_num_pre < (num_pre + 1 )) ” 
  &&  “ (num_pre <= (INT_MAX - 1 )) ” 
  &&  “ (r1_pre <> 0) ” 
  &&  “ (r2_pre <> 0) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec ))
  **
  ((EX c3_2 retval_2,
  “ (retval_2 <> 0) ” 
  &&  “ (safeExec ATrue (return (c3_2)) X_low_level_spec ) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_low_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_low_level_spec )
  **  (mpz_coef_array retval_2 (num_pre + 1 ) c3_2 ))
  -*
  (EX c3 retval,
  “ (retval <> 0) ” 
  &&  “ (generate_new_constraint cur_num_pre c1_high_level_spec c2_high_level_spec c3 ) ”
  &&  (mpz_coef_array r1_pre (num_pre + 1 ) c1_high_level_spec )
  **  (mpz_coef_array r2_pre (num_pre + 1 ) c2_high_level_spec )
  **  (mpz_coef_array retval (num_pre + 1 ) c3 )))
.

Definition eliminate_derive_low_level_spec_aux_with_rel_by_low_level_spec := 
forall (B: Type) ,
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec_aux_with_rel: (B -> (unit -> Prop))) (c_low_level_spec_aux_with_rel: (BP -> (@ MonadErr.M  unit B))) (l_low_level_spec_aux_with_rel: (@list Constraint)) (n_low_level_spec_aux_with_rel: Z) (BP0: Z) ,
  “ (safeExec ATrue (bind ((eliminate_prog (num_pre) (l_low_level_spec_aux_with_rel))) (c_low_level_spec_aux_with_rel)) X_low_level_spec_aux_with_rel ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec_aux_with_rel) ” 
  &&  “ (BP0 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec_aux_with_rel l_low_level_spec_aux_with_rel )
|--
EX (n_low_level_spec: Z) (l_low_level_spec: (@list Constraint)) (X_low_level_spec: (BP -> (unit -> Prop))) (BP0_2: Z) ,
  (“ (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ” 
  &&  “ (BP0_2 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec ))
  **
  ((EX BP0_remain_2 BP0_lower_2 BP0_upper_2 up_2 lo_2 re_2 b_2,
  “ (safeExec ATrue (return (b_2)) X_low_level_spec ) ” 
  &&  “ (form_BP up_2 lo_2 re_2 b_2 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 n_low_level_spec up_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 n_low_level_spec lo_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 n_low_level_spec re_2 ))
  -*
  (EX BP0_remain BP0_lower BP0_upper up lo re b,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux_with_rel) (b)) X_low_level_spec_aux_with_rel ) ” 
  &&  “ (eliminate_xn num_pre l_low_level_spec_aux_with_rel b ) ” 
  &&  “ (form_BP up lo re b ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper n_low_level_spec_aux_with_rel up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower n_low_level_spec_aux_with_rel lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain n_low_level_spec_aux_with_rel re )))
.

Definition eliminate_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (num_pre: Z) (r_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: (BP -> (@ MonadErr.M  unit B))) (l_low_level_spec_aux: (@list Constraint)) (n_low_level_spec_aux: Z) (BP0: Z) ,
  “ (safeExec ATrue (bind ((eliminate_prog (num_pre) (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec_aux) ” 
  &&  “ (BP0 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec_aux l_low_level_spec_aux )
|--
EX (n_low_level_spec: Z) (l_low_level_spec: (@list Constraint)) (X_low_level_spec: (BP -> (unit -> Prop))) (BP0_2: Z) ,
  (“ (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ” 
  &&  “ (BP0_2 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec ))
  **
  ((EX BP0_remain_2 BP0_lower_2 BP0_upper_2 up_2 lo_2 re_2 b_2,
  “ (safeExec ATrue (return (b_2)) X_low_level_spec ) ” 
  &&  “ (form_BP up_2 lo_2 re_2 b_2 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 n_low_level_spec up_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 n_low_level_spec lo_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 n_low_level_spec re_2 ))
  -*
  (EX BP0_remain BP0_lower BP0_upper up lo re b,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (b)) X_low_level_spec_aux ) ” 
  &&  “ (form_BP up lo re b ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper n_low_level_spec_aux up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower n_low_level_spec_aux lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain n_low_level_spec_aux re )))
.

Definition eliminate_derive_high_level_spec_by_low_level_spec := 
forall (num_pre: Z) (r_pre: Z) (l_high_level_spec: (@list Constraint)) (n_high_level_spec: Z) (BP0: Z) ,
  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_high_level_spec) ” 
  &&  “ (BP0 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_high_level_spec l_high_level_spec )
|--
EX (n_low_level_spec: Z) (l_low_level_spec: (@list Constraint)) (X_low_level_spec: (BP -> (unit -> Prop))) (BP0_2: Z) ,
  (“ (safeExec ATrue (eliminate_prog (num_pre) (l_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (1 <= num_pre) ” 
  &&  “ (num_pre < n_low_level_spec) ” 
  &&  “ (BP0_2 <> 0) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |->_)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |->_)
  **  (InequList r_pre n_low_level_spec l_low_level_spec ))
  **
  ((EX BP0_remain_2 BP0_lower_2 BP0_upper_2 up_2 lo_2 re_2 b_2,
  “ (safeExec ATrue (return (b_2)) X_low_level_spec ) ” 
  &&  “ (form_BP up_2 lo_2 re_2 b_2 ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0_2)
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper_2)
  **  (InequList BP0_upper_2 n_low_level_spec up_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower_2)
  **  (InequList BP0_lower_2 n_low_level_spec lo_2 )
  **  ((&((BP0_2)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain_2)
  **  (InequList BP0_remain_2 n_low_level_spec re_2 ))
  -*
  (EX BP0_remain BP0_lower BP0_upper up lo re b,
  “ (eliminate_xn num_pre l_high_level_spec b ) ” 
  &&  “ (form_BP up lo re b ) ” 
  &&  “ (InequList_nth_pos num_pre up ) ” 
  &&  “ (InequList_nth_neg num_pre lo ) ”
  &&  ((( &( "BP0" ) )) # Ptr  |-> BP0)
  **  ((&((BP0)  # "BoundPair" ->ₛ "upper")) # Ptr  |-> BP0_upper)
  **  (InequList BP0_upper n_high_level_spec up )
  **  ((&((BP0)  # "BoundPair" ->ₛ "lower")) # Ptr  |-> BP0_lower)
  **  (InequList BP0_lower n_high_level_spec lo )
  **  ((&((BP0)  # "BoundPair" ->ₛ "remain")) # Ptr  |-> BP0_remain)
  **  (InequList BP0_remain n_high_level_spec re )))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include fme_gmp_Strategy_Correct.
Include safeexec_fme_gmp_Strategy_Correct.

Axiom proof_of_NilInequList_safety_wit_1 : NilInequList_safety_wit_1.
Axiom proof_of_NilInequList_return_wit_1 : NilInequList_return_wit_1.
Axiom proof_of_ConsInequList_return_wit_1 : ConsInequList_return_wit_1.
Axiom proof_of_ConsInequList_partial_solve_wit_1 : ConsInequList_partial_solve_wit_1.
Axiom proof_of_free_InequList_safety_wit_1 : free_InequList_safety_wit_1.
Axiom proof_of_free_InequList_safety_wit_2 : free_InequList_safety_wit_2.
Axiom proof_of_free_InequList_safety_wit_3 : free_InequList_safety_wit_3.
Axiom proof_of_free_InequList_safety_wit_4 : free_InequList_safety_wit_4.
Axiom proof_of_free_InequList_return_wit_1 : free_InequList_return_wit_1.
Axiom proof_of_free_InequList_return_wit_2 : free_InequList_return_wit_2.
Axiom proof_of_free_InequList_return_wit_3 : free_InequList_return_wit_3.
Axiom proof_of_free_InequList_partial_solve_wit_1 : free_InequList_partial_solve_wit_1.
Axiom proof_of_free_InequList_partial_solve_wit_2 : free_InequList_partial_solve_wit_2.
Axiom proof_of_free_InequList_partial_solve_wit_3 : free_InequList_partial_solve_wit_3.
Axiom proof_of_free_InequList_partial_solve_wit_4 : free_InequList_partial_solve_wit_4.
Axiom proof_of_free_InequList_partial_solve_wit_5 : free_InequList_partial_solve_wit_5.
Axiom proof_of_eliminate_safety_wit_1 : eliminate_safety_wit_1.
Axiom proof_of_eliminate_safety_wit_2 : eliminate_safety_wit_2.
Axiom proof_of_eliminate_safety_wit_3 : eliminate_safety_wit_3.
Axiom proof_of_eliminate_safety_wit_4 : eliminate_safety_wit_4.
Axiom proof_of_eliminate_safety_wit_5 : eliminate_safety_wit_5.
Axiom proof_of_eliminate_safety_wit_6 : eliminate_safety_wit_6.
Axiom proof_of_eliminate_safety_wit_7 : eliminate_safety_wit_7.
Axiom proof_of_eliminate_safety_wit_8 : eliminate_safety_wit_8.
Axiom proof_of_eliminate_safety_wit_9 : eliminate_safety_wit_9.
Axiom proof_of_eliminate_safety_wit_10 : eliminate_safety_wit_10.
Axiom proof_of_eliminate_safety_wit_11 : eliminate_safety_wit_11.
Axiom proof_of_eliminate_entail_wit_1 : eliminate_entail_wit_1.
Axiom proof_of_eliminate_entail_wit_2_1 : eliminate_entail_wit_2_1.
Axiom proof_of_eliminate_entail_wit_2_2 : eliminate_entail_wit_2_2.
Axiom proof_of_eliminate_entail_wit_2_3 : eliminate_entail_wit_2_3.
Axiom proof_of_eliminate_return_wit_1 : eliminate_return_wit_1.
Axiom proof_of_eliminate_partial_solve_wit_1 : eliminate_partial_solve_wit_1.
Axiom proof_of_eliminate_partial_solve_wit_2 : eliminate_partial_solve_wit_2.
Axiom proof_of_eliminate_partial_solve_wit_3 : eliminate_partial_solve_wit_3.
Axiom proof_of_eliminate_partial_solve_wit_4 : eliminate_partial_solve_wit_4.
Axiom proof_of_eliminate_partial_solve_wit_5 : eliminate_partial_solve_wit_5.
Axiom proof_of_generate_new_constr_safety_wit_1 : generate_new_constr_safety_wit_1.
Axiom proof_of_generate_new_constr_safety_wit_2 : generate_new_constr_safety_wit_2.
Axiom proof_of_generate_new_constr_safety_wit_3 : generate_new_constr_safety_wit_3.
Axiom proof_of_generate_new_constr_safety_wit_4 : generate_new_constr_safety_wit_4.
Axiom proof_of_generate_new_constr_entail_wit_1 : generate_new_constr_entail_wit_1.
Axiom proof_of_generate_new_constr_entail_wit_2 : generate_new_constr_entail_wit_2.
Axiom proof_of_generate_new_constr_return_wit_1 : generate_new_constr_return_wit_1.
Axiom proof_of_generate_new_constr_partial_solve_wit_1 : generate_new_constr_partial_solve_wit_1.
Axiom proof_of_generate_new_constr_partial_solve_wit_2 : generate_new_constr_partial_solve_wit_2.
Axiom proof_of_generate_new_constr_partial_solve_wit_3 : generate_new_constr_partial_solve_wit_3.
Axiom proof_of_generate_new_constr_partial_solve_wit_4 : generate_new_constr_partial_solve_wit_4.
Axiom proof_of_generate_new_constr_partial_solve_wit_5 : generate_new_constr_partial_solve_wit_5.
Axiom proof_of_generate_new_constr_partial_solve_wit_6 : generate_new_constr_partial_solve_wit_6.
Axiom proof_of_generate_new_constr_partial_solve_wit_7 : generate_new_constr_partial_solve_wit_7.
Axiom proof_of_generate_new_constr_partial_solve_wit_8 : generate_new_constr_partial_solve_wit_8.
Axiom proof_of_generate_new_constr_partial_solve_wit_9 : generate_new_constr_partial_solve_wit_9.
Axiom proof_of_generate_new_constr_partial_solve_wit_10 : generate_new_constr_partial_solve_wit_10.
Axiom proof_of_generate_new_constr_partial_solve_wit_11 : generate_new_constr_partial_solve_wit_11.
Axiom proof_of_generate_new_constr_partial_solve_wit_12 : generate_new_constr_partial_solve_wit_12.
Axiom proof_of_generate_new_constr_partial_solve_wit_13 : generate_new_constr_partial_solve_wit_13.
Axiom proof_of_generate_new_constr_partial_solve_wit_14 : generate_new_constr_partial_solve_wit_14.
Axiom proof_of_generate_new_constr_partial_solve_wit_15 : generate_new_constr_partial_solve_wit_15.
Axiom proof_of_generate_new_constr_partial_solve_wit_16_pure : generate_new_constr_partial_solve_wit_16_pure.
Axiom proof_of_generate_new_constr_partial_solve_wit_16 : generate_new_constr_partial_solve_wit_16.
Axiom proof_of_generate_new_constr_partial_solve_wit_17_pure : generate_new_constr_partial_solve_wit_17_pure.
Axiom proof_of_generate_new_constr_partial_solve_wit_17 : generate_new_constr_partial_solve_wit_17.
Axiom proof_of_generate_new_constr_partial_solve_wit_18 : generate_new_constr_partial_solve_wit_18.
Axiom proof_of_generate_new_constr_partial_solve_wit_19 : generate_new_constr_partial_solve_wit_19.
Axiom proof_of_generate_new_constr_partial_solve_wit_20 : generate_new_constr_partial_solve_wit_20.
Axiom proof_of_generate_new_constr_partial_solve_wit_21 : generate_new_constr_partial_solve_wit_21.
Axiom proof_of_generate_new_constr_partial_solve_wit_22 : generate_new_constr_partial_solve_wit_22.
Axiom proof_of_generate_new_constr_partial_solve_wit_23 : generate_new_constr_partial_solve_wit_23.
Axiom proof_of_generate_new_constr_partial_solve_wit_24 : generate_new_constr_partial_solve_wit_24.
Axiom proof_of_generate_new_constr_partial_solve_wit_25 : generate_new_constr_partial_solve_wit_25.
Axiom proof_of_generate_new_constr_partial_solve_wit_26 : generate_new_constr_partial_solve_wit_26.
Axiom proof_of_generate_new_constr_partial_solve_wit_27 : generate_new_constr_partial_solve_wit_27.
Axiom proof_of_generate_new_constr_partial_solve_wit_28 : generate_new_constr_partial_solve_wit_28.
Axiom proof_of_generate_new_constr_partial_solve_wit_29 : generate_new_constr_partial_solve_wit_29.
Axiom proof_of_generate_new_constr_partial_solve_wit_30 : generate_new_constr_partial_solve_wit_30.
Axiom proof_of_generate_new_constr_partial_solve_wit_31 : generate_new_constr_partial_solve_wit_31.
Axiom proof_of_generate_new_constr_partial_solve_wit_32 : generate_new_constr_partial_solve_wit_32.
Axiom proof_of_generate_new_constr_partial_solve_wit_33 : generate_new_constr_partial_solve_wit_33.
Axiom proof_of_generate_new_constraint_list_safety_wit_1 : generate_new_constraint_list_safety_wit_1.
Axiom proof_of_generate_new_constraint_list_safety_wit_2 : generate_new_constraint_list_safety_wit_2.
Axiom proof_of_generate_new_constraint_list_entail_wit_1 : generate_new_constraint_list_entail_wit_1.
Axiom proof_of_generate_new_constraint_list_entail_wit_2 : generate_new_constraint_list_entail_wit_2.
Axiom proof_of_generate_new_constraint_list_entail_wit_3 : generate_new_constraint_list_entail_wit_3.
Axiom proof_of_generate_new_constraint_list_entail_wit_4 : generate_new_constraint_list_entail_wit_4.
Axiom proof_of_generate_new_constraint_list_entail_wit_5 : generate_new_constraint_list_entail_wit_5.
Axiom proof_of_generate_new_constraint_list_return_wit_1 : generate_new_constraint_list_return_wit_1.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_1_pure : generate_new_constraint_list_partial_solve_wit_1_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_1 : generate_new_constraint_list_partial_solve_wit_1.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_2_pure : generate_new_constraint_list_partial_solve_wit_2_pure.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_2 : generate_new_constraint_list_partial_solve_wit_2.
Axiom proof_of_generate_new_constraint_list_partial_solve_wit_3 : generate_new_constraint_list_partial_solve_wit_3.
Axiom proof_of_real_shadow_safety_wit_1 : real_shadow_safety_wit_1.
Axiom proof_of_real_shadow_safety_wit_2 : real_shadow_safety_wit_2.
Axiom proof_of_real_shadow_safety_wit_3 : real_shadow_safety_wit_3.
Axiom proof_of_real_shadow_safety_wit_4 : real_shadow_safety_wit_4.
Axiom proof_of_real_shadow_safety_wit_5 : real_shadow_safety_wit_5.
Axiom proof_of_real_shadow_safety_wit_6 : real_shadow_safety_wit_6.
Axiom proof_of_real_shadow_safety_wit_7 : real_shadow_safety_wit_7.
Axiom proof_of_real_shadow_safety_wit_8 : real_shadow_safety_wit_8.
Axiom proof_of_real_shadow_safety_wit_9 : real_shadow_safety_wit_9.
Axiom proof_of_real_shadow_safety_wit_10 : real_shadow_safety_wit_10.
Axiom proof_of_real_shadow_safety_wit_11 : real_shadow_safety_wit_11.
Axiom proof_of_real_shadow_safety_wit_12 : real_shadow_safety_wit_12.
Axiom proof_of_real_shadow_entail_wit_1 : real_shadow_entail_wit_1.
Axiom proof_of_real_shadow_entail_wit_2_1 : real_shadow_entail_wit_2_1.
Axiom proof_of_real_shadow_entail_wit_2_2 : real_shadow_entail_wit_2_2.
Axiom proof_of_real_shadow_return_wit_1 : real_shadow_return_wit_1.
Axiom proof_of_real_shadow_return_wit_2 : real_shadow_return_wit_2.
Axiom proof_of_real_shadow_return_wit_3 : real_shadow_return_wit_3.
Axiom proof_of_real_shadow_partial_solve_wit_1_pure : real_shadow_partial_solve_wit_1_pure.
Axiom proof_of_real_shadow_partial_solve_wit_1 : real_shadow_partial_solve_wit_1.
Axiom proof_of_real_shadow_partial_solve_wit_2 : real_shadow_partial_solve_wit_2.
Axiom proof_of_real_shadow_partial_solve_wit_3 : real_shadow_partial_solve_wit_3.
Axiom proof_of_real_shadow_partial_solve_wit_4_pure : real_shadow_partial_solve_wit_4_pure.
Axiom proof_of_real_shadow_partial_solve_wit_4 : real_shadow_partial_solve_wit_4.
Axiom proof_of_real_shadow_partial_solve_wit_5_pure : real_shadow_partial_solve_wit_5_pure.
Axiom proof_of_real_shadow_partial_solve_wit_5 : real_shadow_partial_solve_wit_5.
Axiom proof_of_real_shadow_partial_solve_wit_6 : real_shadow_partial_solve_wit_6.
Axiom proof_of_real_shadow_partial_solve_wit_7 : real_shadow_partial_solve_wit_7.
Axiom proof_of_real_shadow_partial_solve_wit_8 : real_shadow_partial_solve_wit_8.
Axiom proof_of_real_shadow_partial_solve_wit_9 : real_shadow_partial_solve_wit_9.
Axiom proof_of_lia_deduction_safety_wit_1 : lia_deduction_safety_wit_1.
Axiom proof_of_lia_deduction_safety_wit_2 : lia_deduction_safety_wit_2.
Axiom proof_of_lia_deduction_safety_wit_3 : lia_deduction_safety_wit_3.
Axiom proof_of_lia_deduction_safety_wit_4 : lia_deduction_safety_wit_4.
Axiom proof_of_lia_deduction_safety_wit_5 : lia_deduction_safety_wit_5.
Axiom proof_of_lia_deduction_safety_wit_6 : lia_deduction_safety_wit_6.
Axiom proof_of_lia_deduction_safety_wit_7 : lia_deduction_safety_wit_7.
Axiom proof_of_lia_deduction_safety_wit_8 : lia_deduction_safety_wit_8.
Axiom proof_of_lia_deduction_safety_wit_9 : lia_deduction_safety_wit_9.
Axiom proof_of_lia_deduction_entail_wit_1 : lia_deduction_entail_wit_1.
Axiom proof_of_lia_deduction_entail_wit_2 : lia_deduction_entail_wit_2.
Axiom proof_of_lia_deduction_entail_wit_3_1 : lia_deduction_entail_wit_3_1.
Axiom proof_of_lia_deduction_entail_wit_3_2 : lia_deduction_entail_wit_3_2.
Axiom proof_of_lia_deduction_return_wit_1 : lia_deduction_return_wit_1.
Axiom proof_of_lia_deduction_return_wit_2 : lia_deduction_return_wit_2.
Axiom proof_of_lia_deduction_partial_solve_wit_1_pure : lia_deduction_partial_solve_wit_1_pure.
Axiom proof_of_lia_deduction_partial_solve_wit_1 : lia_deduction_partial_solve_wit_1.
Axiom proof_of_lia_deduction_partial_solve_wit_2 : lia_deduction_partial_solve_wit_2.
Axiom proof_of_lia_deduction_partial_solve_wit_3 : lia_deduction_partial_solve_wit_3.
Axiom proof_of_lia_deduction_partial_solve_wit_4 : lia_deduction_partial_solve_wit_4.
Axiom proof_of_lia_deduction_derive_low_level_spec_aux_by_low_level_spec : lia_deduction_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_lia_deduction_derive_high_level_spec_by_low_level_spec : lia_deduction_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_real_shadow_derive_low_level_spec_aux_by_low_level_spec : real_shadow_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_real_shadow_derive_high_level_spec_by_low_level_spec : real_shadow_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_generate_new_constraint_list_derive_low_level_spec_aux_with_rel_by_low_level_spec : generate_new_constraint_list_derive_low_level_spec_aux_with_rel_by_low_level_spec.
Axiom proof_of_generate_new_constraint_list_derive_high_level_spec_by_low_level_spec : generate_new_constraint_list_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_generate_new_constr_derive_low_level_spec_aux_by_low_level_spec : generate_new_constr_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_generate_new_constr_derive_high_level_spec_by_low_level_spec : generate_new_constr_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_eliminate_derive_low_level_spec_aux_with_rel_by_low_level_spec : eliminate_derive_low_level_spec_aux_with_rel_by_low_level_spec.
Axiom proof_of_eliminate_derive_low_level_spec_aux_by_low_level_spec : eliminate_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_eliminate_derive_high_level_spec_by_low_level_spec : eliminate_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
