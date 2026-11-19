(* Historical VC statements retained only to reuse checked proofs.
   No automatic proofs or interface axioms are imported here. *)
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
From SimpleC.EE.stdlib.glibc Require Import two_way_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.

(*----- Function critical_factorization -----*)

Definition critical_factorization_safety_wit_1 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) ,
  “ (safeExec ATrue (critical_factorization_prog (needle0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  ((( &( "b" ) )) # UChar  |->_)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  ((( &( "max_suffix" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition critical_factorization_safety_wit_2 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) ,
  “ (safeExec ATrue (critical_factorization_prog (needle0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  ((( &( "b" ) )) # UChar  |->_)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  ((( &( "max_suffix" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_3 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) ,
  “ (safeExec ATrue (critical_factorization_prog (needle0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  ((( &( "b" ) )) # UChar  |->_)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  ((( &( "max_suffix" ) )) # Int  |-> (-1))
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition critical_factorization_safety_wit_4 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) ,
  “ (safeExec ATrue (critical_factorization_prog (needle0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  ((( &( "b" ) )) # UChar  |->_)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  ((( &( "max_suffix" ) )) # Int  |-> (-1))
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_5 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition critical_factorization_safety_wit_6 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition critical_factorization_safety_wit_7 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ ((max_suffix + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (max_suffix + k )) ”
.

Definition critical_factorization_safety_wit_8 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) < (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition critical_factorization_safety_wit_9 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) < (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> (j + k ))
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_10 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) < (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |-> (j + k ))
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ (((j + k ) - max_suffix ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((j + k ) - max_suffix )) ”
.

Definition critical_factorization_safety_wit_11 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ (k <> p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition critical_factorization_safety_wit_12 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ (k = p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ ((j + p ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + p )) ”
.

Definition critical_factorization_safety_wit_13 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ (k = p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> (j + p ))
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_14 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> j)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition critical_factorization_safety_wit_15 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> j)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_16 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "max_suffix" ) )) # Int  |-> j)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_17 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> p)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition critical_factorization_safety_wit_18 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> p)
  **  ((( &( "max_suffix_rev" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_19 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> p)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> (-1))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition critical_factorization_safety_wit_20 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> p)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> (-1))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_21 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition critical_factorization_safety_wit_22 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition critical_factorization_safety_wit_23 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
|--
  “ ((max_suffix_rev + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (max_suffix_rev + k )) ”
.

Definition critical_factorization_safety_wit_24 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) < (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition critical_factorization_safety_wit_25 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) < (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> (j + k ))
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_26 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) < (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |-> (j + k ))
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ (((j + k ) - max_suffix_rev ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((j + k ) - max_suffix_rev )) ”
.

Definition critical_factorization_safety_wit_27 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ (k <> p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition critical_factorization_safety_wit_28 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ (k = p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ ((j + p ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + p )) ”
.

Definition critical_factorization_safety_wit_29 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ (k = p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> (j + p ))
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_30 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> j)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition critical_factorization_safety_wit_31 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> j)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_32 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> j)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_33 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((max_suffix + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (max_suffix + 1 )) ”
.

Definition critical_factorization_safety_wit_34 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((max_suffix_rev + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (max_suffix_rev + 1 )) ”
.

Definition critical_factorization_safety_wit_35 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_36 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_37 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((max_suffix_rev + 1 ) < (max_suffix + 1 )) ” 
  &&  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((max_suffix + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (max_suffix + 1 )) ”
.

Definition critical_factorization_safety_wit_38 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((max_suffix_rev + 1 ) < (max_suffix + 1 )) ” 
  &&  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_safety_wit_39 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((max_suffix_rev + 1 ) >= (max_suffix + 1 )) ” 
  &&  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> p)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((max_suffix_rev + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (max_suffix_rev + 1 )) ”
.

Definition critical_factorization_safety_wit_40 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((max_suffix_rev + 1 ) >= (max_suffix + 1 )) ” 
  &&  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((( &( "max_suffix" ) )) # Int  |-> max_suffix)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "max_suffix_rev" ) )) # Int  |-> max_suffix_rev)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "period" ) )) # Ptr  |-> period_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> p)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition critical_factorization_entail_wit_1 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) ,
  “ (safeExec ATrue (critical_factorization_prog (needle0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
|--
  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) ((-1)) (0) (1) (1)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= ((-1) + 1 )) ” 
  &&  “ (((-1) + 1 ) <= 0) ” 
  &&  “ (((1 + (-1) ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((0 + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= ((-1) + 1 )) ” 
  &&  “ (((-1) + 1 ) < needle_len_pre) ”
  &&  ((period_pre) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_2_1 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
|--
  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (j) ((j + 1 )) (1) (1)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (j + 1 )) ” 
  &&  “ (((1 + j ) + 1 ) <= needle_len_pre) ” 
  &&  “ (((j + 1 ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_2_2 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ (k = p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
|--
  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) ((j + p )) (1) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + p )) ” 
  &&  “ ((j + p ) <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= (j + p )) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (((j + p ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_2_3 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ (k <> p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) >= (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
|--
  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) ((k + 1 )) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < (k + 1 )) ” 
  &&  “ ((k + 1 ) <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + (k + 1 ) ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + (k + 1 ) )) ” 
  &&  “ ((max_suffix + (k + 1 ) ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_2_4 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) < (Znth (max_suffix + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |->_)
|--
  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) ((j + k )) (1) (((j + k ) - max_suffix ))) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + k )) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 < ((j + k ) - max_suffix )) ” 
  &&  “ (((j + k ) - max_suffix ) <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= ((j + k ) - max_suffix )) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= (j + k )) ” 
  &&  “ (((((j + k ) - max_suffix ) + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (((j + k ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_3 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((period_pre) # Int  |-> p)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (mp: Z) ,
  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) ((-1)) (0) (1) (1) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= ((-1) + 1 )) ” 
  &&  “ (((-1) + 1 ) <= 0) ” 
  &&  “ (((1 + (-1) ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((0 + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= ((-1) + 1 )) ” 
  &&  “ (((-1) + 1 ) < needle_len_pre) ”
  &&  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_4_1 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp_2: Z) ,
  “ ((Znth (j + k ) needle0_low_level_spec 0) <> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp_2)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp_2 + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp_2)
|--
  EX (mp: Z) ,
  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (j) ((j + 1 )) (1) (1) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (j + 1 )) ” 
  &&  “ (((1 + j ) + 1 ) <= needle_len_pre) ” 
  &&  “ (((j + 1 ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_4_2 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp_2: Z) ,
  “ (k = p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp_2)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp_2 + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp_2)
|--
  EX (mp: Z) ,
  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) ((j + p )) (1) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + p )) ” 
  &&  “ ((j + p ) <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= (j + p )) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ (((j + p ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_4_3 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp_2: Z) ,
  “ (k <> p) ” 
  &&  “ ((Znth (j + k ) needle0_low_level_spec 0) = (Znth (max_suffix_rev + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) >= (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp_2)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp_2 + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp_2)
|--
  EX (mp: Z) ,
  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) ((k + 1 )) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < (k + 1 )) ” 
  &&  “ ((k + 1 ) <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + (k + 1 ) ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + (k + 1 ) )) ” 
  &&  “ ((max_suffix_rev + (k + 1 ) ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_entail_wit_4_4 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp_2: Z) ,
  “ ((Znth (max_suffix_rev + k ) needle0_low_level_spec 0) < (Znth (j + k ) needle0_low_level_spec 0)) ” 
  &&  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp_2)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp_2 + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "a" ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  ((( &( "b" ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  ((period_pre) # Int  |-> mp_2)
|--
  EX (mp: Z) ,
  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) ((j + k )) (1) (((j + k ) - max_suffix_rev )) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + k )) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 < ((j + k ) - max_suffix_rev )) ” 
  &&  “ (((j + k ) - max_suffix_rev ) <= needle_len_pre) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= ((j + k ) - max_suffix_rev )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= (j + k )) ” 
  &&  “ (((((j + k ) - max_suffix_rev ) + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ (((j + k ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) < needle_len_pre) ”
  &&  ((( &( "a" ) )) # UChar  |->_)
  **  ((( &( "b" ) )) # UChar  |->_)
  **  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition critical_factorization_return_wit_1 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp_2: Z) ,
  “ ((max_suffix_rev + 1 ) >= (max_suffix + 1 )) ” 
  &&  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp_2)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp_2 + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((period_pre) # Int  |-> p)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (mp: Z) ,
  “ (safeExec ATrue (return ((maketuple ((max_suffix_rev + 1 )) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) < needle_len_pre) ” 
  &&  “ ((mp + (max_suffix_rev + 1 ) ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |-> mp)
.

Definition critical_factorization_return_wit_2 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp_2: Z) ,
  “ ((max_suffix_rev + 1 ) < (max_suffix + 1 )) ” 
  &&  “ ((j + k ) >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp_2)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp_2 + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((period_pre) # Int  |-> mp_2)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (mp: Z) ,
  “ (safeExec ATrue (return ((maketuple ((max_suffix + 1 )) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ ((mp + (max_suffix + 1 ) ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |-> mp)
.

Definition critical_factorization_partial_solve_wit_1 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  ((period_pre) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (((needle_pre + ((j + k ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre (j + k ) 0 needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
.

Definition critical_factorization_partial_solve_wit_2 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix: Z) (j: Z) (k: Z) (p: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
|--
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (first_loop_bind (needle0_low_level_spec) (max_suffix) (j) (k) (p)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) <= j) ” 
  &&  “ (((p + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + k )) ” 
  &&  “ ((max_suffix + k ) < needle_len_pre) ”
  &&  (((needle_pre + ((max_suffix + k ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (max_suffix + k ) needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre (max_suffix + k ) 0 needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_)
.

Definition critical_factorization_partial_solve_wit_3 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  ((period_pre) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (((needle_pre + ((j + k ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (j + k ) needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre (j + k ) 0 needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |-> mp)
.

Definition critical_factorization_partial_solve_wit_4 := 
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) (n0_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (max_suffix_rev: Z) (j: Z) (k: Z) (p: Z) (max_suffix: Z) (mp: Z) ,
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |-> mp)
|--
  “ ((j + k ) < needle_len_pre) ” 
  &&  “ (safeExec ATrue (second_loop_bind (needle0_low_level_spec) (max_suffix_rev) (j) (k) (p) (max_suffix) (mp)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= needle_len_pre) ” 
  &&  “ (0 < p) ” 
  &&  “ (p <= needle_len_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= p) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix + 1 )) ” 
  &&  “ ((max_suffix + 1 ) < needle_len_pre) ” 
  &&  “ (((mp + max_suffix ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + 1 )) ” 
  &&  “ ((max_suffix_rev + 1 ) <= j) ” 
  &&  “ (((p + max_suffix_rev ) + 1 ) <= needle_len_pre) ” 
  &&  “ ((j + k ) <= needle_len_pre) ” 
  &&  “ (0 <= (max_suffix_rev + k )) ” 
  &&  “ ((max_suffix_rev + k ) < needle_len_pre) ”
  &&  (((needle_pre + ((max_suffix_rev + k ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (max_suffix_rev + k ) needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre (max_suffix_rev + k ) 0 needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |-> mp)
.

(*----- Function two_way_short_needle -----*)

Definition two_way_short_needle_safety_wit_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "memory" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "memory" ) )) # Int  |-> 0)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_4 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((haystack_len_pre - needle_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (haystack_len_pre - needle_len_pre )) ”
.

Definition two_way_short_needle_safety_wit_5 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (suffix > memory) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (suffix * sizeof(UCHAR) ) ))
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |-> suffix)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix + j )) ”
.

Definition two_way_short_needle_safety_wit_6 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (suffix <= memory) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (memory * sizeof(UCHAR) ) ))
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |-> memory)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((memory + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (memory + j )) ”
.

Definition two_way_short_needle_safety_wit_7 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_8 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_9 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_short_needle_safety_wit_10 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_11 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_12 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_13 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix - 1 )) ”
.

Definition two_way_short_needle_safety_wit_14 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_15 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> (suffix - 1 ))
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((suffix - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (((suffix - 1 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((suffix - 1 ) + j )) ”
.

Definition two_way_short_needle_safety_wit_16 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_short_needle_safety_wit_17 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_18 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_19 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_20 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition two_way_short_needle_safety_wit_21 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_22 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((memory + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (memory + 1 )) ”
.

Definition two_way_short_needle_safety_wit_23 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ ((memory + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (memory + 1 )) ”
.

Definition two_way_short_needle_safety_wit_24 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_short_needle_safety_wit_25 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_short_needle_safety_wit_26 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_27 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_28 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_29 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_30 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) < (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_31 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_32 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ ((j + mp ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + mp )) ”
.

Definition two_way_short_needle_safety_wit_33 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> (j + mp ))
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ ((needle_len_pre - mp ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - mp )) ”
.

Definition two_way_short_needle_safety_wit_34 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ ((j + ((i - suffix ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + ((i - suffix ) + 1 ) )) ”
.

Definition two_way_short_needle_safety_wit_35 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (((i - suffix ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - suffix ) + 1 )) ”
.

Definition two_way_short_needle_safety_wit_36 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ ((i - suffix ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - suffix )) ”
.

Definition two_way_short_needle_safety_wit_37 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_38 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> (j + ((i - suffix ) + 1 ) ))
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_39 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ ((needle_len_pre - retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - retval )) ”
.

Definition two_way_short_needle_safety_wit_40 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval > (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition two_way_short_needle_safety_wit_41 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval > (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_42 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval <= (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (((needle_len_pre - retval ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((needle_len_pre - retval ) + 1 )) ”
.

Definition two_way_short_needle_safety_wit_43 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval <= (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ ((needle_len_pre - retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - retval )) ”
.

Definition two_way_short_needle_safety_wit_44 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval <= (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_45 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval <= (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> ((needle_len_pre - retval ) + 1 ))
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_46 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval > (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> (retval + 1 ))
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_47 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((haystack_len_pre - needle_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (haystack_len_pre - needle_len_pre )) ”
.

Definition two_way_short_needle_safety_wit_48 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) ,
  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "haystack_char" ) )) # UChar  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix + j )) ”
.

Definition two_way_short_needle_safety_wit_49 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) ,
  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (suffix + j ) hay0_low_level_spec 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((suffix + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_50 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition two_way_short_needle_safety_wit_51 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_52 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((haystack_len_pre - needle_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (haystack_len_pre - needle_len_pre )) ”
.

Definition two_way_short_needle_safety_wit_53 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((j + 1 ) > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_54 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((j + 1 ) <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth ((suffix + j ) + 1 ) hay0_low_level_spec 0))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_55 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((Znth suffix needle0_low_level_spec 0) = phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix + 1 )) ”
.

Definition two_way_short_needle_safety_wit_56 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((Znth suffix needle0_low_level_spec 0) = phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_57 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((Znth suffix needle0_low_level_spec 0) = phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |-> (suffix + 1 ))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((suffix + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (((suffix + 1 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((suffix + 1 ) + j )) ”
.

Definition two_way_short_needle_safety_wit_58 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_59 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_60 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_short_needle_safety_wit_61 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_62 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_63 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_64 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix - 1 )) ”
.

Definition two_way_short_needle_safety_wit_65 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_66 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> (suffix - 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((suffix - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (((suffix - 1 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((suffix - 1 ) + j )) ”
.

Definition two_way_short_needle_safety_wit_67 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition two_way_short_needle_safety_wit_68 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_69 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_70 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_71 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition two_way_short_needle_safety_wit_72 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_73 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition two_way_short_needle_safety_wit_74 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <> (INT_MIN)) ”
.

Definition two_way_short_needle_safety_wit_75 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_76 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_77 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_78 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> phay_ch)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_short_needle_safety_wit_79 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ ((j + mp ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + mp )) ”
.

Definition two_way_short_needle_safety_wit_80 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ ((j + ((i - suffix ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + ((i - suffix ) + 1 ) )) ”
.

Definition two_way_short_needle_safety_wit_81 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (((i - suffix ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - suffix ) + 1 )) ”
.

Definition two_way_short_needle_safety_wit_82 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ ((i - suffix ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - suffix )) ”
.

Definition two_way_short_needle_safety_wit_83 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "needle_suffix" ) )) # UChar  |-> (Znth suffix needle0_low_level_spec 0))
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  ((( &( "haystack_char" ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_short_needle_safety_wit_84 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_safety_wit_85 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_short_needle_entail_wit_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (retval) (mp) (0) (0)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_2_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (suffix <= memory) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= memory) ” 
  &&  “ (memory <= memory) ” 
  &&  “ (memory <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_2_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (suffix > memory) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (suffix)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= suffix) ” 
  &&  “ (memory <= suffix) ” 
  &&  “ (suffix <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
|--
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= (i + 1 )) ” 
  &&  “ (memory <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= needle_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i + 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_4 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) ((suffix - 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= ((suffix - 1 ) + 1 )) ” 
  &&  “ (((suffix - 1 ) + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_5 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
|--
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= suffix) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i - 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_6_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + ((i - suffix ) + 1 ) )) (0)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + ((i - suffix ) + 1 ) )) ” 
  &&  “ ((j + ((i - suffix ) + 1 ) ) <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_6_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + mp )) ((needle_len_pre - mp ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + mp )) ” 
  &&  “ ((j + mp ) <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (needle_len_pre - mp )) ” 
  &&  “ ((needle_len_pre - mp ) < needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_7_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval > (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (retval) ((retval + 1 )) (0)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_7_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval <= (needle_len_pre - retval )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (retval) (((needle_len_pre - retval ) + 1 )) (0)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < ((needle_len_pre - retval ) + 1 )) ” 
  &&  “ (((needle_len_pre - retval ) + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_8 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) ,
  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((suffix + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ ((Znth (suffix + j ) hay0_low_level_spec 0) = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_9 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((j + 1 ) <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + (j + 1 ) ) + 1 )) ” 
  &&  “ (((suffix + (j + 1 ) ) + 1 ) <= haystack_len_pre) ” 
  &&  “ ((Znth ((suffix + j ) + 1 ) hay0_low_level_spec 0) = (Znth ((suffix + (j + 1 ) )) (hay0_low_level_spec) (0))) ”
  &&  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix + (j + 1 ) ) + 1 ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_10 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((Znth suffix needle0_low_level_spec 0) = phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) ((suffix + 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_11 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
|--
  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((i + 1 ) + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i + 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_12 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre <= i) ” 
  &&  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) ((suffix - 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix - 1 ) + 1 )) ” 
  &&  “ (((suffix - 1 ) + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= (((suffix - 1 ) + 1 ) + j )) ” 
  &&  “ ((((suffix - 1 ) + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_13 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
|--
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= (((i - 1 ) + 1 ) + j )) ” 
  &&  “ ((((i - 1 ) + 1 ) + j ) <= haystack_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i - 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_14_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (needle_len_pre > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + ((i - suffix ) + 1 ) ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= (j + ((i - suffix ) + 1 ) )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_entail_wit_14_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
|--
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + mp ))) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= (j + mp )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_return_wit_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) (0) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_return_wit_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) (0) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_return_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) ((haystack_pre + (j * sizeof(UCHAR) ) )) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_return_wit_4 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((j + 1 ) > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) (0) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_return_wit_5 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) < (memory + 1 )) ” 
  &&  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) ((haystack_pre + (j * sizeof(UCHAR) ) )) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_1_pure := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) ,
  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "suffix" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (needle_len_pre = needle_len_pre) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((critical_factorization_prog (needle0_low_level_spec))) ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec)))) X_low_level_spec ) ”
.

Definition two_way_short_needle_partial_solve_wit_1_aux := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) ,
  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (needle_len_pre = needle_len_pre) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((critical_factorization_prog (needle0_low_level_spec))) ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_1 := two_way_short_needle_partial_solve_wit_1_pure -> two_way_short_needle_partial_solve_wit_1_aux.

Definition two_way_short_needle_partial_solve_wit_2_pure := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (needle_pre = (needle_pre + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ ((needle_pre + (mp * sizeof(UCHAR) ) ) = (needle_pre + (mp * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= mp) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((0 + retval ) <= needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ”
.

Definition two_way_short_needle_partial_solve_wit_2_aux := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (needle_pre = (needle_pre + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ ((needle_pre + (mp * sizeof(UCHAR) ) ) = (needle_pre + (mp * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= mp) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((0 + retval ) <= needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_2 := two_way_short_needle_partial_solve_wit_2_pure -> two_way_short_needle_partial_solve_wit_2_aux.

Definition two_way_short_needle_partial_solve_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_4 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= needle_len_pre) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_5 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_6 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_7 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp retval retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (((needle_pre + (retval * sizeof(UCHAR) ) )) # UChar  |-> (Znth retval needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre retval 0 needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_8 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) ,
  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (((haystack_pre + ((suffix + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (suffix + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (suffix + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_9 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (phay_ch: Z) (suffix: Z) (mp: Z) (j: Z) ,
  “ ((j + 1 ) <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + 1 ) <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ ((Znth suffix needle0_low_level_spec 0) <> phay_ch) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= haystack_len_pre) ” 
  &&  “ (phay_ch = (Znth ((suffix + j )) (hay0_low_level_spec) (0))) ”
  &&  (((haystack_pre + (((suffix + j ) + 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth ((suffix + j ) + 1 ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre ((suffix + j ) + 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_10 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_11 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((suffix + j ) + 1 )) ” 
  &&  “ (((suffix + j ) + 1 ) <= (i + j )) ” 
  &&  “ (((suffix + j ) + 1 ) <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= ((suffix + 1 ) + j )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) <= haystack_len_pre) ” 
  &&  “ (((suffix + 1 ) + j ) <= haystack_len_pre) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_12 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_short_needle_partial_solve_wit_13 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (suffix + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

(*----- Function two_way_long_needle -----*)

Definition two_way_long_needle_safety_wit_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (retval) (mp)) ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.undef_full ( &( "shift_table" ) ) 256 )
  **  ((( &( "suffix" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (suffix: Z) (mp: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.seg ( &( "shift_table" ) ) 0 i (repeat_Z (needle_len_pre) (i)) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) i 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
.

Definition two_way_long_needle_safety_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (suffix: Z) (mp: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.seg ( &( "shift_table" ) ) 0 i (repeat_Z (needle_len_pre) (i)) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) i 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition two_way_long_needle_safety_wit_4 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (suffix: Z) (mp: Z) ,
  “ (i < (Z.shiftl 1 8)) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.seg ( &( "shift_table" ) ) 0 (i + 1 ) (app ((repeat_Z (needle_len_pre) (i))) ((cons (needle_len_pre) (nil)))) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) (i + 1 ) 256 )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_long_needle_safety_wit_5 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec 0 table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_6 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (i: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i) (needle0_low_level_spec) (0)))
|--
  “ (((needle_len_pre - i ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((needle_len_pre - i ) - 1 )) ”
.

Definition two_way_long_needle_safety_wit_7 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (i: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i) (needle0_low_level_spec) (0)))
|--
  “ ((needle_len_pre - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - i )) ”
.

Definition two_way_long_needle_safety_wit_8 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (i: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i) (needle0_low_level_spec) (0)))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_9 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (i: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre (replace_Znth (i) ((Znth (i) (needle0_low_level_spec) (0))) (needle0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 (replace_Znth ((Znth (i) (needle0_low_level_spec) (0))) (((needle_len_pre - i ) - 1 )) (table)) )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_long_needle_safety_wit_10 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_11 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_12 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "memory" ) )) # Int  |-> 0)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_13 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((haystack_len_pre - needle_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (haystack_len_pre - needle_len_pre )) ”
.

Definition two_way_long_needle_safety_wit_14 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (((j + needle_len_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((j + needle_len_pre ) - 1 )) ”
.

Definition two_way_long_needle_safety_wit_15 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + needle_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + needle_len_pre )) ”
.

Definition two_way_long_needle_safety_wit_16 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_17 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |-> (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0))
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_18 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ ((Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0) < mp) ” 
  &&  “ (memory <> 0) ” 
  &&  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |-> (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0))
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((needle_len_pre - mp ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - mp )) ”
.

Definition two_way_long_needle_safety_wit_19 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) (shift: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j shift ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < shift) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_20 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) (shift: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j shift ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < shift) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + shift ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + shift )) ”
.

Definition two_way_long_needle_safety_wit_21 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) (shift: Z) ,
  “ (suffix > memory) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (suffix * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> suffix)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix + j )) ”
.

Definition two_way_long_needle_safety_wit_22 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) (shift: Z) ,
  “ (suffix <= memory) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (memory * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> memory)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((memory + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (memory + j )) ”
.

Definition two_way_long_needle_safety_wit_23 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((needle_len_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - 1 )) ”
.

Definition two_way_long_needle_safety_wit_24 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_25 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_26 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_27 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_long_needle_safety_wit_28 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_29 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((needle_len_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - 1 )) ”
.

Definition two_way_long_needle_safety_wit_30 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((needle_len_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - 1 )) ”
.

Definition two_way_long_needle_safety_wit_31 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_32 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_33 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_34 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_35 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix - 1 )) ”
.

Definition two_way_long_needle_safety_wit_36 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_37 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> (suffix - 1 ))
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((suffix - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (((suffix - 1 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((suffix - 1 ) + j )) ”
.

Definition two_way_long_needle_safety_wit_38 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_long_needle_safety_wit_39 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_40 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_41 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_42 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition two_way_long_needle_safety_wit_43 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_44 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((memory + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (memory + 1 )) ”
.

Definition two_way_long_needle_safety_wit_45 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((memory + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (memory + 1 )) ”
.

Definition two_way_long_needle_safety_wit_46 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_long_needle_safety_wit_47 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_long_needle_safety_wit_48 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_49 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_50 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_51 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_52 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) < (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_53 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_54 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((j + mp ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + mp )) ”
.

Definition two_way_long_needle_safety_wit_55 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> (j + mp ))
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((needle_len_pre - mp ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - mp )) ”
.

Definition two_way_long_needle_safety_wit_56 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((j + ((i - suffix ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + ((i - suffix ) + 1 ) )) ”
.

Definition two_way_long_needle_safety_wit_57 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (((i - suffix ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - suffix ) + 1 )) ”
.

Definition two_way_long_needle_safety_wit_58 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((i - suffix ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - suffix )) ”
.

Definition two_way_long_needle_safety_wit_59 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_60 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "memory" ) )) # Int  |-> memory)
  **  ((( &( "j" ) )) # Int  |-> (j + ((i - suffix ) + 1 ) ))
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_61 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ ((needle_len_pre - suffix ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - suffix )) ”
.

Definition two_way_long_needle_safety_wit_62 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix > (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ ((suffix + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix + 1 )) ”
.

Definition two_way_long_needle_safety_wit_63 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix > (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_64 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix <= (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (((needle_len_pre - suffix ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((needle_len_pre - suffix ) + 1 )) ”
.

Definition two_way_long_needle_safety_wit_65 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix <= (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ ((needle_len_pre - suffix ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - suffix )) ”
.

Definition two_way_long_needle_safety_wit_66 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix <= (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_67 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix <= (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> ((needle_len_pre - suffix ) + 1 ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_68 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix > (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> (suffix + 1 ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_69 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((haystack_len_pre - needle_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (haystack_len_pre - needle_len_pre )) ”
.

Definition two_way_long_needle_safety_wit_70 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (((j + needle_len_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((j + needle_len_pre ) - 1 )) ”
.

Definition two_way_long_needle_safety_wit_71 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + needle_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + needle_len_pre )) ”
.

Definition two_way_long_needle_safety_wit_72 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_73 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # Int  |-> (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_74 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) (shift: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j shift ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < shift) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((j + shift ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + shift )) ”
.

Definition two_way_long_needle_safety_wit_75 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) (shift: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (suffix * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> suffix)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix + j )) ”
.

Definition two_way_long_needle_safety_wit_76 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((needle_len_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - 1 )) ”
.

Definition two_way_long_needle_safety_wit_77 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_78 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_79 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_80 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition two_way_long_needle_safety_wit_81 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_82 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((needle_len_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - 1 )) ”
.

Definition two_way_long_needle_safety_wit_83 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((needle_len_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (needle_len_pre - 1 )) ”
.

Definition two_way_long_needle_safety_wit_84 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_85 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_86 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_87 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_88 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ ((suffix - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (suffix - 1 )) ”
.

Definition two_way_long_needle_safety_wit_89 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_90 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> (suffix - 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((suffix - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (((suffix - 1 ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((suffix - 1 ) + j )) ”
.

Definition two_way_long_needle_safety_wit_91 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition two_way_long_needle_safety_wit_92 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_93 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_94 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_95 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition two_way_long_needle_safety_wit_96 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_97 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition two_way_long_needle_safety_wit_98 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition two_way_long_needle_safety_wit_99 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_100 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_101 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_102 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ False ”
.

Definition two_way_long_needle_safety_wit_103 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((j + period ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + period )) ”
.

Definition two_way_long_needle_safety_wit_104 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((j + ((i - suffix ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + ((i - suffix ) + 1 ) )) ”
.

Definition two_way_long_needle_safety_wit_105 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (((i - suffix ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - suffix ) + 1 )) ”
.

Definition two_way_long_needle_safety_wit_106 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ ((i - suffix ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - suffix )) ”
.

Definition two_way_long_needle_safety_wit_107 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition two_way_long_needle_safety_wit_108 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "period" ) )) # Int  |-> period)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_safety_wit_109 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition two_way_long_needle_entail_wit_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (retval: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (retval) (mp)) ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.undef_full ( &( "shift_table" ) ) 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (retval) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (retval) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ”
  &&  (IntArray.seg ( &( "shift_table" ) ) 0 0 (repeat_Z (needle_len_pre) (0)) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) 0 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (suffix: Z) (mp: Z) ,
  “ (i < (Z.shiftl 1 8)) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.seg ( &( "shift_table" ) ) 0 (i + 1 ) (app ((repeat_Z (needle_len_pre) (i))) ((cons (needle_len_pre) (nil)))) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) (i + 1 ) 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.seg ( &( "shift_table" ) ) 0 (i + 1 ) (repeat_Z (needle_len_pre) ((i + 1 ))) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) (i + 1 ) 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (suffix: Z) (mp: Z) ,
  “ (i >= (Z.shiftl 1 8)) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ( &( "shift_table" ) ) 0 i (repeat_Z (needle_len_pre) (i)) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) i 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec 0 table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_4 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (suffix: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec 0 table_2 ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec 0 table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= needle_len_pre) ” 
  &&  “ (0 <= (Znth (0) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (0) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_5 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (table_2: (@list Z)) (suffix: Z) (mp: Z) ,
  “ (i < needle_len_pre) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table_2 ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i) (needle0_low_level_spec) (0)))
.

Definition two_way_long_needle_entail_wit_6 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (suffix: Z) (i: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table_2 ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre (replace_Znth (i) ((Znth (i) (needle0_low_level_spec) (0))) (needle0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 (replace_Znth ((Znth (i) (needle0_low_level_spec) (0))) (((needle_len_pre - i ) - 1 )) (table_2)) )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec (i + 1 ) table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= needle_len_pre) ” 
  &&  “ (0 <= (Znth ((i + 1 )) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth ((i + 1 )) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_7 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (table_2: (@list Z)) (suffix: Z) (mp: Z) ,
  “ (i >= needle_len_pre) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table_2 ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_8 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (0) (0)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec 0 mp 0 ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_9 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_10_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ ((Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table_2 0) < mp) ” 
  &&  “ (memory <> 0) ” 
  &&  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table_2 0)) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - mp ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < (needle_len_pre - mp )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_10_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ (memory = 0) ” 
  &&  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table_2: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_10_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ ((Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0) >= mp) ” 
  &&  “ (memory <> 0) ” 
  &&  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table_2: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_11 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ (0 >= (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table_2: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ ((Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0) = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_12_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (memory: Z) (j: Z) (suffix: Z) (shift: Z) ,
  “ (suffix <= memory) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix memory ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= memory) ” 
  &&  “ (memory <= memory) ” 
  &&  “ (memory <= (needle_len_pre - 1 )) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_12_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (memory: Z) (j: Z) (suffix: Z) (shift: Z) ,
  “ (suffix > memory) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (suffix)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix suffix ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= suffix) ” 
  &&  “ (memory <= suffix) ” 
  &&  “ (suffix <= (needle_len_pre - 1 )) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_13 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix (i + 1 ) ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= (i + 1 )) ” 
  &&  “ (memory <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (needle_len_pre - 1 )) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i + 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_14 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) ((suffix - 1 ))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j ((suffix - 1 ) + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= ((suffix - 1 ) + 1 )) ” 
  &&  “ (((suffix - 1 ) + 1 ) <= suffix) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_15 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j ((i - 1 ) + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= suffix) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i - 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_16 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) < (memory + 1 )) ” 
  &&  “ (memory >= (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (i * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((i + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ ((i + 1 ) < (memory + 1 )) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |->_)
  **  ((( &( "phaystack" ) )) # Ptr  |->_)
  **  (IntArray.undef_full ( &( "shift_table" ) ) 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_17_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (memory: Z) (j: Z) (suffix: Z) (shift: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j shift ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < shift) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + shift )) (0)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec (j + shift ) mp 0 ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + shift )) ” 
  &&  “ ((j + shift ) <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_17_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + ((i - suffix ) + 1 ) )) (0)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec (j + ((i - suffix ) + 1 ) ) mp 0 ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + ((i - suffix ) + 1 ) )) ” 
  &&  “ ((j + ((i - suffix ) + 1 ) ) <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_17_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ ((i + 1 ) >= (memory + 1 )) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) ((j + mp )) ((needle_len_pre - mp ))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec (j + mp ) mp (needle_len_pre - mp ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + mp )) ” 
  &&  “ ((j + mp ) <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (needle_len_pre - mp )) ” 
  &&  “ ((needle_len_pre - mp ) < needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_18_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix > (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) ((suffix + 1 )) (0)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < (suffix + 1 )) ” 
  &&  “ ((suffix + 1 ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_18_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table_2: (@list Z)) (suffix: Z) (retval: Z) ,
  “ (suffix <= (needle_len_pre - suffix )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (memcmp_result needle0_low_level_spec 0 mp suffix retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (((needle_len_pre - suffix ) + 1 )) (0)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < ((needle_len_pre - suffix ) + 1 )) ” 
  &&  “ (((needle_len_pre - suffix ) + 1 ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_19 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (period: Z) (j: Z) ,
  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_20 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) ,
  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table_2: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_21 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) ,
  “ (0 >= (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0)) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre (replace_Znth (((j + needle_len_pre ) - 1 )) ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) (hay0_low_level_spec)) )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table_2: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ ((Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0) = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_22 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (j: Z) (period: Z) (suffix: Z) (shift: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift = 0) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (suffix * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((suffix + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (suffix)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= suffix) ” 
  &&  “ (suffix <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (suffix + j )) ” 
  &&  “ ((suffix + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + (suffix * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + ((suffix + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_23 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) + (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i + 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i + 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_24 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) <= i) ” 
  &&  “ (i >= (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((suffix - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix - 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) ((suffix - 1 ))) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((suffix - 1 ) + 1 )) ” 
  &&  “ (((suffix - 1 ) + 1 ) <= suffix) ” 
  &&  “ (0 <= (((suffix - 1 ) + 1 ) + j )) ” 
  &&  “ ((((suffix - 1 ) + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((suffix - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((suffix - 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_25 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((Znth i needle0_low_level_spec 0) = (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "pneedle" ) )) # Ptr  |-> ((needle_pre + (i * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> ((haystack_pre + ((i + j ) * sizeof(UCHAR) ) ) - (1 * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) ((i - 1 ))) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= suffix) ” 
  &&  “ (0 <= (((i - 1 ) + 1 ) + j )) ” 
  &&  “ ((((i - 1 ) + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "pneedle" ) )) # Ptr  |-> (needle_pre + ((i - 1 ) * sizeof(UCHAR) ) ))
  **  ((( &( "phaystack" ) )) # Ptr  |-> (haystack_pre + (((i - 1 ) + j ) * sizeof(UCHAR) ) ))
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_26_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (j: Z) (period: Z) (suffix: Z) (shift: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (valid_skip hay0_low_level_spec needle0_low_level_spec j shift ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < shift) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |-> shift)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) ((j + shift ))) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + shift )) ” 
  &&  “ ((j + shift ) <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_26_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ ((needle_len_pre - 1 ) > i) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) ((j + ((i - suffix ) + 1 ) ))) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + ((i - suffix ) + 1 ) )) ” 
  &&  “ ((j + ((i - suffix ) + 1 ) ) <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_entail_wit_26_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table_2: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ ((Znth i needle0_low_level_spec 0) <> (Znth (i + j ) hay0_low_level_spec 0)) ” 
  &&  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table_2 ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) ((j + period ))) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= (j + period )) ” 
  &&  “ ((j + period ) <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_return_wit_1 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) (0) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_return_wit_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) ,
  “ (j > (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= haystack_len_pre) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) (0) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_return_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i = (-1)) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) ((haystack_pre + (j * sizeof(UCHAR) ) )) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_return_wit_4 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (i: Z) (memory: Z) (j: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ ((i + 1 ) < (memory + 1 )) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) ((haystack_pre + (j * sizeof(UCHAR) ) )) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_1_pure := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) ,
  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.undef_full ( &( "shift_table" ) ) 256 )
  **  ((( &( "suffix" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (needle_len_pre = needle_len_pre) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((critical_factorization_prog (needle0_low_level_spec))) ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec)))) X_low_level_spec ) ”
.

Definition two_way_long_needle_partial_solve_wit_1_aux := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (nn_low_level_spec: Z) (hn_low_level_spec: Z) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) ,
  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.undef_full ( &( "shift_table" ) ) 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (needle_len_pre = needle_len_pre) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((critical_factorization_prog (needle0_low_level_spec))) ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.undef_full ( &( "shift_table" ) ) 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_1 := two_way_long_needle_partial_solve_wit_1_pure -> two_way_long_needle_partial_solve_wit_1_aux.

Definition two_way_long_needle_partial_solve_wit_2 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (i: Z) (suffix: Z) (mp: Z) ,
  “ (i < (Z.shiftl 1 8)) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.seg ( &( "shift_table" ) ) 0 i (repeat_Z (needle_len_pre) (i)) )
  **  (IntArray.undef_seg ( &( "shift_table" ) ) i 256 )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i < (Z.shiftl 1 8)) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (((( &( "shift_table" ) ) + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "shift_table" ) ) (i + 1 ) 256 )
  **  (IntArray.seg ( &( "shift_table" ) ) 0 i (repeat_Z (needle_len_pre) (i)) )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_3 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) (i: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i) (needle0_low_level_spec) (0)))
|--
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_build_prefix needle0_low_level_spec i table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < needle_len_pre) ” 
  &&  “ (0 <= (Znth (i) (needle0_low_level_spec) (0))) ” 
  &&  “ ((Znth (i) (needle0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (((( &( "shift_table" ) ) + ((Znth (i) (needle0_low_level_spec) (0)) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i ( &( "shift_table" ) ) (Znth (i) (needle0_low_level_spec) (0)) 0 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i) (needle0_low_level_spec) (0)))
.

Definition two_way_long_needle_partial_solve_wit_4_pure := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "haystack_len" ) )) # Int  |-> haystack_len_pre)
  **  ((( &( "needle_len" ) )) # Int  |-> needle_len_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "period" ) )) # Int  |-> mp)
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (needle_pre = (needle_pre + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ ((needle_pre + (mp * sizeof(UCHAR) ) ) = (needle_pre + (mp * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= mp) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ ((0 + suffix ) <= needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
.

Definition two_way_long_needle_partial_solve_wit_4_aux := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (suffix: Z) ,
  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (needle_pre = (needle_pre + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ ((needle_pre + (mp * sizeof(UCHAR) ) ) = (needle_pre + (mp * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= mp) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ ((0 + suffix ) <= needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ” 
  &&  “ (safeExec ATrue (applyf ((two_way_generic_after_factorization (hay0_low_level_spec) (needle0_low_level_spec))) ((maketuple (suffix) (mp)))) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ ((mp + suffix ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_4 := two_way_long_needle_partial_solve_wit_4_pure -> two_way_long_needle_partial_solve_wit_4_aux.

Definition two_way_long_needle_partial_solve_wit_5 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (mp: Z) (table: (@list Z)) (memory: Z) (j: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_periodic_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ”
  &&  (((( &( "shift_table" ) ) + ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) * sizeof(INT) ) )) # Int  |-> (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0))
  **  (IntArray.missing_i ( &( "shift_table" ) ) (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) 0 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_6 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_7 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j suffix i ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (memory <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
.

Definition two_way_long_needle_partial_solve_wit_8 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_9 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (mp: Z) (j: Z) (memory: Z) (i: Z) ,
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (memory < (i + 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_periodic_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (mp) (j) (memory) (i)) X_low_level_spec ) ” 
  &&  “ (critical_factorization_spec needle0_low_level_spec (maketuple (suffix) (mp)) ) ” 
  &&  “ (repetitive_split needle0_low_level_spec suffix mp ) ” 
  &&  “ (periodic_memory_match hay0_low_level_spec needle0_low_level_spec j mp memory ) ” 
  &&  “ (matched_range hay0_low_level_spec needle0_low_level_spec j (i + 1 ) needle_len_pre ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= memory) ” 
  &&  “ (memory < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
.

Definition two_way_long_needle_partial_solve_wit_10 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (j: Z) (period: Z) (suffix: Z) ,
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (safeExec ATrue (generic_match_from (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 <= ((j + needle_len_pre ) - 1 )) ” 
  &&  “ (((j + needle_len_pre ) - 1 ) < haystack_len_pre) ” 
  &&  “ (0 <= (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0))) ” 
  &&  “ ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) < 256) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (((( &( "shift_table" ) ) + ((Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) * sizeof(INT) ) )) # Int  |-> (Znth (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) table 0))
  **  (IntArray.missing_i ( &( "shift_table" ) ) (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)) 0 256 table )
  **  (UCharArray.missing_i haystack_pre ((j + needle_len_pre ) - 1 ) 0 haystack_len_pre hay0_low_level_spec )
  **  (((haystack_pre + (((j + needle_len_pre ) - 1 ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (((j + needle_len_pre ) - 1 )) (hay0_low_level_spec) (0)))
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_11 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_12 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (i < (needle_len_pre - 1 )) ” 
  &&  “ (safeExec ATrue (generic_match_from_right (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (i)) X_low_level_spec ) ” 
  &&  “ (match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1 ) ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (suffix <= i) ” 
  &&  “ (i <= (needle_len_pre - 1 )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
.

Definition two_way_long_needle_partial_solve_wit_13 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
|--
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (((needle_pre + (i * sizeof(UCHAR) ) )) # UChar  |-> (Znth i needle0_low_level_spec 0))
  **  (UCharArray.missing_i needle_pre i 0 needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
.

Definition two_way_long_needle_partial_solve_wit_14 := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needle0_low_level_spec: (@list Z)) (hay0_low_level_spec: (@list Z)) (table: (@list Z)) (suffix: Z) (period: Z) (j: Z) (i: Z) ,
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
  **  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
|--
  “ (i <> (-1)) ” 
  &&  “ (safeExec ATrue (generic_match_from_left (hay0_low_level_spec) (needle0_low_level_spec) (suffix) (period) (j) (0) (i)) X_low_level_spec ) ” 
  &&  “ (shift_table_sound hay0_low_level_spec needle0_low_level_spec table ) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (haystack_len_pre - needle_len_pre )) ” 
  &&  “ (0 < suffix) ” 
  &&  “ (0 <= suffix) ” 
  &&  “ (suffix < needle_len_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= suffix) ” 
  &&  “ (0 <= ((i + 1 ) + j )) ” 
  &&  “ (((i + 1 ) + j ) <= haystack_len_pre) ” 
  &&  “ (0 < period) ” 
  &&  “ (period <= needle_len_pre) ”
  &&  (((haystack_pre + ((i + j ) * sizeof(UCHAR) ) )) # UChar  |-> (Znth (i + j ) hay0_low_level_spec 0))
  **  (UCharArray.missing_i haystack_pre (i + j ) 0 haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  (IntArray.full ( &( "shift_table" ) ) 256 table )
.

Definition two_way_long_needle_derive_high_level_spec_by_low_level_spec := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (nn_high_level_spec: Z) (hn_high_level_spec: Z) (needle0_high_level_spec: (@list Z)) (hay0_high_level_spec: (@list Z)) ,
  “ (haystack_len_pre = hn_high_level_spec) ” 
  &&  “ (needle_len_pre = nn_high_level_spec) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_high_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_high_level_spec )
|--
EX (hay0_low_level_spec: (@list Z)) (needle0_low_level_spec: (@list Z)) (hn_low_level_spec: Z) (nn_low_level_spec: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) ,
  (“ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (32 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec ))
  **
  ((EX retval_2,
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) (retval_2) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec ))
  -*
  (EX ret retval,
  “ (match_post hay0_high_level_spec needle0_high_level_spec ret ) ” 
  &&  “ ((uchar_ptr_option_repr (haystack_pre) (retval) (sizeof(UCHAR))) = ret) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_high_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_high_level_spec )))
.

Definition two_way_short_needle_derive_high_level_spec_by_low_level_spec := 
forall (needle_len_pre: Z) (needle_pre: Z) (haystack_len_pre: Z) (haystack_pre: Z) (nn_high_level_spec: Z) (hn_high_level_spec: Z) (needle0_high_level_spec: (@list Z)) (hay0_high_level_spec: (@list Z)) ,
  “ (haystack_len_pre = hn_high_level_spec) ” 
  &&  “ (needle_len_pre = nn_high_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_high_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_high_level_spec )
|--
EX (hay0_low_level_spec: (@list Z)) (needle0_low_level_spec: (@list Z)) (hn_low_level_spec: Z) (nn_low_level_spec: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) ,
  (“ (haystack_len_pre = hn_low_level_spec) ” 
  &&  “ (needle_len_pre = nn_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= 32) ” 
  &&  “ (0 < haystack_len_pre) ” 
  &&  “ (haystack_len_pre <= INT_MAX) ” 
  &&  “ (needle_len_pre <= haystack_len_pre) ” 
  &&  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (two_way_generic_prog (hay0_low_level_spec) (needle0_low_level_spec)) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec ))
  **
  ((EX retval_2,
  “ (haystack_pre > 0) ” 
  &&  “ (needle_pre > 0) ” 
  &&  “ (safeExec ATrue (return ((uchar_ptr_option_repr (haystack_pre) (retval_2) (sizeof(UCHAR))))) X_low_level_spec ) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_low_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec ))
  -*
  (EX ret retval,
  “ (match_post hay0_high_level_spec needle0_high_level_spec ret ) ” 
  &&  “ ((uchar_ptr_option_repr (haystack_pre) (retval) (sizeof(UCHAR))) = ret) ”
  &&  (UCharArray.full haystack_pre haystack_len_pre hay0_high_level_spec )
  **  (UCharArray.full needle_pre needle_len_pre needle0_high_level_spec )))
.

Definition critical_factorization_derive_long_needle_bind_spec_by_low_level_spec := 
forall (C: Type) ,
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (f_long_needle_bind_spec: ((Z * Z) -> (@program unit C))) (X_long_needle_bind_spec: (C -> (unit -> Prop))) (n0_long_needle_bind_spec: Z) (needle0_long_needle_bind_spec: (@list Z)) ,
  “ (safeExec ATrue (bind ((critical_factorization_prog (needle0_long_needle_bind_spec))) (f_long_needle_bind_spec)) X_long_needle_bind_spec ) ” 
  &&  “ (needle_len_pre = n0_long_needle_bind_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_long_needle_bind_spec )
  **  ((period_pre) # Int  |->_)
|--
EX (needle0_low_level_spec: (@list Z)) (n0_low_level_spec: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (critical_factorization_prog (needle0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_))
  **
  ((EX mp_2 retval_2,
  “ (safeExec ATrue (return ((maketuple (retval_2) (mp_2)))) X_low_level_spec ) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < needle_len_pre) ” 
  &&  “ ((mp_2 + retval_2 ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |-> mp_2))
  -*
  (EX mp retval,
  “ (safeExec ATrue (applyf (f_long_needle_bind_spec) ((maketuple (retval) (mp)))) X_long_needle_bind_spec ) ” 
  &&  “ (critical_factorization_spec needle0_long_needle_bind_spec (maketuple (retval) (mp)) ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_long_needle_bind_spec )
  **  ((period_pre) # Int  |-> mp)))
.

Definition critical_factorization_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (period_pre: Z) (needle_len_pre: Z) (needle_pre: Z) (f_bind_spec: ((Z * Z) -> (@program unit B))) (X_bind_spec: (B -> (unit -> Prop))) (n0_bind_spec: Z) (needle0_bind_spec: (@list Z)) ,
  “ (safeExec ATrue (bind ((critical_factorization_prog (needle0_bind_spec))) (f_bind_spec)) X_bind_spec ) ” 
  &&  “ (needle_len_pre = n0_bind_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_bind_spec )
  **  ((period_pre) # Int  |->_)
|--
EX (needle0_low_level_spec: (@list Z)) (n0_low_level_spec: Z) (X_low_level_spec: ((Z * Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (critical_factorization_prog (needle0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (needle_len_pre = n0_low_level_spec) ” 
  &&  “ (0 < needle_len_pre) ” 
  &&  “ (needle_len_pre <= INT_MAX) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |->_))
  **
  ((EX mp_2 retval_2,
  “ (safeExec ATrue (return ((maketuple (retval_2) (mp_2)))) X_low_level_spec ) ” 
  &&  “ (0 < mp_2) ” 
  &&  “ (mp_2 <= needle_len_pre) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < needle_len_pre) ” 
  &&  “ ((mp_2 + retval_2 ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_low_level_spec )
  **  ((period_pre) # Int  |-> mp_2))
  -*
  (EX mp retval,
  “ (safeExec ATrue (applyf (f_bind_spec) ((maketuple (retval) (mp)))) X_bind_spec ) ” 
  &&  “ (0 < mp) ” 
  &&  “ (mp <= needle_len_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < needle_len_pre) ” 
  &&  “ ((mp + retval ) <= needle_len_pre) ”
  &&  (UCharArray.full needle_pre needle_len_pre needle0_bind_spec )
  **  ((period_pre) # Int  |-> mp)))
.

