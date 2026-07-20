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
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import ast_lib.
Require Import malloc.
Require Import super_poly_sll2.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import safeexec_strategy_proof.

(*----- Function alpha_equiv -----*)

Definition alpha_equiv_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t1_pre <> 0)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t1_pre = 0)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t2_pre = 0)) (PreH2 : (t1_pre <> 0)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_5 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) <> (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : (retval = (list_Z_cmp (str1) (str2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (term1 = (TermVar (str1)))) (PreH5 : (term2 = (TermVar (str2)))) (PreH6 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t1_pre <> 0)) (PreH11 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition alpha_equiv_safety_wit_9 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : ((ctID (typ1)) <> (ctID (typ2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (term1 = (TermConst (typ1) (con1)))) (PreH5 : (term2 = (TermConst (typ2) (con2)))) (PreH6 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t1_pre <> 0)) (PreH11 : (0 <> (termtypeID (term1)))) (PreH12 : (1 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : ((ctID (typ1)) = (ctID (typ2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (term1 = (TermConst (typ1) (con1)))) (PreH5 : (term2 = (TermConst (typ2) (con2)))) (PreH6 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t1_pre <> 0)) (PreH11 : (0 <> (termtypeID (term1)))) (PreH12 : (1 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_11 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : ((ctID (typ1)) <> 0)) (PreH2 : ((ctID (typ1)) = (ctID (typ2)))) (PreH3 : (t1_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (term1 = (TermConst (typ1) (con1)))) (PreH6 : (term2 = (TermConst (typ2) (con2)))) (PreH7 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t1_pre <> 0)) (PreH12 : (0 <> (termtypeID (term1)))) (PreH13 : (1 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition alpha_equiv_safety_wit_12 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition alpha_equiv_safety_wit_13 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 <> (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition alpha_equiv_safety_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (PreH1 : ((qtID (qt1)) <> (qtID (qt2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH5 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH6 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t1_pre <> 0)) (PreH11 : (0 <> (termtypeID (term1)))) (PreH12 : (1 <> (termtypeID (term1)))) (PreH13 : (2 <> (termtypeID (term1)))) (PreH14 : (3 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_15 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (PreH1 : (retval = (list_Z_cmp (qv1) (qv2)))) (PreH2 : ((qtID (qt1)) = (qtID (qt2)))) (PreH3 : (t1_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH6 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH7 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t1_pre <> 0)) (PreH12 : (0 <> (termtypeID (term1)))) (PreH13 : (1 <> (termtypeID (term1)))) (PreH14 : (2 <> (termtypeID (term1)))) (PreH15 : (3 = (termtypeID (term1)))) ,
  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition alpha_equiv_safety_wit_16 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 <> (termtypeID (term1)))) (PreH9 : (3 <> (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ False ”
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 <> (termtypeID (term1)))) (PreH9 : (3 <> (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ False ”
).

Definition alpha_equiv_safety_wit_16_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 <> (termtypeID (term1)))) (PreH9 : (3 <> (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ False ”
.

Definition alpha_equiv_return_wit_1 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (PreH1 : (retval = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2)))))) (PreH2 : (retval_4 = retval_3)) (PreH3 : (retval_3 <> 0)) (PreH4 : (y1 <> 0)) (PreH5 : (y2 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH8 : ((qtID (qt1)) = (qtID (qt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH12 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 <> (termtypeID (term1)))) (PreH21 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  “ (retval = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : (retval = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2)))))) (PreH10 : (retval_4 = retval_3)) (PreH11 : (retval_3 <> 0)) (PreH12 : (y1 <> 0)) (PreH13 : (y2 <> 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH16 : ((qtID (qt1)) = (qtID (qt2)))) (PreH17 : (t1_pre <> 0)) (PreH18 : (t2_pre <> 0)) (PreH19 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH20 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH21 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH22 : (t1_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t2_pre <> 0)) (PreH25 : (t1_pre <> 0)) (PreH26 : (0 <> (termtypeID (term1)))) (PreH27 : (1 <> (termtypeID (term1)))) (PreH28 : (2 <> (termtypeID (term1)))) (PreH29 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  “ (retval = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_1_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : (retval = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2)))))) (PreH10 : (retval_4 = retval_3)) (PreH11 : (retval_3 <> 0)) (PreH12 : (y1 <> 0)) (PreH13 : (y2 <> 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH16 : ((qtID (qt1)) = (qtID (qt2)))) (PreH17 : (t1_pre <> 0)) (PreH18 : (t2_pre <> 0)) (PreH19 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH20 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH21 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH22 : (t1_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t2_pre <> 0)) (PreH25 : (t1_pre <> 0)) (PreH26 : (0 <> (termtypeID (term1)))) (PreH27 : (1 <> (termtypeID (term1)))) (PreH28 : (2 <> (termtypeID (term1)))) (PreH29 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  “ (retval = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_1_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval: Z) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : (retval = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2)))))) (PreH10 : (retval_4 = retval_3)) (PreH11 : (retval_3 <> 0)) (PreH12 : (y1 <> 0)) (PreH13 : (y2 <> 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH16 : ((qtID (qt1)) = (qtID (qt2)))) (PreH17 : (t1_pre <> 0)) (PreH18 : (t2_pre <> 0)) (PreH19 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH20 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH21 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH22 : (t1_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t2_pre <> 0)) (PreH25 : (t1_pre <> 0)) (PreH26 : (0 <> (termtypeID (term1)))) (PreH27 : (1 <> (termtypeID (term1)))) (PreH28 : (2 <> (termtypeID (term1)))) (PreH29 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_2 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) (PreH1 : (retval = (term_alpha_eqn (qterm1) (qterm2)))) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH4 : ((qtID (qt1)) = (qtID (qt2)))) (PreH5 : (t1_pre <> 0)) (PreH6 : (t2_pre <> 0)) (PreH7 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH8 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH9 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH10 : (t1_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (t2_pre <> 0)) (PreH13 : (t1_pre <> 0)) (PreH14 : (0 <> (termtypeID (term1)))) (PreH15 : (1 <> (termtypeID (term1)))) (PreH16 : (2 <> (termtypeID (term1)))) (PreH17 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  “ (retval = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : (retval = (term_alpha_eqn (qterm1) (qterm2)))) (PreH10 : (retval_2 = 0)) (PreH11 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH12 : ((qtID (qt1)) = (qtID (qt2)))) (PreH13 : (t1_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH16 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH17 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH18 : (t1_pre <> 0)) (PreH19 : (t2_pre <> 0)) (PreH20 : (t2_pre <> 0)) (PreH21 : (t1_pre <> 0)) (PreH22 : (0 <> (termtypeID (term1)))) (PreH23 : (1 <> (termtypeID (term1)))) (PreH24 : (2 <> (termtypeID (term1)))) (PreH25 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  “ (retval = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_2_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : (retval = (term_alpha_eqn (qterm1) (qterm2)))) (PreH10 : (retval_2 = 0)) (PreH11 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH12 : ((qtID (qt1)) = (qtID (qt2)))) (PreH13 : (t1_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH16 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH17 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH18 : (t1_pre <> 0)) (PreH19 : (t2_pre <> 0)) (PreH20 : (t2_pre <> 0)) (PreH21 : (t1_pre <> 0)) (PreH22 : (0 <> (termtypeID (term1)))) (PreH23 : (1 <> (termtypeID (term1)))) (PreH24 : (2 <> (termtypeID (term1)))) (PreH25 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  “ (retval = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_2_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : (retval = (term_alpha_eqn (qterm1) (qterm2)))) (PreH10 : (retval_2 = 0)) (PreH11 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH12 : ((qtID (qt1)) = (qtID (qt2)))) (PreH13 : (t1_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH16 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH17 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH18 : (t1_pre <> 0)) (PreH19 : (t2_pre <> 0)) (PreH20 : (t2_pre <> 0)) (PreH21 : (t1_pre <> 0)) (PreH22 : (0 <> (termtypeID (term1)))) (PreH23 : (1 <> (termtypeID (term1)))) (PreH24 : (2 <> (termtypeID (term1)))) (PreH25 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_3 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (PreH1 : ((qtID (qt1)) <> (qtID (qt2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH5 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH6 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t1_pre <> 0)) (PreH11 : (0 <> (termtypeID (term1)))) (PreH12 : (1 <> (termtypeID (term1)))) (PreH13 : (2 <> (termtypeID (term1)))) (PreH14 : (3 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : ((qtID (qt1)) <> (qtID (qt2)))) (PreH10 : (t1_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH13 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH14 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH15 : (t1_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (t1_pre <> 0)) (PreH19 : (0 <> (termtypeID (term1)))) (PreH20 : (1 <> (termtypeID (term1)))) (PreH21 : (2 <> (termtypeID (term1)))) (PreH22 : (3 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_3_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : ((qtID (qt1)) <> (qtID (qt2)))) (PreH10 : (t1_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH13 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH14 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH15 : (t1_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (t1_pre <> 0)) (PreH19 : (0 <> (termtypeID (term1)))) (PreH20 : (1 <> (termtypeID (term1)))) (PreH21 : (2 <> (termtypeID (term1)))) (PreH22 : (3 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_3_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (PreH1 : ((qtID (qt2)) <= INT_MAX)) (PreH2 : ((qtID (qt1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) <= INT_MAX)) (PreH4 : ((termtypeID (term1)) <= INT_MAX)) (PreH5 : ((qtID (qt2)) >= INT_MIN)) (PreH6 : ((qtID (qt1)) >= INT_MIN)) (PreH7 : ((termtypeID (term2)) >= INT_MIN)) (PreH8 : ((termtypeID (term1)) >= INT_MIN)) (PreH9 : ((qtID (qt1)) <> (qtID (qt2)))) (PreH10 : (t1_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH13 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH14 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH15 : (t1_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (t1_pre <> 0)) (PreH19 : (0 <> (termtypeID (term1)))) (PreH20 : (1 <> (termtypeID (term1)))) (PreH21 : (2 <> (termtypeID (term1)))) (PreH22 : (3 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_4 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH3 : (t1_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (term1 = (TermApply (lt1) (rt1)))) (PreH6 : (term2 = (TermApply (lt2) (rt2)))) (PreH7 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t1_pre <> 0)) (PreH12 : (0 <> (termtypeID (term1)))) (PreH13 : (1 <> (termtypeID (term1)))) (PreH14 : (2 = (termtypeID (term1)))) ,
  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermApply (lt1) (rt1)))) (PreH10 : (term2 = (TermApply (lt2) (rt2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 <> (termtypeID (term1)))) (PreH17 : (1 <> (termtypeID (term1)))) (PreH18 : (2 = (termtypeID (term1)))) ,
  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_4_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermApply (lt1) (rt1)))) (PreH10 : (term2 = (TermApply (lt2) (rt2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 <> (termtypeID (term1)))) (PreH17 : (1 <> (termtypeID (term1)))) (PreH18 : (2 = (termtypeID (term1)))) ,
  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_4_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermApply (lt1) (rt1)))) (PreH10 : (term2 = (TermApply (lt2) (rt2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 <> (termtypeID (term1)))) (PreH17 : (1 <> (termtypeID (term1)))) (PreH18 : (2 = (termtypeID (term1)))) ,
  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_5 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH3 : (retval <> 0)) (PreH4 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH5 : (t1_pre <> 0)) (PreH6 : (t2_pre <> 0)) (PreH7 : (term1 = (TermApply (lt1) (rt1)))) (PreH8 : (term2 = (TermApply (lt2) (rt2)))) (PreH9 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH10 : (t1_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (t2_pre <> 0)) (PreH13 : (t1_pre <> 0)) (PreH14 : (0 <> (termtypeID (term1)))) (PreH15 : (1 <> (termtypeID (term1)))) (PreH16 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH7 : (retval <> 0)) (PreH8 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermApply (lt1) (rt1)))) (PreH12 : (term2 = (TermApply (lt2) (rt2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_5_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH7 : (retval <> 0)) (PreH8 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermApply (lt1) (rt1)))) (PreH12 : (term2 = (TermApply (lt2) (rt2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_5_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH7 : (retval <> 0)) (PreH8 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermApply (lt1) (rt1)))) (PreH12 : (term2 = (TermApply (lt2) (rt2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_6 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH3 : (retval <> 0)) (PreH4 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH5 : (t1_pre <> 0)) (PreH6 : (t2_pre <> 0)) (PreH7 : (term1 = (TermApply (lt1) (rt1)))) (PreH8 : (term2 = (TermApply (lt2) (rt2)))) (PreH9 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH10 : (t1_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (t2_pre <> 0)) (PreH13 : (t1_pre <> 0)) (PreH14 : (0 <> (termtypeID (term1)))) (PreH15 : (1 <> (termtypeID (term1)))) (PreH16 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval_2 = 0)) (PreH6 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH7 : (retval <> 0)) (PreH8 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermApply (lt1) (rt1)))) (PreH12 : (term2 = (TermApply (lt2) (rt2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_6_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval_2 = 0)) (PreH6 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH7 : (retval <> 0)) (PreH8 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermApply (lt1) (rt1)))) (PreH12 : (term2 = (TermApply (lt2) (rt2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_6_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval_2 = 0)) (PreH6 : (retval_2 = (term_alpha_eqn (rt1) (rt2)))) (PreH7 : (retval <> 0)) (PreH8 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermApply (lt1) (rt1)))) (PreH12 : (term2 = (TermApply (lt2) (rt2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 = (termtypeID (term1)))) ,
  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_7 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : ((ctID (typ1)) <> 0)) (PreH2 : ((ctID (typ1)) = (ctID (typ2)))) (PreH3 : (t1_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (term1 = (TermConst (typ1) (con1)))) (PreH6 : (term2 = (TermConst (typ2) (con2)))) (PreH7 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t1_pre <> 0)) (PreH12 : (0 <> (termtypeID (term1)))) (PreH13 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : ((ctID (typ1)) <> 0)) (PreH14 : ((ctID (typ1)) = (ctID (typ2)))) (PreH15 : (t1_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (term1 = (TermConst (typ1) (con1)))) (PreH18 : (term2 = (TermConst (typ2) (con2)))) (PreH19 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH20 : (t1_pre <> 0)) (PreH21 : (t2_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t1_pre <> 0)) (PreH24 : (0 <> (termtypeID (term1)))) (PreH25 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_7_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : ((ctID (typ1)) <> 0)) (PreH14 : ((ctID (typ1)) = (ctID (typ2)))) (PreH15 : (t1_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (term1 = (TermConst (typ1) (con1)))) (PreH18 : (term2 = (TermConst (typ2) (con2)))) (PreH19 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH20 : (t1_pre <> 0)) (PreH21 : (t2_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t1_pre <> 0)) (PreH24 : (0 <> (termtypeID (term1)))) (PreH25 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_7_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : ((ctID (typ1)) <> 0)) (PreH14 : ((ctID (typ1)) = (ctID (typ2)))) (PreH15 : (t1_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (term1 = (TermConst (typ1) (con1)))) (PreH18 : (term2 = (TermConst (typ2) (con2)))) (PreH19 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH20 : (t1_pre <> 0)) (PreH21 : (t2_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t1_pre <> 0)) (PreH24 : (0 <> (termtypeID (term1)))) (PreH25 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_8 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con1 <> con2)) (PreH2 : ((ctID (typ1)) = 0)) (PreH3 : ((ctID (typ1)) = (ctID (typ2)))) (PreH4 : (t1_pre <> 0)) (PreH5 : (t2_pre <> 0)) (PreH6 : (term1 = (TermConst (typ1) (con1)))) (PreH7 : (term2 = (TermConst (typ2) (con2)))) (PreH8 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (t1_pre <> 0)) (PreH13 : (0 <> (termtypeID (term1)))) (PreH14 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : (con1 <> con2)) (PreH14 : ((ctID (typ1)) = 0)) (PreH15 : ((ctID (typ1)) = (ctID (typ2)))) (PreH16 : (t1_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (term1 = (TermConst (typ1) (con1)))) (PreH19 : (term2 = (TermConst (typ2) (con2)))) (PreH20 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH21 : (t1_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t1_pre <> 0)) (PreH25 : (0 <> (termtypeID (term1)))) (PreH26 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_8_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : (con1 <> con2)) (PreH14 : ((ctID (typ1)) = 0)) (PreH15 : ((ctID (typ1)) = (ctID (typ2)))) (PreH16 : (t1_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (term1 = (TermConst (typ1) (con1)))) (PreH19 : (term2 = (TermConst (typ2) (con2)))) (PreH20 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH21 : (t1_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t1_pre <> 0)) (PreH25 : (0 <> (termtypeID (term1)))) (PreH26 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_8_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : (con1 <> con2)) (PreH14 : ((ctID (typ1)) = 0)) (PreH15 : ((ctID (typ1)) = (ctID (typ2)))) (PreH16 : (t1_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (term1 = (TermConst (typ1) (con1)))) (PreH19 : (term2 = (TermConst (typ2) (con2)))) (PreH20 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH21 : (t1_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t1_pre <> 0)) (PreH25 : (0 <> (termtypeID (term1)))) (PreH26 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_9 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con1 = con2)) (PreH2 : ((ctID (typ1)) = 0)) (PreH3 : ((ctID (typ1)) = (ctID (typ2)))) (PreH4 : (t1_pre <> 0)) (PreH5 : (t2_pre <> 0)) (PreH6 : (term1 = (TermConst (typ1) (con1)))) (PreH7 : (term2 = (TermConst (typ2) (con2)))) (PreH8 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (t1_pre <> 0)) (PreH13 : (0 <> (termtypeID (term1)))) (PreH14 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : (con1 = con2)) (PreH14 : ((ctID (typ1)) = 0)) (PreH15 : ((ctID (typ1)) = (ctID (typ2)))) (PreH16 : (t1_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (term1 = (TermConst (typ1) (con1)))) (PreH19 : (term2 = (TermConst (typ2) (con2)))) (PreH20 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH21 : (t1_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t1_pre <> 0)) (PreH25 : (0 <> (termtypeID (term1)))) (PreH26 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_9_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : (con1 = con2)) (PreH14 : ((ctID (typ1)) = 0)) (PreH15 : ((ctID (typ1)) = (ctID (typ2)))) (PreH16 : (t1_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (term1 = (TermConst (typ1) (con1)))) (PreH19 : (term2 = (TermConst (typ2) (con2)))) (PreH20 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH21 : (t1_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t1_pre <> 0)) (PreH25 : (0 <> (termtypeID (term1)))) (PreH26 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_9_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : (con1 = con2)) (PreH14 : ((ctID (typ1)) = 0)) (PreH15 : ((ctID (typ1)) = (ctID (typ2)))) (PreH16 : (t1_pre <> 0)) (PreH17 : (t2_pre <> 0)) (PreH18 : (term1 = (TermConst (typ1) (con1)))) (PreH19 : (term2 = (TermConst (typ2) (con2)))) (PreH20 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH21 : (t1_pre <> 0)) (PreH22 : (t2_pre <> 0)) (PreH23 : (t2_pre <> 0)) (PreH24 : (t1_pre <> 0)) (PreH25 : (0 <> (termtypeID (term1)))) (PreH26 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_10 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : ((ctID (typ1)) <> (ctID (typ2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (term1 = (TermConst (typ1) (con1)))) (PreH5 : (term2 = (TermConst (typ2) (con2)))) (PreH6 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t1_pre <> 0)) (PreH11 : (0 <> (termtypeID (term1)))) (PreH12 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : ((ctID (typ1)) <> (ctID (typ2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (term1 = (TermConst (typ1) (con1)))) (PreH17 : (term2 = (TermConst (typ2) (con2)))) (PreH18 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH19 : (t1_pre <> 0)) (PreH20 : (t2_pre <> 0)) (PreH21 : (t2_pre <> 0)) (PreH22 : (t1_pre <> 0)) (PreH23 : (0 <> (termtypeID (term1)))) (PreH24 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_10_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : ((ctID (typ1)) <> (ctID (typ2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (term1 = (TermConst (typ1) (con1)))) (PreH17 : (term2 = (TermConst (typ2) (con2)))) (PreH18 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH19 : (t1_pre <> 0)) (PreH20 : (t2_pre <> 0)) (PreH21 : (t2_pre <> 0)) (PreH22 : (t1_pre <> 0)) (PreH23 : (0 <> (termtypeID (term1)))) (PreH24 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_10_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (typ2: const_type) (con2: Z) (typ1: const_type) (con1: Z) (PreH1 : (con2 <= INT_MAX)) (PreH2 : (con1 <= INT_MAX)) (PreH3 : ((ctID (typ2)) <= INT_MAX)) (PreH4 : ((ctID (typ1)) <= INT_MAX)) (PreH5 : ((termtypeID (term2)) <= INT_MAX)) (PreH6 : ((termtypeID (term1)) <= INT_MAX)) (PreH7 : (con2 >= INT_MIN)) (PreH8 : (con1 >= INT_MIN)) (PreH9 : ((ctID (typ2)) >= INT_MIN)) (PreH10 : ((ctID (typ1)) >= INT_MIN)) (PreH11 : ((termtypeID (term2)) >= INT_MIN)) (PreH12 : ((termtypeID (term1)) >= INT_MIN)) (PreH13 : ((ctID (typ1)) <> (ctID (typ2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (term1 = (TermConst (typ1) (con1)))) (PreH17 : (term2 = (TermConst (typ2) (con2)))) (PreH18 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH19 : (t1_pre <> 0)) (PreH20 : (t2_pre <> 0)) (PreH21 : (t2_pre <> 0)) (PreH22 : (t1_pre <> 0)) (PreH23 : (0 <> (termtypeID (term1)))) (PreH24 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_11 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (list_Z_cmp (str1) (str2)))) (PreH3 : (t1_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (term1 = (TermVar (str1)))) (PreH6 : (term2 = (TermVar (str2)))) (PreH7 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t1_pre <> 0)) (PreH12 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (list_Z_cmp (str1) (str2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermVar (str1)))) (PreH10 : (term2 = (TermVar (str2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_11_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (list_Z_cmp (str1) (str2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermVar (str1)))) (PreH10 : (term2 = (TermVar (str2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_11_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (list_Z_cmp (str1) (str2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermVar (str1)))) (PreH10 : (term2 = (TermVar (str2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_12 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (str1) (str2)))) (PreH3 : (t1_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (term1 = (TermVar (str1)))) (PreH6 : (term2 = (TermVar (str2)))) (PreH7 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t1_pre <> 0)) (PreH12 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (list_Z_cmp (str1) (str2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermVar (str1)))) (PreH10 : (term2 = (TermVar (str2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_12_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (list_Z_cmp (str1) (str2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermVar (str1)))) (PreH10 : (term2 = (TermVar (str2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  “ (1 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_12_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (retval = (list_Z_cmp (str1) (str2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermVar (str1)))) (PreH10 : (term2 = (TermVar (str2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 = (termtypeID (term1)))) ,
  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_13 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) <> (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : ((termtypeID (term1)) <> (termtypeID (term2)))) (PreH6 : (t1_pre <> 0)) (PreH7 : (t2_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t1_pre <> 0)) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_13_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : ((termtypeID (term1)) <> (termtypeID (term2)))) (PreH6 : (t1_pre <> 0)) (PreH7 : (t2_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t1_pre <> 0)) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_13_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term2)) <= INT_MAX)) (PreH2 : ((termtypeID (term1)) <= INT_MAX)) (PreH3 : ((termtypeID (term2)) >= INT_MIN)) (PreH4 : ((termtypeID (term1)) >= INT_MIN)) (PreH5 : ((termtypeID (term1)) <> (termtypeID (term2)))) (PreH6 : (t1_pre <> 0)) (PreH7 : (t2_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t1_pre <> 0)) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_14 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t1_pre = 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t1_pre = 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_14_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t1_pre = 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_14_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t1_pre = 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_return_wit_15 := 
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t2_pre = 0)) (PreH2 : (t1_pre <> 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t2_pre = 0)) (PreH2 : (t1_pre <> 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
).

Definition alpha_equiv_return_wit_15_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t2_pre = 0)) (PreH2 : (t1_pre <> 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (0 = (term_alpha_eqn (term1) (term2))) ”
.

Definition alpha_equiv_return_wit_15_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t2_pre = 0)) (PreH2 : (t1_pre <> 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : (t2_pre <> 0)) (PreH2 : (t1_pre <> 0)) ,
  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
|--
  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ”
  &&  (store_term t1_pre term1 )
  **  (store_term t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 0) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ”
.

Definition alpha_equiv_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 0) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 = (termtypeID (term1))) ”
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_2 := alpha_equiv_partial_solve_wit_2_pure -> alpha_equiv_partial_solve_wit_2_aux.

Definition alpha_equiv_partial_solve_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z: Z) (y: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (t1_pre <> 0)) (PreH2 : (t2_pre <> 0)) (PreH3 : (term1 = (TermVar (str1)))) (PreH4 : (term2 = (TermVar (str2)))) (PreH5 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH6 : (t1_pre <> 0)) (PreH7 : (t2_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t1_pre <> 0)) (PreH10 : (0 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
  **  (store_string y str1 )
  **  (store_string z str2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermVar (str1))) ” 
  &&  “ (term2 = (TermVar (str2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 = (termtypeID (term1))) ”
  &&  (store_string y str1 )
  **  (store_string z str2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
.

Definition alpha_equiv_partial_solve_wit_4_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 1) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ”
.

Definition alpha_equiv_partial_solve_wit_4_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 1) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 = (termtypeID (term1))) ”
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_4 := alpha_equiv_partial_solve_wit_4_pure -> alpha_equiv_partial_solve_wit_4_aux.

Definition alpha_equiv_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 2) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ”
.

Definition alpha_equiv_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 2) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 = (termtypeID (term1))) ”
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_5 := alpha_equiv_partial_solve_wit_5_pure -> alpha_equiv_partial_solve_wit_5_aux.

Definition alpha_equiv_partial_solve_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (PreH1 : (t1_pre <> 0)) (PreH2 : (t2_pre <> 0)) (PreH3 : (term1 = (TermApply (lt1) (rt1)))) (PreH4 : (term2 = (TermApply (lt2) (rt2)))) (PreH5 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH6 : (t1_pre <> 0)) (PreH7 : (t2_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t1_pre <> 0)) (PreH10 : (0 <> (termtypeID (term1)))) (PreH11 : (1 <> (termtypeID (term1)))) (PreH12 : (2 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term y1 lt1 )
  **  (store_term z1 rt1 )
  **  (store_term y2 lt2 )
  **  (store_term z2 rt2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermApply (lt1) (rt1))) ” 
  &&  “ (term2 = (TermApply (lt2) (rt2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 = (termtypeID (term1))) ”
  &&  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
.

Definition alpha_equiv_partial_solve_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (lt2: term) (rt2: term) (lt1: term) (rt1: term) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (term_alpha_eqn (lt1) (lt2)))) (PreH3 : (t1_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (term1 = (TermApply (lt1) (rt1)))) (PreH6 : (term2 = (TermApply (lt2) (rt2)))) (PreH7 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t1_pre <> 0)) (PreH12 : (0 <> (termtypeID (term1)))) (PreH13 : (1 <> (termtypeID (term1)))) (PreH14 : (2 = (termtypeID (term1)))) ,
  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
|--
  “ (retval <> 0) ” 
  &&  “ (retval = (term_alpha_eqn (lt1) (lt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermApply (lt1) (rt1))) ” 
  &&  “ (term2 = (TermApply (lt2) (rt2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 = (termtypeID (term1))) ”
  &&  (store_term z1 rt1 )
  **  (store_term z2 rt2 )
  **  (store_term y1 lt1 )
  **  (store_term y2 lt2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
.

Definition alpha_equiv_partial_solve_wit_8_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 <> (termtypeID (term1)))) (PreH9 : (3 = (termtypeID (term1)))) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 3) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ”
.

Definition alpha_equiv_partial_solve_wit_8_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (PreH1 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (t2_pre <> 0)) (PreH5 : (t1_pre <> 0)) (PreH6 : (0 <> (termtypeID (term1)))) (PreH7 : (1 <> (termtypeID (term1)))) (PreH8 : (2 <> (termtypeID (term1)))) (PreH9 : (3 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
|--
  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ ((termtypeID (term1)) = 3) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1_pre term1 )
  **  (store_term' t2_pre term2 )
.

Definition alpha_equiv_partial_solve_wit_8 := alpha_equiv_partial_solve_wit_8_pure -> alpha_equiv_partial_solve_wit_8_aux.

Definition alpha_equiv_partial_solve_wit_9 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (PreH1 : ((qtID (qt1)) = (qtID (qt2)))) (PreH2 : (t1_pre <> 0)) (PreH3 : (t2_pre <> 0)) (PreH4 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH5 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH6 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (t1_pre <> 0)) (PreH11 : (0 <> (termtypeID (term1)))) (PreH12 : (1 <> (termtypeID (term1)))) (PreH13 : (2 <> (termtypeID (term1)))) (PreH14 : (3 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
|--
  “ ((qtID (qt1)) = (qtID (qt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
.

Definition alpha_equiv_partial_solve_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (qv1) (qv2)))) (PreH3 : ((qtID (qt1)) = (qtID (qt2)))) (PreH4 : (t1_pre <> 0)) (PreH5 : (t2_pre <> 0)) (PreH6 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH7 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH8 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (t1_pre <> 0)) (PreH13 : (0 <> (termtypeID (term1)))) (PreH14 : (1 <> (termtypeID (term1)))) (PreH15 : (2 <> (termtypeID (term1)))) (PreH16 : (3 = (termtypeID (term1)))) ,
  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  “ (retval = 0) ” 
  &&  “ (retval = (list_Z_cmp (qv1) (qv2))) ” 
  &&  “ ((qtID (qt1)) = (qtID (qt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
.

Definition alpha_equiv_partial_solve_wit_11 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (list_Z_cmp (qv1) (qv2)))) (PreH3 : ((qtID (qt1)) = (qtID (qt2)))) (PreH4 : (t1_pre <> 0)) (PreH5 : (t2_pre <> 0)) (PreH6 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH7 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH8 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (t2_pre <> 0)) (PreH12 : (t1_pre <> 0)) (PreH13 : (0 <> (termtypeID (term1)))) (PreH14 : (1 <> (termtypeID (term1)))) (PreH15 : (2 <> (termtypeID (term1)))) (PreH16 : (3 = (termtypeID (term1)))) ,
  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  “ (retval <> 0) ” 
  &&  “ (retval = (list_Z_cmp (qv1) (qv2))) ” 
  &&  “ ((qtID (qt1)) = (qtID (qt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  (store_string y1 qv1 )
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
.

Definition alpha_equiv_partial_solve_wit_12 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (PreH1 : (y1 <> 0)) (PreH2 : (y2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval = (list_Z_cmp (qv1) (qv2)))) (PreH5 : ((qtID (qt1)) = (qtID (qt2)))) (PreH6 : (t1_pre <> 0)) (PreH7 : (t2_pre <> 0)) (PreH8 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH9 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH10 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH11 : (t1_pre <> 0)) (PreH12 : (t2_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t1_pre <> 0)) (PreH15 : (0 <> (termtypeID (term1)))) (PreH16 : (1 <> (termtypeID (term1)))) (PreH17 : (2 <> (termtypeID (term1)))) (PreH18 : (3 = (termtypeID (term1)))) ,
  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
  **  (store_term z2 qterm2 )
|--
  “ (y1 <> 0) ” 
  &&  “ (y2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (list_Z_cmp (qv1) (qv2))) ” 
  &&  “ ((qtID (qt1)) = (qtID (qt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
.

Definition alpha_equiv_partial_solve_wit_13_pure := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (y1 <> 0)) (PreH3 : (y2 <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH6 : ((qtID (qt1)) = (qtID (qt2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH10 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 <> (termtypeID (term1)))) (PreH17 : (1 <> (termtypeID (term1)))) (PreH18 : (2 <> (termtypeID (term1)))) (PreH19 : (3 = (termtypeID (term1)))) ,
  (store_term z2 qterm2 )
  **  (store_term retval qterm2 )
  **  ((( &( "t21" ) )) # Ptr  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
|--
  “ (y1 <> 0) ” 
  &&  “ (y2 <> 0) ” 
  &&  “ (retval <> 0) ”
.

Definition alpha_equiv_partial_solve_wit_13_aux := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (y1 <> 0)) (PreH3 : (y2 <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (list_Z_cmp (qv1) (qv2)))) (PreH6 : ((qtID (qt1)) = (qtID (qt2)))) (PreH7 : (t1_pre <> 0)) (PreH8 : (t2_pre <> 0)) (PreH9 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH10 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH11 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH12 : (t1_pre <> 0)) (PreH13 : (t2_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t1_pre <> 0)) (PreH16 : (0 <> (termtypeID (term1)))) (PreH17 : (1 <> (termtypeID (term1)))) (PreH18 : (2 <> (termtypeID (term1)))) (PreH19 : (3 = (termtypeID (term1)))) ,
  (store_term z2 qterm2 )
  **  (store_term retval qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
|--
  “ (y1 <> 0) ” 
  &&  “ (y2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (y1 <> 0) ” 
  &&  “ (y2 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (list_Z_cmp (qv1) (qv2))) ” 
  &&  “ ((qtID (qt1)) = (qtID (qt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  (store_term retval qterm2 )
  **  (store_string y2 qv2 )
  **  (store_string y1 qv1 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
.

Definition alpha_equiv_partial_solve_wit_13 := alpha_equiv_partial_solve_wit_13_pure -> alpha_equiv_partial_solve_wit_13_aux.

Definition alpha_equiv_partial_solve_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = retval_2)) (PreH2 : (retval_2 <> 0)) (PreH3 : (y1 <> 0)) (PreH4 : (y2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (list_Z_cmp (qv1) (qv2)))) (PreH7 : ((qtID (qt1)) = (qtID (qt2)))) (PreH8 : (t1_pre <> 0)) (PreH9 : (t2_pre <> 0)) (PreH10 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH11 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH12 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH13 : (t1_pre <> 0)) (PreH14 : (t2_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t1_pre <> 0)) (PreH17 : (0 <> (termtypeID (term1)))) (PreH18 : (1 <> (termtypeID (term1)))) (PreH19 : (2 <> (termtypeID (term1)))) (PreH20 : (3 = (termtypeID (term1)))) ,
  (store_term retval_2 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_term z1 qterm1 )
|--
  “ (retval_3 = retval_2) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (y1 <> 0) ” 
  &&  “ (y2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (list_Z_cmp (qv1) (qv2))) ” 
  &&  “ ((qtID (qt1)) = (qtID (qt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  (store_term z1 qterm1 )
  **  (store_term retval_3 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
.

Definition alpha_equiv_partial_solve_wit_15 := 
forall (t2_pre: Z) (t1_pre: Z) (term2: term) (term1: term) (z2: Z) (z1: Z) (y2: Z) (y1: Z) (qt2: quant_type) (qv2: (@list Z)) (qterm2: term) (qt1: quant_type) (qv1: (@list Z)) (qterm1: term) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2)))))) (PreH2 : (retval_3 = retval_2)) (PreH3 : (retval_2 <> 0)) (PreH4 : (y1 <> 0)) (PreH5 : (y2 <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (list_Z_cmp (qv1) (qv2)))) (PreH8 : ((qtID (qt1)) = (qtID (qt2)))) (PreH9 : (t1_pre <> 0)) (PreH10 : (t2_pre <> 0)) (PreH11 : (term1 = (TermQuant (qt1) (qv1) (qterm1)))) (PreH12 : (term2 = (TermQuant (qt2) (qv2) (qterm2)))) (PreH13 : ((termtypeID (term1)) = (termtypeID (term2)))) (PreH14 : (t1_pre <> 0)) (PreH15 : (t2_pre <> 0)) (PreH16 : (t2_pre <> 0)) (PreH17 : (t1_pre <> 0)) (PreH18 : (0 <> (termtypeID (term1)))) (PreH19 : (1 <> (termtypeID (term1)))) (PreH20 : (2 <> (termtypeID (term1)))) (PreH21 : (3 = (termtypeID (term1)))) ,
  (store_term z1 qterm1 )
  **  (store_term retval_3 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
|--
  “ (retval_4 = (term_alpha_eqn (qterm1) ((term_subst_v (qv1) (qv2) (qterm2))))) ” 
  &&  “ (retval_3 = retval_2) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (y1 <> 0) ” 
  &&  “ (y2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (list_Z_cmp (qv1) (qv2))) ” 
  &&  “ ((qtID (qt1)) = (qtID (qt2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ” 
  &&  “ ((termtypeID (term1)) = (termtypeID (term2))) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t2_pre <> 0) ” 
  &&  “ (t1_pre <> 0) ” 
  &&  “ (0 <> (termtypeID (term1))) ” 
  &&  “ (1 <> (termtypeID (term1))) ” 
  &&  “ (2 <> (termtypeID (term1))) ” 
  &&  “ (3 = (termtypeID (term1))) ”
  &&  (store_term retval_3 (term_subst_v (qv1) (qv2) (qterm2)) )
  **  (store_term z1 qterm1 )
  **  (store_string y1 qv1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
.

Definition alpha_equiv_which_implies_wit_1 := 
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  (store_term t1 term1 )
  **  (store_term t2 term2 )
|--
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ”
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
) \/
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  (store_term t1 term1 )
  **  (store_term t2 term2 )
|--
  “ (t2 <> 0) ” 
  &&  “ (t1 <> 0) ”
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
).

Definition alpha_equiv_which_implies_wit_1_split_goal_1 := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  (store_term t1 term1 )
  **  (store_term t2 term2 )
|--
  “ (t2 <> 0) ”
.

Definition alpha_equiv_which_implies_wit_1_split_goal_2 := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  (store_term t1 term1 )
  **  (store_term t2 term2 )
|--
  “ (t1 <> 0) ”
.

Definition alpha_equiv_which_implies_wit_1_split_goal_spatial := 
forall (term2: term) (term1: term) (t1: Z) (t2: Z) ,
  (store_term t1 term1 )
  **  (store_term t2 term2 )
|--
  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
.

Definition alpha_equiv_which_implies_wit_2 := 
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 0)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z: Z)  (y: Z)  (str2: (@list Z))  (str1: (@list Z)) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermVar (str1))) ” 
  &&  “ (term2 = (TermVar (str2))) ”
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
  **  (store_string y str1 )
  **  (store_string z str2 )
) \/
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 0)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z: Z)  (y: Z)  (str2: (@list Z))  (str1: (@list Z)) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermVar (str1))) ” 
  &&  “ (term2 = (TermVar (str2))) ”
  &&  ((&((t1)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> z)
  **  (store_string y str1 )
  **  (store_string z str2 )
).

Definition alpha_equiv_which_implies_wit_3 := 
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 1)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (typ2: const_type)  (con2: Z)  (typ1: const_type)  (con1: Z) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermConst (typ1) (con1))) ” 
  &&  “ (term2 = (TermConst (typ2) (con2))) ”
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
) \/
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 1)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (typ2: const_type)  (con2: Z)  (typ1: const_type)  (con1: Z) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermConst (typ1) (con1))) ” 
  &&  “ (term2 = (TermConst (typ2) (con2))) ”
  &&  ((&((t1)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ1)))
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con2)
).

Definition alpha_equiv_which_implies_wit_4 := 
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 2)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z2: Z)  (z1: Z)  (y2: Z)  (y1: Z)  (lt2: term)  (rt2: term)  (lt1: term)  (rt1: term) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermApply (lt1) (rt1))) ” 
  &&  “ (term2 = (TermApply (lt2) (rt2))) ”
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term y1 lt1 )
  **  (store_term z1 rt1 )
  **  (store_term y2 lt2 )
  **  (store_term z2 rt2 )
) \/
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 2)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z2: Z)  (z1: Z)  (y2: Z)  (y1: Z)  (lt2: term)  (rt2: term)  (lt1: term)  (rt1: term) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermApply (lt1) (rt1))) ” 
  &&  “ (term2 = (TermApply (lt2) (rt2))) ”
  &&  ((&((t1)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y2)
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z2)
  **  (store_term y1 lt1 )
  **  (store_term z1 rt1 )
  **  (store_term y2 lt2 )
  **  (store_term z2 rt2 )
).

Definition alpha_equiv_which_implies_wit_5 := 
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 3)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z2: Z)  (z1: Z)  (y2: Z)  (y1: Z)  (qt2: quant_type)  (qv2: (@list Z))  (qterm2: term)  (qt1: quant_type)  (qv1: (@list Z))  (qterm1: term) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ”
  &&  ((&((t1)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term1)))
  **  ((&((t2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (term2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
) \/
(
forall (term2: term) (term1: term) (t1: Z) (t2: Z) (PreH1 : (t1 <> 0)) (PreH2 : (t2 <> 0)) (PreH3 : ((termtypeID (term1)) = 3)) (PreH4 : ((termtypeID (term1)) = (termtypeID (term2)))) ,
  (store_term' t1 term1 )
  **  (store_term' t2 term2 )
|--
  EX (z2: Z)  (z1: Z)  (y2: Z)  (y1: Z)  (qt2: quant_type)  (qv2: (@list Z))  (qterm2: term)  (qt1: quant_type)  (qv1: (@list Z))  (qterm1: term) ,
  “ (t1 <> 0) ” 
  &&  “ (t2 <> 0) ” 
  &&  “ (term1 = (TermQuant (qt1) (qv1) (qterm1))) ” 
  &&  “ (term2 = (TermQuant (qt2) (qv2) (qterm2))) ”
  &&  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt1)))
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt2)))
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y2)
  **  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z1)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z2)
  **  (store_string y1 qv1 )
  **  (store_term z1 qterm1 )
  **  (store_string y2 qv2 )
  **  (store_term z2 qterm2 )
).

Definition alpha_equiv_which_implies_wit_6 := 
(
forall (qv2: (@list Z)) (qv1: (@list Z)) (t1: Z) (v: Z) (t2: Z) (v_2: Z) ,
  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v)
  **  (store_string v qv1 )
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v_2)
  **  (store_string v_2 qv2 )
|--
  “ (v <> 0) ” 
  &&  “ (v_2 <> 0) ”
  &&  ((&((t1)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v)
  **  ((&((t2)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> v_2)
  **  (store_string v qv1 )
  **  (store_string v_2 qv2 )
) \/
(
forall (qv2: (@list Z)) (qv1: (@list Z)) (v: Z) (v_2: Z) ,
  (store_string v qv1 )
  **  (store_string v_2 qv2 )
|--
  “ (v_2 <> 0) ” 
  &&  “ (v <> 0) ”
  &&  (store_string v qv1 )
  **  (store_string v_2 qv2 )
).

Definition alpha_equiv_which_implies_wit_6_split_goal_1 := 
forall (qv2: (@list Z)) (qv1: (@list Z)) (v: Z) (v_2: Z) ,
  (store_string v qv1 )
  **  (store_string v_2 qv2 )
|--
  “ (v_2 <> 0) ”
.

Definition alpha_equiv_which_implies_wit_6_split_goal_2 := 
forall (qv2: (@list Z)) (qv1: (@list Z)) (v: Z) (v_2: Z) ,
  (store_string v qv1 )
  **  (store_string v_2 qv2 )
|--
  “ (v <> 0) ”
.

Definition alpha_equiv_which_implies_wit_6_split_goal_spatial := 
forall (qv2: (@list Z)) (qv1: (@list Z)) (v: Z) (v_2: Z) ,
  (store_string v qv1 )
  **  (store_string v_2 qv2 )
|--
  (store_string v qv1 )
  **  (store_string v_2 qv2 )
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.

Axiom proof_of_alpha_equiv_safety_wit_1 : alpha_equiv_safety_wit_1.
Axiom proof_of_alpha_equiv_safety_wit_2 : alpha_equiv_safety_wit_2.
Axiom proof_of_alpha_equiv_safety_wit_3 : alpha_equiv_safety_wit_3.
Axiom proof_of_alpha_equiv_safety_wit_4 : alpha_equiv_safety_wit_4.
Axiom proof_of_alpha_equiv_safety_wit_5 : alpha_equiv_safety_wit_5.
Axiom proof_of_alpha_equiv_safety_wit_6 : alpha_equiv_safety_wit_6.
Axiom proof_of_alpha_equiv_safety_wit_7 : alpha_equiv_safety_wit_7.
Axiom proof_of_alpha_equiv_safety_wit_8 : alpha_equiv_safety_wit_8.
Axiom proof_of_alpha_equiv_safety_wit_9 : alpha_equiv_safety_wit_9.
Axiom proof_of_alpha_equiv_safety_wit_10 : alpha_equiv_safety_wit_10.
Axiom proof_of_alpha_equiv_safety_wit_11 : alpha_equiv_safety_wit_11.
Axiom proof_of_alpha_equiv_safety_wit_12 : alpha_equiv_safety_wit_12.
Axiom proof_of_alpha_equiv_safety_wit_13 : alpha_equiv_safety_wit_13.
Axiom proof_of_alpha_equiv_safety_wit_14 : alpha_equiv_safety_wit_14.
Axiom proof_of_alpha_equiv_safety_wit_15 : alpha_equiv_safety_wit_15.
Axiom proof_of_alpha_equiv_safety_wit_16 : alpha_equiv_safety_wit_16.
Axiom proof_of_alpha_equiv_return_wit_1 : alpha_equiv_return_wit_1.
Axiom proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Axiom proof_of_alpha_equiv_return_wit_3 : alpha_equiv_return_wit_3.
Axiom proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Axiom proof_of_alpha_equiv_return_wit_5 : alpha_equiv_return_wit_5.
Axiom proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Axiom proof_of_alpha_equiv_return_wit_7 : alpha_equiv_return_wit_7.
Axiom proof_of_alpha_equiv_return_wit_8 : alpha_equiv_return_wit_8.
Axiom proof_of_alpha_equiv_return_wit_9 : alpha_equiv_return_wit_9.
Axiom proof_of_alpha_equiv_return_wit_10 : alpha_equiv_return_wit_10.
Axiom proof_of_alpha_equiv_return_wit_11 : alpha_equiv_return_wit_11.
Axiom proof_of_alpha_equiv_return_wit_12 : alpha_equiv_return_wit_12.
Axiom proof_of_alpha_equiv_return_wit_13 : alpha_equiv_return_wit_13.
Axiom proof_of_alpha_equiv_return_wit_14 : alpha_equiv_return_wit_14.
Axiom proof_of_alpha_equiv_return_wit_15 : alpha_equiv_return_wit_15.
Axiom proof_of_alpha_equiv_partial_solve_wit_1 : alpha_equiv_partial_solve_wit_1.
Axiom proof_of_alpha_equiv_partial_solve_wit_2_pure : alpha_equiv_partial_solve_wit_2_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_2 : alpha_equiv_partial_solve_wit_2.
Axiom proof_of_alpha_equiv_partial_solve_wit_3 : alpha_equiv_partial_solve_wit_3.
Axiom proof_of_alpha_equiv_partial_solve_wit_4_pure : alpha_equiv_partial_solve_wit_4_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_4 : alpha_equiv_partial_solve_wit_4.
Axiom proof_of_alpha_equiv_partial_solve_wit_5_pure : alpha_equiv_partial_solve_wit_5_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_5 : alpha_equiv_partial_solve_wit_5.
Axiom proof_of_alpha_equiv_partial_solve_wit_6 : alpha_equiv_partial_solve_wit_6.
Axiom proof_of_alpha_equiv_partial_solve_wit_7 : alpha_equiv_partial_solve_wit_7.
Axiom proof_of_alpha_equiv_partial_solve_wit_8_pure : alpha_equiv_partial_solve_wit_8_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_8 : alpha_equiv_partial_solve_wit_8.
Axiom proof_of_alpha_equiv_partial_solve_wit_9 : alpha_equiv_partial_solve_wit_9.
Axiom proof_of_alpha_equiv_partial_solve_wit_10 : alpha_equiv_partial_solve_wit_10.
Axiom proof_of_alpha_equiv_partial_solve_wit_11 : alpha_equiv_partial_solve_wit_11.
Axiom proof_of_alpha_equiv_partial_solve_wit_12 : alpha_equiv_partial_solve_wit_12.
Axiom proof_of_alpha_equiv_partial_solve_wit_13_pure : alpha_equiv_partial_solve_wit_13_pure.
Axiom proof_of_alpha_equiv_partial_solve_wit_13 : alpha_equiv_partial_solve_wit_13.
Axiom proof_of_alpha_equiv_partial_solve_wit_14 : alpha_equiv_partial_solve_wit_14.
Axiom proof_of_alpha_equiv_partial_solve_wit_15 : alpha_equiv_partial_solve_wit_15.
Axiom proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Axiom proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Axiom proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Axiom proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Axiom proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Axiom proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.

End VC_Correct.
