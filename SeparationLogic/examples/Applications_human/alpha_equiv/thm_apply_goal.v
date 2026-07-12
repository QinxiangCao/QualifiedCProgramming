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

(*----- Function sub_thm -----*)

Definition sub_thm_safety_wit_1 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_thm_safety_wit_2 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (PreH1 : (thm_pre <> 0)) (PreH2 : (l = (cons (vs) (l0)))) (PreH3 : (lis_pre <> 0)) ,
  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sub_thm_safety_wit_3 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (PreH1 : ((termtypeID (t)) <> 3)) (PreH2 : (thm_pre <> 0)) (PreH3 : (l = (cons (vs) (l0)))) (PreH4 : (lis_pre <> 0)) ,
  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sub_thm_return_wit_1 := 
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (PreH1 : ((termtypeID (t)) <> 3)) (PreH2 : (thm_pre <> 0)) (PreH3 : (l = (cons (vs) (l0)))) (PreH4 : (lis_pre <> 0)) ,
  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre 0 t l )
) \/
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (PreH1 : ((termtypeID (t)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) >= INT_MIN)) (PreH3 : ((termtypeID (t)) <> 3)) (PreH4 : (thm_pre <> 0)) (PreH5 : (l = (cons (vs) (l0)))) (PreH6 : (lis_pre <> 0)) ,
  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre 0 t l )
).

Definition sub_thm_return_wit_1_split_goal_spatial := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (PreH1 : ((termtypeID (t)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) >= INT_MIN)) (PreH3 : ((termtypeID (t)) <> 3)) (PreH4 : (thm_pre <> 0)) (PreH5 : (l = (cons (vs) (l0)))) (PreH6 : (lis_pre <> 0)) ,
  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre 0 t l )
.

Definition sub_thm_return_wit_2 := 
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 = z)) (PreH2 : (thm_pre <> 0)) (PreH3 : (lis_cur <> 0)) (PreH4 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH5 : (vs = (VarSub (sv) (st)))) (PreH6 : ((termtypeID (t)) = 3)) (PreH7 : (thm_pre <> 0)) (PreH8 : (l = (cons (vs) (l0)))) (PreH9 : (lis_pre <> 0)) ,
  (sll_var_sub_list lis_next l0 )
  **  (store_sub_thm_res retval_2 retval (term_subst_t (st) (sv) (qterm)) l0 )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
) \/
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval_2: Z) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (t)) >= INT_MIN)) (PreH5 : (retval_2 = z)) (PreH6 : (thm_pre <> 0)) (PreH7 : (lis_cur <> 0)) (PreH8 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH9 : (vs = (VarSub (sv) (st)))) (PreH10 : ((termtypeID (t)) = 3)) (PreH11 : (thm_pre <> 0)) (PreH12 : (l = (cons (vs) (l0)))) (PreH13 : (lis_pre <> 0)) ,
  (sll_var_sub_list lis_next l0 )
  **  (store_sub_thm_res retval_2 retval (term_subst_t (st) (sv) (qterm)) l0 )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
).

Definition sub_thm_return_wit_2_split_goal_spatial := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval_2: Z) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (t)) >= INT_MIN)) (PreH5 : (retval_2 = z)) (PreH6 : (thm_pre <> 0)) (PreH7 : (lis_cur <> 0)) (PreH8 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH9 : (vs = (VarSub (sv) (st)))) (PreH10 : ((termtypeID (t)) = 3)) (PreH11 : (thm_pre <> 0)) (PreH12 : (l = (cons (vs) (l0)))) (PreH13 : (lis_pre <> 0)) ,
  (sll_var_sub_list lis_next l0 )
  **  (store_sub_thm_res retval_2 retval (term_subst_t (st) (sv) (qterm)) l0 )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
.

Definition sub_thm_return_wit_3 := 
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (PreH1 : (lis_pre = 0)) ,
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre thm_pre t l )
) \/
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (PreH1 : (lis_pre = 0)) ,
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre thm_pre t l )
).

Definition sub_thm_return_wit_3_split_goal_spatial := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (PreH1 : (lis_pre = 0)) ,
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre thm_pre t l )
.

Definition sub_thm_partial_solve_wit_1_pure := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (PreH1 : (lis_pre <> 0)) ,
  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  “ (lis_pre <> 0) ”
.

Definition sub_thm_partial_solve_wit_1_aux := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (PreH1 : (lis_pre <> 0)) ,
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  “ (lis_pre <> 0) ” 
  &&  “ (lis_pre <> 0) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
.

Definition sub_thm_partial_solve_wit_1 := sub_thm_partial_solve_wit_1_pure -> sub_thm_partial_solve_wit_1_aux.

Definition sub_thm_partial_solve_wit_2_pure := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (PreH1 : ((termtypeID (t)) = 3)) (PreH2 : (thm_pre <> 0)) (PreH3 : (l = (cons (vs) (l0)))) (PreH4 : (lis_pre <> 0)) ,
  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ ((termtypeID (t)) = 3) ” 
  &&  “ (thm_pre <> 0) ”
.

Definition sub_thm_partial_solve_wit_2_aux := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (PreH1 : ((termtypeID (t)) = 3)) (PreH2 : (thm_pre <> 0)) (PreH3 : (l = (cons (vs) (l0)))) (PreH4 : (lis_pre <> 0)) ,
  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ ((termtypeID (t)) = 3) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ ((termtypeID (t)) = 3) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (l = (cons (vs) (l0))) ” 
  &&  “ (lis_pre <> 0) ”
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_partial_solve_wit_2 := sub_thm_partial_solve_wit_2_pure -> sub_thm_partial_solve_wit_2_aux.

Definition sub_thm_partial_solve_wit_3_pure := 
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : (thm_pre <> 0)) (PreH2 : (lis_cur <> 0)) (PreH3 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (vs = (VarSub (sv) (st)))) (PreH5 : ((termtypeID (t)) = 3)) (PreH6 : (thm_pre <> 0)) (PreH7 : (l = (cons (vs) (l0)))) (PreH8 : (lis_pre <> 0)) ,
  ((( &( "den" ) )) # Ptr  |-> sz)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (z <> 0) ” 
  &&  “ (sy <> 0) ” 
  &&  “ (sz <> 0) ”
) \/
(
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (t)) >= INT_MIN)) (PreH5 : (thm_pre <> 0)) (PreH6 : (lis_cur <> 0)) (PreH7 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (vs = (VarSub (sv) (st)))) (PreH9 : ((termtypeID (t)) = 3)) (PreH10 : (thm_pre <> 0)) (PreH11 : (l = (cons (vs) (l0)))) (PreH12 : (lis_pre <> 0)) ,
  ((( &( "den" ) )) # Ptr  |-> sz)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (sz <> 0) ” 
  &&  “ (sy <> 0) ” 
  &&  “ (z <> 0) ”
).

Definition sub_thm_partial_solve_wit_3_pure_split_goal_1 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (t)) >= INT_MIN)) (PreH5 : (thm_pre <> 0)) (PreH6 : (lis_cur <> 0)) (PreH7 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (vs = (VarSub (sv) (st)))) (PreH9 : ((termtypeID (t)) = 3)) (PreH10 : (thm_pre <> 0)) (PreH11 : (l = (cons (vs) (l0)))) (PreH12 : (lis_pre <> 0)) ,
  ((( &( "den" ) )) # Ptr  |-> sz)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (sz <> 0) ”
.

Definition sub_thm_partial_solve_wit_3_pure_split_goal_2 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (t)) >= INT_MIN)) (PreH5 : (thm_pre <> 0)) (PreH6 : (lis_cur <> 0)) (PreH7 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (vs = (VarSub (sv) (st)))) (PreH9 : ((termtypeID (t)) = 3)) (PreH10 : (thm_pre <> 0)) (PreH11 : (l = (cons (vs) (l0)))) (PreH12 : (lis_pre <> 0)) ,
  ((( &( "den" ) )) # Ptr  |-> sz)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (sy <> 0) ”
.

Definition sub_thm_partial_solve_wit_3_pure_split_goal_3 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (t)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (t)) >= INT_MIN)) (PreH5 : (thm_pre <> 0)) (PreH6 : (lis_cur <> 0)) (PreH7 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (vs = (VarSub (sv) (st)))) (PreH9 : ((termtypeID (t)) = 3)) (PreH10 : (thm_pre <> 0)) (PreH11 : (l = (cons (vs) (l0)))) (PreH12 : (lis_pre <> 0)) ,
  ((( &( "den" ) )) # Ptr  |-> sz)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (z <> 0) ”
.

Definition sub_thm_partial_solve_wit_3_aux := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : (thm_pre <> 0)) (PreH2 : (lis_cur <> 0)) (PreH3 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (vs = (VarSub (sv) (st)))) (PreH5 : ((termtypeID (t)) = 3)) (PreH6 : (thm_pre <> 0)) (PreH7 : (l = (cons (vs) (l0)))) (PreH8 : (lis_pre <> 0)) ,
  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (z <> 0) ” 
  &&  “ (sy <> 0) ” 
  &&  “ (sz <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (lis_cur <> 0) ” 
  &&  “ (t = (TermQuant (qt) (qvar) (qterm))) ” 
  &&  “ (vs = (VarSub (sv) (st))) ” 
  &&  “ ((termtypeID (t)) = 3) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (l = (cons (vs) (l0))) ” 
  &&  “ (lis_pre <> 0) ”
  &&  (store_term z qterm )
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_partial_solve_wit_3 := sub_thm_partial_solve_wit_3_pure -> sub_thm_partial_solve_wit_3_aux.

Definition sub_thm_partial_solve_wit_4 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : (retval = z)) (PreH2 : (thm_pre <> 0)) (PreH3 : (lis_cur <> 0)) (PreH4 : (t = (TermQuant (qt) (qvar) (qterm)))) (PreH5 : (vs = (VarSub (sv) (st)))) (PreH6 : ((termtypeID (t)) = 3)) (PreH7 : (thm_pre <> 0)) (PreH8 : (l = (cons (vs) (l0)))) (PreH9 : (lis_pre <> 0)) ,
  (store_term retval (term_subst_t (st) (sv) (qterm)) )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  “ (retval = z) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (lis_cur <> 0) ” 
  &&  “ (t = (TermQuant (qt) (qvar) (qterm))) ” 
  &&  “ (vs = (VarSub (sv) (st))) ” 
  &&  “ ((termtypeID (t)) = 3) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (l = (cons (vs) (l0))) ” 
  &&  “ (lis_pre <> 0) ”
  &&  (store_term retval (term_subst_t (st) (sv) (qterm)) )
  **  (sll_var_sub_list lis_next l0 )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
.

Definition sub_thm_which_implies_wit_1 := 
(
forall (l: (@list var_sub)) (t: term) (lis: Z) (thm: Z) (PreH1 : (lis <> 0)) ,
  (store_term thm t )
  **  (sll_var_sub_list lis l )
|--
  EX (lis_next: Z)  (lis_cur: Z)  (vs: var_sub)  (l0: (@list var_sub)) ,
  “ (thm <> 0) ” 
  &&  “ (l = (cons (vs) (l0))) ”
  &&  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm t )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
) \/
(
forall (l: (@list var_sub)) (t: term) (lis: Z) (thm: Z) (PreH1 : (lis <> 0)) ,
  (store_term thm t )
  **  (sll_var_sub_list lis l )
|--
  EX (lis_next: Z)  (lis_cur: Z)  (vs: var_sub)  (l0: (@list var_sub)) ,
  “ (thm <> 0) ” 
  &&  “ (l = (cons (vs) (l0))) ”
  &&  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm t )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
).

Definition sub_thm_which_implies_wit_2 := 
(
forall (t: term) (vs: var_sub) (thm: Z) (lis: Z) (lis_cur: Z) (PreH1 : ((termtypeID (t)) = 3)) (PreH2 : (thm <> 0)) ,
  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm t )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
|--
  EX (sz: Z)  (sy: Z)  (z: Z)  (y: Z)  (sv: (@list Z))  (st: term)  (qt: quant_type)  (qvar: (@list Z))  (qterm: term) ,
  “ (thm <> 0) ” 
  &&  “ (lis_cur <> 0) ” 
  &&  “ (t = (TermQuant (qt) (qvar) (qterm))) ” 
  &&  “ (vs = (VarSub (sv) (st))) ”
  &&  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
) \/
(
forall (t: term) (vs: var_sub) (thm: Z) (lis_cur: Z) (PreH1 : ((termtypeID (t)) = 3)) (PreH2 : (thm <> 0)) ,
  (store_term' thm t )
  **  (store_var_sub lis_cur vs )
|--
  EX (sz: Z)  (sy: Z)  (z: Z)  (y: Z)  (sv: (@list Z))  (st: term)  (qt: quant_type)  (qvar: (@list Z))  (qterm: term) ,
  “ (thm <> 0) ” 
  &&  “ (lis_cur <> 0) ” 
  &&  “ (t = (TermQuant (qt) (qvar) (qterm))) ” 
  &&  “ (vs = (VarSub (sv) (st))) ”
  &&  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
).

(*----- Function separate_imply -----*)

Definition separate_imply_safety_wit_1 := 
forall (t_pre: Z) (trm: term) (PreH1 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition separate_imply_safety_wit_2 := 
forall (t_pre: Z) (trm: term) (PreH1 : ((termtypeID (trm)) <> 2)) (PreH2 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_imply_safety_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (PreH1 : (v_2 <> 0)) (PreH2 : (trm = (TermApply (lt) (rt)))) (PreH3 : ((termtypeID (trm)) = 2)) (PreH4 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition separate_imply_safety_wit_4 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (lt)) <> 2)) (PreH2 : (v_2 <> 0)) (PreH3 : (trm = (TermApply (lt) (rt)))) (PreH4 : ((termtypeID (trm)) = 2)) (PreH5 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_imply_safety_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (PreH1 : (v_4 <> 0)) (PreH2 : (lt = (TermApply (ll) (lr)))) (PreH3 : ((termtypeID (lt)) = 2)) (PreH4 : (v_2 <> 0)) (PreH5 : (trm = (TermApply (lt) (rt)))) (PreH6 : ((termtypeID (trm)) = 2)) (PreH7 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_imply_safety_wit_6 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (PreH1 : ((termtypeID (ll)) <> 1)) (PreH2 : (v_4 <> 0)) (PreH3 : (lt = (TermApply (ll) (lr)))) (PreH4 : ((termtypeID (lt)) = 2)) (PreH5 : (v_2 <> 0)) (PreH6 : (trm = (TermApply (lt) (rt)))) (PreH7 : ((termtypeID (trm)) = 2)) (PreH8 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_imply_safety_wit_7 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (PreH1 : (ll = (TermConst (llctype) (llcctnt)))) (PreH2 : ((termtypeID (ll)) = 1)) (PreH3 : (v_4 <> 0)) (PreH4 : (lt = (TermApply (ll) (lr)))) (PreH5 : ((termtypeID (lt)) = 2)) (PreH6 : (v_2 <> 0)) (PreH7 : (trm = (TermApply (lt) (rt)))) (PreH8 : ((termtypeID (trm)) = 2)) (PreH9 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition separate_imply_safety_wit_8 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (PreH1 : ((ctID (llctype)) <> 7)) (PreH2 : (ll = (TermConst (llctype) (llcctnt)))) (PreH3 : ((termtypeID (ll)) = 1)) (PreH4 : (v_4 <> 0)) (PreH5 : (lt = (TermApply (ll) (lr)))) (PreH6 : ((termtypeID (lt)) = 2)) (PreH7 : (v_2 <> 0)) (PreH8 : (trm = (TermApply (lt) (rt)))) (PreH9 : ((termtypeID (trm)) = 2)) (PreH10 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_imply_return_wit_1 := 
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (t1': Z) (t2': Z) (retval: Z) (PreH1 : ((ctID (llctype)) = 7)) (PreH2 : (ll = (TermConst (llctype) (llcctnt)))) (PreH3 : ((termtypeID (ll)) = 1)) (PreH4 : (v_4 <> 0)) (PreH5 : (lt = (TermApply (ll) (lr)))) (PreH6 : ((termtypeID (lt)) = 2)) (PreH7 : (v_2 <> 0)) (PreH8 : (trm = (TermApply (lt) (rt)))) (PreH9 : ((termtypeID (trm)) = 2)) (PreH10 : (t_pre <> 0)) ,
  (store_term v_3 lr )
  **  (store_term v rt )
  **  (store_ImplyProp retval t1' t2' lr rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res retval (sep_impl (trm)) )
  **  (store_term t_pre trm )
) \/
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (t1': Z) (t2': Z) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (ll)) <= INT_MAX)) (PreH4 : (llcctnt <= INT_MAX)) (PreH5 : ((ctID (llctype)) <= INT_MAX)) (PreH6 : ((termtypeID (trm)) >= INT_MIN)) (PreH7 : ((termtypeID (lt)) >= INT_MIN)) (PreH8 : ((termtypeID (ll)) >= INT_MIN)) (PreH9 : (llcctnt >= INT_MIN)) (PreH10 : ((ctID (llctype)) >= INT_MIN)) (PreH11 : ((ctID (llctype)) = 7)) (PreH12 : (ll = (TermConst (llctype) (llcctnt)))) (PreH13 : ((termtypeID (ll)) = 1)) (PreH14 : (v_4 <> 0)) (PreH15 : (lt = (TermApply (ll) (lr)))) (PreH16 : ((termtypeID (lt)) = 2)) (PreH17 : (v_2 <> 0)) (PreH18 : (trm = (TermApply (lt) (rt)))) (PreH19 : ((termtypeID (trm)) = 2)) (PreH20 : (t_pre <> 0)) ,
  (store_term v_3 lr )
  **  (store_term v rt )
  **  (store_ImplyProp retval t1' t2' lr rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res retval (sep_impl (trm)) )
  **  (store_term t_pre trm )
).

Definition separate_imply_return_wit_1_split_goal_spatial := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (t1': Z) (t2': Z) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (ll)) <= INT_MAX)) (PreH4 : (llcctnt <= INT_MAX)) (PreH5 : ((ctID (llctype)) <= INT_MAX)) (PreH6 : ((termtypeID (trm)) >= INT_MIN)) (PreH7 : ((termtypeID (lt)) >= INT_MIN)) (PreH8 : ((termtypeID (ll)) >= INT_MIN)) (PreH9 : (llcctnt >= INT_MIN)) (PreH10 : ((ctID (llctype)) >= INT_MIN)) (PreH11 : ((ctID (llctype)) = 7)) (PreH12 : (ll = (TermConst (llctype) (llcctnt)))) (PreH13 : ((termtypeID (ll)) = 1)) (PreH14 : (v_4 <> 0)) (PreH15 : (lt = (TermApply (ll) (lr)))) (PreH16 : ((termtypeID (lt)) = 2)) (PreH17 : (v_2 <> 0)) (PreH18 : (trm = (TermApply (lt) (rt)))) (PreH19 : ((termtypeID (trm)) = 2)) (PreH20 : (t_pre <> 0)) ,
  (store_term v_3 lr )
  **  (store_term v rt )
  **  (store_ImplyProp retval t1' t2' lr rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res retval (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_2 := 
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (PreH1 : ((ctID (llctype)) <> 7)) (PreH2 : (ll = (TermConst (llctype) (llcctnt)))) (PreH3 : ((termtypeID (ll)) = 1)) (PreH4 : (v_4 <> 0)) (PreH5 : (lt = (TermApply (ll) (lr)))) (PreH6 : ((termtypeID (lt)) = 2)) (PreH7 : (v_2 <> 0)) (PreH8 : (trm = (TermApply (lt) (rt)))) (PreH9 : ((termtypeID (trm)) = 2)) (PreH10 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
) \/
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (ll)) <= INT_MAX)) (PreH4 : (llcctnt <= INT_MAX)) (PreH5 : ((ctID (llctype)) <= INT_MAX)) (PreH6 : ((termtypeID (trm)) >= INT_MIN)) (PreH7 : ((termtypeID (lt)) >= INT_MIN)) (PreH8 : ((termtypeID (ll)) >= INT_MIN)) (PreH9 : (llcctnt >= INT_MIN)) (PreH10 : ((ctID (llctype)) >= INT_MIN)) (PreH11 : ((ctID (llctype)) <> 7)) (PreH12 : (ll = (TermConst (llctype) (llcctnt)))) (PreH13 : ((termtypeID (ll)) = 1)) (PreH14 : (v_4 <> 0)) (PreH15 : (lt = (TermApply (ll) (lr)))) (PreH16 : ((termtypeID (lt)) = 2)) (PreH17 : (v_2 <> 0)) (PreH18 : (trm = (TermApply (lt) (rt)))) (PreH19 : ((termtypeID (trm)) = 2)) (PreH20 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
).

Definition separate_imply_return_wit_2_split_goal_spatial := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (ll)) <= INT_MAX)) (PreH4 : (llcctnt <= INT_MAX)) (PreH5 : ((ctID (llctype)) <= INT_MAX)) (PreH6 : ((termtypeID (trm)) >= INT_MIN)) (PreH7 : ((termtypeID (lt)) >= INT_MIN)) (PreH8 : ((termtypeID (ll)) >= INT_MIN)) (PreH9 : (llcctnt >= INT_MIN)) (PreH10 : ((ctID (llctype)) >= INT_MIN)) (PreH11 : ((ctID (llctype)) <> 7)) (PreH12 : (ll = (TermConst (llctype) (llcctnt)))) (PreH13 : ((termtypeID (ll)) = 1)) (PreH14 : (v_4 <> 0)) (PreH15 : (lt = (TermApply (ll) (lr)))) (PreH16 : ((termtypeID (lt)) = 2)) (PreH17 : (v_2 <> 0)) (PreH18 : (trm = (TermApply (lt) (rt)))) (PreH19 : ((termtypeID (trm)) = 2)) (PreH20 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_3 := 
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (PreH1 : ((termtypeID (ll)) <> 1)) (PreH2 : (v_4 <> 0)) (PreH3 : (lt = (TermApply (ll) (lr)))) (PreH4 : ((termtypeID (lt)) = 2)) (PreH5 : (v_2 <> 0)) (PreH6 : (trm = (TermApply (lt) (rt)))) (PreH7 : ((termtypeID (trm)) = 2)) (PreH8 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
) \/
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (ll)) <= INT_MAX)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : ((termtypeID (lt)) >= INT_MIN)) (PreH6 : ((termtypeID (ll)) >= INT_MIN)) (PreH7 : ((termtypeID (ll)) <> 1)) (PreH8 : (v_4 <> 0)) (PreH9 : (lt = (TermApply (ll) (lr)))) (PreH10 : ((termtypeID (lt)) = 2)) (PreH11 : (v_2 <> 0)) (PreH12 : (trm = (TermApply (lt) (rt)))) (PreH13 : ((termtypeID (trm)) = 2)) (PreH14 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
).

Definition separate_imply_return_wit_3_split_goal_spatial := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (ll)) <= INT_MAX)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : ((termtypeID (lt)) >= INT_MIN)) (PreH6 : ((termtypeID (ll)) >= INT_MIN)) (PreH7 : ((termtypeID (ll)) <> 1)) (PreH8 : (v_4 <> 0)) (PreH9 : (lt = (TermApply (ll) (lr)))) (PreH10 : ((termtypeID (lt)) = 2)) (PreH11 : (v_2 <> 0)) (PreH12 : (trm = (TermApply (lt) (rt)))) (PreH13 : ((termtypeID (trm)) = 2)) (PreH14 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_4 := 
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (lt)) <> 2)) (PreH2 : (v_2 <> 0)) (PreH3 : (trm = (TermApply (lt) (rt)))) (PreH4 : ((termtypeID (trm)) = 2)) (PreH5 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
) \/
(
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (trm)) >= INT_MIN)) (PreH4 : ((termtypeID (lt)) >= INT_MIN)) (PreH5 : ((termtypeID (lt)) <> 2)) (PreH6 : (v_2 <> 0)) (PreH7 : (trm = (TermApply (lt) (rt)))) (PreH8 : ((termtypeID (trm)) = 2)) (PreH9 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
).

Definition separate_imply_return_wit_4_split_goal_spatial := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (lt)) <= INT_MAX)) (PreH3 : ((termtypeID (trm)) >= INT_MIN)) (PreH4 : ((termtypeID (lt)) >= INT_MIN)) (PreH5 : ((termtypeID (lt)) <> 2)) (PreH6 : (v_2 <> 0)) (PreH7 : (trm = (TermApply (lt) (rt)))) (PreH8 : ((termtypeID (trm)) = 2)) (PreH9 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_5 := 
(
forall (t_pre: Z) (trm: term) (PreH1 : ((termtypeID (trm)) <> 2)) (PreH2 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
) \/
(
forall (t_pre: Z) (trm: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : ((termtypeID (trm)) <> 2)) (PreH4 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
).

Definition separate_imply_return_wit_5_split_goal_spatial := 
forall (t_pre: Z) (trm: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : ((termtypeID (trm)) <> 2)) (PreH4 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_partial_solve_wit_1 := 
forall (t_pre: Z) (trm: term) ,
  (store_term t_pre trm )
|--
  (store_term t_pre trm )
.

Definition separate_imply_partial_solve_wit_2_pure := 
forall (t_pre: Z) (trm: term) (PreH1 : ((termtypeID (trm)) = 2)) (PreH2 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  “ (t_pre <> 0) ” 
  &&  “ ((termtypeID (trm)) = 2) ”
.

Definition separate_imply_partial_solve_wit_2_aux := 
forall (t_pre: Z) (trm: term) (PreH1 : ((termtypeID (trm)) = 2)) (PreH2 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  “ (t_pre <> 0) ” 
  &&  “ ((termtypeID (trm)) = 2) ” 
  &&  “ ((termtypeID (trm)) = 2) ” 
  &&  “ (t_pre <> 0) ”
  &&  (store_term' t_pre trm )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_2 := separate_imply_partial_solve_wit_2_pure -> separate_imply_partial_solve_wit_2_aux.

Definition separate_imply_partial_solve_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (PreH1 : (trm = (TermApply (lt) (rt)))) (PreH2 : ((termtypeID (trm)) = 2)) (PreH3 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (trm = (TermApply (lt) (rt))) ” 
  &&  “ ((termtypeID (trm)) = 2) ” 
  &&  “ (t_pre <> 0) ”
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_4_pure := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (lt)) = 2)) (PreH2 : (v <> 0)) (PreH3 : (trm = (TermApply (lt) (rt)))) (PreH4 : ((termtypeID (trm)) = 2)) (PreH5 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (v <> 0) ” 
  &&  “ ((termtypeID (lt)) = 2) ”
.

Definition separate_imply_partial_solve_wit_4_aux := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (lt)) = 2)) (PreH2 : (v <> 0)) (PreH3 : (trm = (TermApply (lt) (rt)))) (PreH4 : ((termtypeID (trm)) = 2)) (PreH5 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (v <> 0) ” 
  &&  “ ((termtypeID (lt)) = 2) ” 
  &&  “ ((termtypeID (lt)) = 2) ” 
  &&  “ (v <> 0) ” 
  &&  “ (trm = (TermApply (lt) (rt))) ” 
  &&  “ ((termtypeID (trm)) = 2) ” 
  &&  “ (t_pre <> 0) ”
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term' v lt )
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_4 := separate_imply_partial_solve_wit_4_pure -> separate_imply_partial_solve_wit_4_aux.

Definition separate_imply_partial_solve_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (PreH1 : (lt = (TermApply (ll) (lr)))) (PreH2 : ((termtypeID (lt)) = 2)) (PreH3 : (v_2 <> 0)) (PreH4 : (trm = (TermApply (lt) (rt)))) (PreH5 : ((termtypeID (trm)) = 2)) (PreH6 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (lt = (TermApply (ll) (lr))) ” 
  &&  “ ((termtypeID (lt)) = 2) ” 
  &&  “ (v_2 <> 0) ” 
  &&  “ (trm = (TermApply (lt) (rt))) ” 
  &&  “ ((termtypeID (trm)) = 2) ” 
  &&  “ (t_pre <> 0) ”
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_6_pure := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v_3: Z) (lt: term) (rt: term) (v_4: Z) (v: Z) (ll: term) (lr: term) (PreH1 : ((termtypeID (ll)) = 1)) (PreH2 : (v <> 0)) (PreH3 : (lt = (TermApply (ll) (lr)))) (PreH4 : ((termtypeID (lt)) = 2)) (PreH5 : (v_3 <> 0)) (PreH6 : (trm = (TermApply (lt) (rt)))) (PreH7 : ((termtypeID (trm)) = 2)) (PreH8 : (t_pre <> 0)) ,
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v ll )
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_4)
  **  (store_term v_4 lr )
  **  ((&((v_3)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (v <> 0) ” 
  &&  “ ((termtypeID (ll)) = 1) ”
.

Definition separate_imply_partial_solve_wit_6_aux := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v_3: Z) (lt: term) (rt: term) (v_4: Z) (v: Z) (ll: term) (lr: term) (PreH1 : ((termtypeID (ll)) = 1)) (PreH2 : (v <> 0)) (PreH3 : (lt = (TermApply (ll) (lr)))) (PreH4 : ((termtypeID (lt)) = 2)) (PreH5 : (v_3 <> 0)) (PreH6 : (trm = (TermApply (lt) (rt)))) (PreH7 : ((termtypeID (trm)) = 2)) (PreH8 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v ll )
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_4)
  **  (store_term v_4 lr )
  **  ((&((v_3)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ (v <> 0) ” 
  &&  “ ((termtypeID (ll)) = 1) ” 
  &&  “ ((termtypeID (ll)) = 1) ” 
  &&  “ (v <> 0) ” 
  &&  “ (lt = (TermApply (ll) (lr))) ” 
  &&  “ ((termtypeID (lt)) = 2) ” 
  &&  “ (v_3 <> 0) ” 
  &&  “ (trm = (TermApply (lt) (rt))) ” 
  &&  “ ((termtypeID (trm)) = 2) ” 
  &&  “ (t_pre <> 0) ”
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term' v ll )
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_4)
  **  (store_term v_4 lr )
  **  ((&((v_3)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_6 := separate_imply_partial_solve_wit_6_pure -> separate_imply_partial_solve_wit_6_aux.

Definition separate_imply_partial_solve_wit_7 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (PreH1 : ((ctID (llctype)) = 7)) (PreH2 : (ll = (TermConst (llctype) (llcctnt)))) (PreH3 : ((termtypeID (ll)) = 1)) (PreH4 : (v_4 <> 0)) (PreH5 : (lt = (TermApply (ll) (lr)))) (PreH6 : ((termtypeID (lt)) = 2)) (PreH7 : (v_2 <> 0)) (PreH8 : (trm = (TermApply (lt) (rt)))) (PreH9 : ((termtypeID (trm)) = 2)) (PreH10 : (t_pre <> 0)) ,
  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  “ ((ctID (llctype)) = 7) ” 
  &&  “ (ll = (TermConst (llctype) (llcctnt))) ” 
  &&  “ ((termtypeID (ll)) = 1) ” 
  &&  “ (v_4 <> 0) ” 
  &&  “ (lt = (TermApply (ll) (lr))) ” 
  &&  “ ((termtypeID (lt)) = 2) ” 
  &&  “ (v_2 <> 0) ” 
  &&  “ (trm = (TermApply (lt) (rt))) ” 
  &&  “ ((termtypeID (trm)) = 2) ” 
  &&  “ (t_pre <> 0) ”
  &&  (store_term v_3 lr )
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_which_implies_wit_1 := 
(
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  “ (t <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
) \/
(
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  “ (t <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
).

Definition separate_imply_which_implies_wit_1_split_goal_1 := 
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  “ (t <> 0) ”
.

Definition separate_imply_which_implies_wit_1_split_goal_spatial := 
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
.

Definition separate_imply_which_implies_wit_2 := 
(
forall (trm: term) (t: Z) (PreH1 : (t <> 0)) (PreH2 : ((termtypeID (trm)) = 2)) ,
  (store_term' t trm )
|--
  EX (v_2: Z)  (v: Z)  (lt: term)  (rt: term) ,
  “ (trm = (TermApply (lt) (rt))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term v lt )
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
) \/
(
forall (trm: term) (t: Z) (PreH1 : (t <> 0)) (PreH2 : ((termtypeID (trm)) = 2)) ,
  (store_term' t trm )
|--
  EX (v_2: Z)  (v: Z)  (lt: term)  (rt: term) ,
  “ (trm = (TermApply (lt) (rt))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term v lt )
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
).

Definition separate_imply_which_implies_wit_3 := 
(
forall (lt: term) (t: Z) (v: Z) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term v lt )
|--
  “ (v <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
) \/
(
forall (lt: term) (v: Z) ,
  (store_term v lt )
|--
  “ (v <> 0) ”
  &&  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
).

Definition separate_imply_which_implies_wit_3_split_goal_1 := 
forall (lt: term) (v: Z) ,
  (store_term v lt )
|--
  “ (v <> 0) ”
.

Definition separate_imply_which_implies_wit_3_split_goal_spatial := 
forall (lt: term) (v: Z) ,
  (store_term v lt )
|--
  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
.

Definition separate_imply_which_implies_wit_4 := 
(
forall (lt: term) (t: Z) (v: Z) (PreH1 : (v <> 0)) (PreH2 : ((termtypeID (lt)) = 2)) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term' v lt )
|--
  EX (v_3: Z)  (v_2: Z)  (ll: term)  (lr: term) ,
  “ (lt = (TermApply (ll) (lr))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 ll )
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
) \/
(
forall (lt: term) (v: Z) (PreH1 : (v <> 0)) (PreH2 : ((termtypeID (lt)) = 2)) ,
  (store_term' v lt )
|--
  EX (v_3: Z)  (v_2: Z)  (ll: term)  (lr: term) ,
  “ (lt = (TermApply (ll) (lr))) ”
  &&  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 ll )
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
).

Definition separate_imply_which_implies_wit_5 := 
(
forall (ll: term) (t: Z) (v: Z) (v_2: Z) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 ll )
|--
  “ (v_2 <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_2 ll )
) \/
(
forall (ll: term) (v_2: Z) ,
  (store_term v_2 ll )
|--
  “ (v_2 <> 0) ”
  &&  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_2 ll )
).

Definition separate_imply_which_implies_wit_5_split_goal_1 := 
forall (ll: term) (v_2: Z) ,
  (store_term v_2 ll )
|--
  “ (v_2 <> 0) ”
.

Definition separate_imply_which_implies_wit_5_split_goal_spatial := 
forall (ll: term) (v_2: Z) ,
  (store_term v_2 ll )
|--
  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_2 ll )
.

Definition separate_imply_which_implies_wit_6 := 
(
forall (ll: term) (t: Z) (v: Z) (v_2: Z) (PreH1 : (v_2 <> 0)) (PreH2 : ((termtypeID (ll)) = 1)) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term' v_2 ll )
|--
  EX (llctype: const_type)  (llcctnt: Z) ,
  “ (ll = (TermConst (llctype) (llcctnt))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
) \/
(
forall (ll: term) (v_2: Z) (PreH1 : (v_2 <> 0)) (PreH2 : ((termtypeID (ll)) = 1)) ,
  (store_term' v_2 ll )
|--
  EX (llctype: const_type)  (llcctnt: Z) ,
  “ (ll = (TermConst (llctype) (llcctnt))) ”
  &&  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
).

(*----- Function check_list_gen -----*)

Definition check_list_gen_safety_wit_1 := 
forall (target_pre: Z) (thm_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (theo_low_level_spec: term) (PreH1 : (safeExec ATrue (check_rel (theo_low_level_spec) (targ_low_level_spec)) X_low_level_spec )) ,
  ((( &( "check_list" ) )) # Ptr  |->_)
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre theo_low_level_spec )
  **  (store_term target_pre targ_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_list_gen_safety_wit_2 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (thm: Z) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH3 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_imply_res retval_2 (sep_impl (t)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  (store_term target_pre targ_low_level_spec )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm)
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> tail_ptr)
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_list_gen_safety_wit_3 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (thm: Z) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (check_list: Z) (tail_ptr_addr_v: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval = 0)) (PreH3 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH4 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  ((( &( "tail_ptr" ) )) # Ptr  |-> tail_ptr_addr_v)
  **  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (store_imply_res retval_2 (sep_impl (t)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  (store_term target_pre targ_low_level_spec )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_list_gen_safety_wit_4 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (thm: Z) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (retval_3: Z) (pc: Z) (pa: Z) (c: Z) (r: term) (tr: term) (PreH1 : (t = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr)))) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = 0)) (PreH5 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH6 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((retval_2)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "new_node" ) )) # Ptr  |-> retval_3)
  **  (store_term target_pre targ_low_level_spec )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm)
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> tail_ptr)
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_list_gen_entail_wit_1 := 
(
forall (target_pre: Z) (thm_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (theo_low_level_spec: term) (PreH1 : (safeExec ATrue (check_rel (theo_low_level_spec) (targ_low_level_spec)) X_low_level_spec )) ,
  (store_term thm_pre theo_low_level_spec )
  **  (store_term target_pre targ_low_level_spec )
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term thm_pre t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) ( &( "check_list" ) ) l )
) \/
(
forall (target_pre: Z) (thm_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (theo_low_level_spec: term) (PreH1 : (safeExec ATrue (check_rel (theo_low_level_spec) (targ_low_level_spec)) X_low_level_spec )) ,
  (store_term thm_pre theo_low_level_spec )
  **  (store_term target_pre targ_low_level_spec )
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term thm_pre t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) ( &( "check_list" ) ) l )
).

Definition check_list_gen_entail_wit_2 := 
(
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t_2: term) (l_2: (@list term)) (retval_2: Z) (retval_3: Z) (retval: Z) (pc: Z) (pa: Z) (c: Z) (r: term) (tr: term) (PreH1 : (t_2 = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr)))) (PreH2 : (retval <> 0)) (PreH3 : (retval_3 <> 0)) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = (term_alpha_eqn (t_2) (targ_low_level_spec)))) (PreH6 : (safeExec ATrue (check_from_mid_rel (t_2) (targ_low_level_spec) (l_2)) X_low_level_spec )) ,
  (store_term pa r )
  **  (store_term pc tr )
  **  ((&((retval)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  ((&((retval)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l_2 )
  **  ((tail_ptr) # Ptr  |-> retval)
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term pc t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) &((retval)  # "term_list" ->ₛ "next") l )
  **  ((&((retval)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
) \/
(
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t_2: term) (l_2: (@list term)) (retval_2: Z) (retval_3: Z) (retval: Z) (pc: Z) (pa: Z) (c: Z) (r: term) (tr: term) (PreH1 : (t_2 = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr)))) (PreH2 : (retval <> 0)) (PreH3 : (retval_3 <> 0)) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = (term_alpha_eqn (t_2) (targ_low_level_spec)))) (PreH6 : (safeExec ATrue (check_from_mid_rel (t_2) (targ_low_level_spec) (l_2)) X_low_level_spec )) ,
  (store_term pa r )
  **  (store_term pc tr )
  **  ((&((retval)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l_2 )
  **  ((tail_ptr) # Ptr  |-> retval)
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term pc t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) &((retval)  # "term_list" ->ₛ "next") l )
).

Definition check_list_gen_return_wit_1 := 
(
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (t_2: term) (l_2: (@list term)) (retval: Z) (check_list: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (term_alpha_eqn (t_2) (targ_low_level_spec)))) (PreH3 : (safeExec ATrue (check_from_mid_rel (t_2) (targ_low_level_spec) (l_2)) X_low_level_spec )) ,
  (sll_term_list check_list l_2 )
  **  (store_term target_pre targ_low_level_spec )
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (return ((makepair (t) (l)))) X_low_level_spec ) ”
  &&  (store_term target_pre targ_low_level_spec )
  **  (sll_term_list check_list l )
) \/
(
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (t_2: term) (l_2: (@list term)) (retval: Z) (check_list: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (term_alpha_eqn (t_2) (targ_low_level_spec)))) (PreH3 : (safeExec ATrue (check_from_mid_rel (t_2) (targ_low_level_spec) (l_2)) X_low_level_spec )) ,
  (sll_term_list check_list l_2 )
  **  (store_term target_pre targ_low_level_spec )
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (return ((makepair (t) (l)))) X_low_level_spec ) ”
  &&  (store_term target_pre targ_low_level_spec )
  **  (sll_term_list check_list l )
).

Definition check_list_gen_return_wit_2 := 
(
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (t_2: term) (l_2: (@list term)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval = 0)) (PreH3 : (retval = (term_alpha_eqn (t_2) (targ_low_level_spec)))) (PreH4 : (safeExec ATrue (check_from_mid_rel (t_2) (targ_low_level_spec) (l_2)) X_low_level_spec )) ,
  (store_imply_res retval_2 (sep_impl (t_2)) )
  **  (store_term target_pre targ_low_level_spec )
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (return ((makepair (t) (l)))) X_low_level_spec ) ”
  &&  (store_term target_pre targ_low_level_spec )
  **  (sll_term_list 0 l )
) \/
(
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (t_2: term) (l_2: (@list term)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval = 0)) (PreH3 : (retval = (term_alpha_eqn (t_2) (targ_low_level_spec)))) (PreH4 : (safeExec ATrue (check_from_mid_rel (t_2) (targ_low_level_spec) (l_2)) X_low_level_spec )) ,
  (store_imply_res retval_2 (sep_impl (t_2)) )
  **  (store_term target_pre targ_low_level_spec )
|--
  EX (t: term)  (l: (@list term)) ,
  “ (safeExec ATrue (return ((makepair (t) (l)))) X_low_level_spec ) ”
  &&  (store_term target_pre targ_low_level_spec )
  **  (sll_term_list 0 l )
).

Definition check_list_gen_partial_solve_wit_1 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (thm: Z) (t: term) (l: (@list term)) (PreH1 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_term thm t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term thm t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
.

Definition check_list_gen_partial_solve_wit_2 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (thm: Z) (t: term) (l: (@list term)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH3 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_term thm t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval = 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term thm t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
.

Definition check_list_gen_partial_solve_wit_3 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (thm: Z) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH3 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term thm t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval = 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term thm t )
  **  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
.

Definition check_list_gen_partial_solve_wit_4 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval = 0)) (PreH3 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH4 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
  **  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
.

Definition check_list_gen_partial_solve_wit_5 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (check_list: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval = 0)) (PreH3 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH4 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (sll_term_list check_list l )
  **  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
|--
  “ (retval_2 = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (sll_term_list check_list l )
  **  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
.

Definition check_list_gen_partial_solve_wit_6 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = 0)) (PreH3 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH4 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_imply_res retval_2 (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
.

Definition check_list_gen_partial_solve_wit_7_pure := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (thm: Z) (t: term) (l: (@list term)) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_2 = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH5 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "new_node" ) )) # Ptr  |-> retval_3)
  **  (store_imply_res retval (sep_impl (t)) )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (store_term target_pre targ_low_level_spec )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm)
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> tail_ptr)
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval <> 0) ”
.

Definition check_list_gen_partial_solve_wit_7_aux := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t: term) (l: (@list term)) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_2 = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH5 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_imply_res retval (sep_impl (t)) )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_imply_res retval (sep_impl (t)) )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> 0)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
.

Definition check_list_gen_partial_solve_wit_7 := check_list_gen_partial_solve_wit_7_pure -> check_list_gen_partial_solve_wit_7_aux.

Definition check_list_gen_partial_solve_wit_8_pure := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t: term) (l: (@list term)) (retval_2: Z) (retval: Z) (retval_3: Z) (pc: Z) (pa: Z) (c: Z) (r: term) (tr: term) (PreH1 : (t = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr)))) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH6 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((retval)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((( &( "new_node" ) )) # Ptr  |-> retval_3)
  **  (store_term target_pre targ_low_level_spec )
  **  ((( &( "target" ) )) # Ptr  |-> target_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> pc)
  **  ((( &( "tail_ptr" ) )) # Ptr  |-> &((retval_3)  # "term_list" ->ₛ "next"))
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> retval_3)
|--
  “ (retval <> 0) ”
.

Definition check_list_gen_partial_solve_wit_8_aux := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t: term) (l: (@list term)) (retval_2: Z) (retval: Z) (retval_3: Z) (pc: Z) (pa: Z) (c: Z) (r: term) (tr: term) (PreH1 : (t = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr)))) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_2 = 0)) (PreH5 : (retval_2 = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH6 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  ((&((retval)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((retval)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> retval_3)
|--
  “ (retval <> 0) ” 
  &&  “ (t = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr))) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  ((&((retval)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((retval)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> retval_3)
.

Definition check_list_gen_partial_solve_wit_8 := check_list_gen_partial_solve_wit_8_pure -> check_list_gen_partial_solve_wit_8_aux.

Definition check_list_gen_partial_solve_wit_9 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t: term) (l: (@list term)) (retval: Z) (retval_2: Z) (retval_3: Z) (pc: Z) (pa: Z) (c: Z) (r: term) (tr: term) (PreH1 : (t = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr)))) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = 0)) (PreH5 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH6 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_ImplyProp retval_2 pa pc r tr )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> retval_3)
|--
  “ (t = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr))) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_ImplyProp retval_2 pa pc r tr )
  **  ((&((retval_3)  # "term_list" ->ₛ "element")) # Ptr  |-> pa)
  **  ((&((retval_3)  # "term_list" ->ₛ "next")) # Ptr  |-> 0)
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> retval_3)
.

Definition check_list_gen_partial_solve_wit_10 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (thm: Z) (t: term) (l: (@list term)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH3 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_term thm t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval <> 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (store_term thm t )
  **  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
.

Definition check_list_gen_partial_solve_wit_11 := 
forall (target_pre: Z) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) (targ_low_level_spec: term) (tail_ptr: Z) (t: term) (l: (@list term)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (term_alpha_eqn (t) (targ_low_level_spec)))) (PreH3 : (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec )) ,
  (store_term target_pre targ_low_level_spec )
  **  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  “ (retval <> 0) ” 
  &&  “ (retval = (term_alpha_eqn (t) (targ_low_level_spec))) ” 
  &&  “ (safeExec ATrue (check_from_mid_rel (t) (targ_low_level_spec) (l)) X_low_level_spec ) ”
  &&  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
  **  (store_term target_pre targ_low_level_spec )
.

Definition check_list_gen_which_implies_wit_1 := 
(
forall (l: (@list term)) (tail_ptr: Z) ,
  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  EX (check_list: Z) ,
  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
) \/
(
forall (l: (@list term)) (tail_ptr: Z) ,
  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  EX (check_list: Z) ,
  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
).

Definition check_list_gen_which_implies_wit_2 := 
(
forall (ttm: term) (p: Z) (PreH1 : (p <> 0)) ,
  (store_imply_res p (sep_impl (ttm)) )
|--
  EX (pc: Z)  (pa: Z)  (c: Z)  (r: term)  (tr: term) ,
  “ (ttm = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr))) ”
  &&  ((&((p)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((p)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
) \/
(
forall (ttm: term) (p: Z) (PreH1 : (p <> 0)) ,
  (store_imply_res p (sep_impl (ttm)) )
|--
  EX (pc: Z)  (pa: Z)  (c: Z)  (r: term)  (tr: term) ,
  “ (ttm = (TermApply ((TermApply ((TermConst (CImpl) (c))) (r))) (tr))) ”
  &&  ((&((p)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((p)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
).

Definition check_list_gen_which_implies_wit_3 := 
(
forall (pc: Z) (pa: Z) (tr: term) (r: term) (p: Z) (PreH1 : (p <> 0)) ,
  ((&((p)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((p)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
|--
  (store_ImplyProp p pa pc r tr )
) \/
(
forall (pc: Z) (pa: Z) (tr: term) (r: term) (p: Z) (PreH1 : (p <> 0)) ,
  ((&((p)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((p)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
|--
  (store_ImplyProp p pa pc r tr )
).

Definition check_list_gen_which_implies_wit_3_split_goal_spatial := 
forall (pc: Z) (pa: Z) (tr: term) (r: term) (p: Z) (PreH1 : (p <> 0)) ,
  ((&((p)  # "imply_prop" ->ₛ "assum")) # Ptr  |-> pa)
  **  ((&((p)  # "imply_prop" ->ₛ "concl")) # Ptr  |-> pc)
  **  (store_term pa r )
  **  (store_term pc tr )
|--
  (store_ImplyProp p pa pc r tr )
.

Definition check_list_gen_which_implies_wit_4 := 
(
forall (l: (@list term)) (tail_ptr: Z) ,
  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  EX (check_list: Z) ,
  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
) \/
(
forall (l: (@list term)) (tail_ptr: Z) ,
  (sllbseg_term_list ( &( "check_list" ) ) tail_ptr l )
  **  ((tail_ptr) # Ptr  |-> 0)
|--
  EX (check_list: Z) ,
  ((( &( "check_list" ) )) # Ptr  |-> check_list)
  **  (sll_term_list check_list l )
).

(*----- Function thm_apply -----*)

Definition thm_apply_safety_wit_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (PreH1 : (res_type = 0)) (PreH2 : (v = 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (thm_pre <> 0)) (PreH5 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition thm_apply_safety_wit_2 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (PreH1 : (retval = 0)) (PreH2 : (res_type = 0)) (PreH3 : (v = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (thm_pre <> 0)) (PreH6 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition thm_apply_safety_wit_3 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (PreH1 : (retval = 0)) (PreH2 : (res_type = 0)) (PreH3 : (v = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (thm_pre <> 0)) (PreH6 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition thm_apply_safety_wit_4 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (PreH1 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (retval <> 0)) (PreH4 : (res_type = 0)) (PreH5 : (v = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (thm_pre <> 0)) (PreH8 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH9 : (retval_3 <> 0)) ,
  (store_term retval st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition thm_apply_safety_wit_5 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (PreH1 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (retval <> 0)) (PreH4 : (res_type = 0)) (PreH5 : (v = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (thm_pre <> 0)) (PreH8 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH9 : (retval_3 <> 0)) ,
  (store_term retval st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition thm_apply_safety_wit_6 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (PreH1 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (retval <> 0)) (PreH4 : (res_type = 0)) (PreH5 : (v = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (thm_pre <> 0)) (PreH8 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH9 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition thm_apply_return_wit_1 := 
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t_2: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (res_type = 0)) (PreH3 : (v = 0)) (PreH4 : (retval <> 0)) (PreH5 : (thm_pre <> 0)) (PreH6 : (safeExec ATrue (thm_app_rel (t_2) (l) (g)) X )) ,
  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 0)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval_2 t_2 l )
  **  (store_term goal_pre g )
|--
  EX (t: term)  (sr: solve_res) ,
  “ (safeExec ATrue (return (sr)) X ) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval sr )
) \/
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t_2: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (retval_2 = 0)) (PreH4 : (res_type = 0)) (PreH5 : (v = 0)) (PreH6 : (retval <> 0)) (PreH7 : (thm_pre <> 0)) (PreH8 : (safeExec ATrue (thm_app_rel (t_2) (l) (g)) X )) ,
  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 0)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval_2 t_2 l )
  **  (store_term goal_pre g )
|--
  EX (t: term)  (sr: solve_res) ,
  “ (safeExec ATrue (return (sr)) X ) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval sr )
).

Definition thm_apply_return_wit_2 := 
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t_2: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (PreH1 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH2 : (thm_subst_allres_rel t_2 l pq st )) (PreH3 : (retval_2 <> 0)) (PreH4 : (res_type = 0)) (PreH5 : (v = 0)) (PreH6 : (retval <> 0)) (PreH7 : (thm_pre <> 0)) (PreH8 : (safeExec ATrue (thm_app_rel (t_2) (l) (g)) X )) (PreH9 : (retval_3 <> 0)) ,
  (store_term retval_2 st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  EX (t: term)  (sr: solve_res) ,
  “ (safeExec ATrue (return (sr)) X ) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval sr )
) \/
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t_2: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH6 : (thm_subst_allres_rel t_2 l pq st )) (PreH7 : (retval_2 <> 0)) (PreH8 : (res_type = 0)) (PreH9 : (v = 0)) (PreH10 : (retval <> 0)) (PreH11 : (thm_pre <> 0)) (PreH12 : (safeExec ATrue (thm_app_rel (t_2) (l) (g)) X )) (PreH13 : (retval_3 <> 0)) ,
  (store_term retval_2 st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  EX (t: term)  (sr: solve_res) ,
  “ (safeExec ATrue (return (sr)) X ) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval sr )
).

Definition thm_apply_return_wit_3 := 
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t_2: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (t_3: term) (l_2: (@list term)) (retval_5: Z) (PreH1 : (safeExec ATrue (applyf (get_list) ((makepair (t_3) (l_2)))) X )) (PreH2 : (retval_4 <> 0)) (PreH3 : (v_2 = 0)) (PreH4 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH5 : (thm_subst_allres_rel t_2 l pq st )) (PreH6 : (retval_2 <> 0)) (PreH7 : (res_type = 0)) (PreH8 : (v = 0)) (PreH9 : (retval <> 0)) (PreH10 : (thm_pre <> 0)) (PreH11 : (retval_3 = 0)) ,
  (store_term goal_pre g )
  **  (sll_term_list retval_5 l_2 )
  **  (store_term retval_2 st )
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> retval_5)
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  EX (t: term)  (sr: solve_res) ,
  “ (safeExec ATrue (return (sr)) X ) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval sr )
) \/
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t_2: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (t_3: term) (l_2: (@list term)) (retval_5: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (safeExec ATrue (applyf (get_list) ((makepair (t_3) (l_2)))) X )) (PreH4 : (retval_4 <> 0)) (PreH5 : (v_2 = 0)) (PreH6 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH7 : (thm_subst_allres_rel t_2 l pq st )) (PreH8 : (retval_2 <> 0)) (PreH9 : (res_type = 0)) (PreH10 : (v = 0)) (PreH11 : (retval <> 0)) (PreH12 : (thm_pre <> 0)) (PreH13 : (retval_3 = 0)) ,
  (store_term goal_pre g )
  **  (sll_term_list retval_5 l_2 )
  **  (store_term retval_2 st )
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> retval_5)
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  EX (t: term)  (sr: solve_res) ,
  “ (safeExec ATrue (return (sr)) X ) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval sr )
).

Definition thm_apply_partial_solve_wit_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (PreH1 : (thm_pre <> 0)) (PreH2 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
|--
  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ”
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_2 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (PreH1 : (thm_pre <> 0)) (PreH2 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
|--
  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ”
  &&  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_3 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (thm_pre <> 0)) (PreH3 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  (store_solve_res retval_2 (SRBool (0)) )
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ”
  &&  (store_solve_res retval_2 (SRBool (0)) )
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_4_pure := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (PreH1 : (retval <> 0)) (PreH2 : (res_type = 0)) (PreH3 : (v = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (thm_pre <> 0)) (PreH6 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  “ (retval <> 0) ”
.

Definition thm_apply_partial_solve_wit_4_aux := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (PreH1 : (retval <> 0)) (PreH2 : (res_type = 0)) (PreH3 : (v = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (thm_pre <> 0)) (PreH6 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (res_type = 0) ” 
  &&  “ (v = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ”
  &&  (store_sub_thm_res thm_pre retval t l )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_4 := thm_apply_partial_solve_wit_4_pure -> thm_apply_partial_solve_wit_4_aux.

Definition thm_apply_partial_solve_wit_5 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (PreH1 : (thm_subst_allres_rel t l pq st )) (PreH2 : (retval <> 0)) (PreH3 : (res_type = 0)) (PreH4 : (v = 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (thm_pre <> 0)) (PreH7 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  (store_partial_quant thm_pre retval pq )
  **  (store_term retval st )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
|--
  “ (thm_subst_allres_rel t l pq st ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (res_type = 0) ” 
  &&  “ (v = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ”
  &&  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_6_pure := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (PreH1 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (retval <> 0)) (PreH4 : (res_type = 0)) (PreH5 : (v = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (thm_pre <> 0)) (PreH8 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH9 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ (0 = 0) ”
.

Definition thm_apply_partial_solve_wit_6_aux := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (PreH1 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (retval <> 0)) (PreH4 : (res_type = 0)) (PreH5 : (v = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (thm_pre <> 0)) (PreH8 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH9 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
|--
  “ (0 = 0) ” 
  &&  “ (retval_3 = (term_alpha_eqn (st) (g))) ” 
  &&  “ (thm_subst_allres_rel t l pq st ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (res_type = 0) ” 
  &&  “ (v = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ” 
  &&  “ (retval_3 = 0) ”
  &&  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 0)
  **  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_6 := thm_apply_partial_solve_wit_6_pure -> thm_apply_partial_solve_wit_6_aux.

Definition thm_apply_partial_solve_wit_7 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (PreH1 : (v_2 = 0)) (PreH2 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH3 : (thm_subst_allres_rel t l pq st )) (PreH4 : (retval <> 0)) (PreH5 : (res_type = 0)) (PreH6 : (v = 0)) (PreH7 : (retval_2 <> 0)) (PreH8 : (thm_pre <> 0)) (PreH9 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH10 : (retval_3 = 0)) ,
  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  “ (v_2 = 0) ” 
  &&  “ (retval_3 = (term_alpha_eqn (st) (g))) ” 
  &&  “ (thm_subst_allres_rel t l pq st ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (res_type = 0) ” 
  &&  “ (v = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_term retval st )
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_8_pure := 
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (v_2 = 0)) (PreH3 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH4 : (thm_subst_allres_rel t l pq st )) (PreH5 : (retval <> 0)) (PreH6 : (res_type = 0)) (PreH7 : (v = 0)) (PreH8 : (retval_2 <> 0)) (PreH9 : (thm_pre <> 0)) (PreH10 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH11 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term retval_4 st )
  **  ((( &( "thm_ins_c" ) )) # Ptr  |-> retval_4)
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ (thm_subst_allres_rel t l pq st ) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ” 
  &&  “ ((term_alpha_eqn (st) (g)) = 0) ”
) \/
(
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (retval_4 <> 0)) (PreH4 : (v_2 = 0)) (PreH5 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH6 : (thm_subst_allres_rel t l pq st )) (PreH7 : (retval <> 0)) (PreH8 : (res_type = 0)) (PreH9 : (v = 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (thm_pre <> 0)) (PreH12 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH13 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term retval_4 st )
  **  ((( &( "thm_ins_c" ) )) # Ptr  |-> retval_4)
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ ((term_alpha_eqn (st) (g)) = 0) ”
).

Definition thm_apply_partial_solve_wit_8_pure_split_goal_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (retval_4 <> 0)) (PreH4 : (v_2 = 0)) (PreH5 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH6 : (thm_subst_allres_rel t l pq st )) (PreH7 : (retval <> 0)) (PreH8 : (res_type = 0)) (PreH9 : (v = 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (thm_pre <> 0)) (PreH12 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH13 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term retval_4 st )
  **  ((( &( "thm_ins_c" ) )) # Ptr  |-> retval_4)
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ ((term_alpha_eqn (st) (g)) = 0) ”
.

Definition thm_apply_partial_solve_wit_8_aux := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (v_2 = 0)) (PreH3 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH4 : (thm_subst_allres_rel t l pq st )) (PreH5 : (retval <> 0)) (PreH6 : (res_type = 0)) (PreH7 : (v = 0)) (PreH8 : (retval_2 <> 0)) (PreH9 : (thm_pre <> 0)) (PreH10 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) (PreH11 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term retval_4 st )
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  “ (thm_subst_allres_rel t l pq st ) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ” 
  &&  “ ((term_alpha_eqn (st) (g)) = 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (v_2 = 0) ” 
  &&  “ (retval_3 = (term_alpha_eqn (st) (g))) ” 
  &&  “ (thm_subst_allres_rel t l pq st ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (res_type = 0) ” 
  &&  “ (v = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (safeExec ATrue (thm_app_rel (t) (l) (g)) X ) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_term retval st )
  **  (store_term retval_4 st )
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_8 := thm_apply_partial_solve_wit_8_pure -> thm_apply_partial_solve_wit_8_aux.

Definition thm_apply_partial_solve_wit_9_pure := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (PreH1 : (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X )) (PreH2 : (retval_4 <> 0)) (PreH3 : (v_2 = 0)) (PreH4 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH5 : (thm_subst_allres_rel t l pq st )) (PreH6 : (retval <> 0)) (PreH7 : (res_type = 0)) (PreH8 : (v = 0)) (PreH9 : (retval_2 <> 0)) (PreH10 : (thm_pre <> 0)) (PreH11 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term retval_4 st )
  **  ((( &( "thm_ins_c" ) )) # Ptr  |-> retval_4)
  **  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  “ (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X ) ”
.

Definition thm_apply_partial_solve_wit_9_aux := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) (retval_4: Z) (PreH1 : (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X )) (PreH2 : (retval_4 <> 0)) (PreH3 : (v_2 = 0)) (PreH4 : (retval_3 = (term_alpha_eqn (st) (g)))) (PreH5 : (thm_subst_allres_rel t l pq st )) (PreH6 : (retval <> 0)) (PreH7 : (res_type = 0)) (PreH8 : (v = 0)) (PreH9 : (retval_2 <> 0)) (PreH10 : (thm_pre <> 0)) (PreH11 : (retval_3 = 0)) ,
  (store_term retval st )
  **  (store_term retval_4 st )
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  “ (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X ) ” 
  &&  “ (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X ) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (v_2 = 0) ” 
  &&  “ (retval_3 = (term_alpha_eqn (st) (g))) ” 
  &&  “ (thm_subst_allres_rel t l pq st ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (res_type = 0) ” 
  &&  “ (v = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (thm_pre <> 0) ” 
  &&  “ (retval_3 = 0) ”
  &&  (store_term retval_4 st )
  **  (store_term goal_pre g )
  **  (store_term retval st )
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_9 := thm_apply_partial_solve_wit_9_pure -> thm_apply_partial_solve_wit_9_aux.

Definition thm_apply_which_implies_wit_1 := 
(
forall (res: Z) ,
  (store_solve_res res (SRBool (0)) )
|--
  EX (v: Z)  (res_type: Z) ,
  “ (res_type = 0) ” 
  &&  “ (v = 0) ”
  &&  ((&((res)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
) \/
(
forall (res: Z) ,
  (store_solve_res res (SRBool (0)) )
|--
  ((&((res)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 0)
).

Definition thm_apply_which_implies_wit_1_split_goal_spatial := 
forall (res: Z) ,
  (store_solve_res res (SRBool (0)) )
|--
  ((&((res)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 0)
.

Definition thm_apply_which_implies_wit_2 := 
(
forall (l: (@list var_sub)) (t: term) (thm_ins: Z) (thm: Z) (PreH1 : (thm_ins <> 0)) ,
  (store_sub_thm_res thm thm_ins t l )
|--
  EX (pq: partial_quant)  (st: term) ,
  “ (thm_subst_allres_rel t l pq st ) ”
  &&  (store_partial_quant thm thm_ins pq )
  **  (store_term thm_ins st )
) \/
(
forall (l: (@list var_sub)) (t: term) (thm_ins: Z) (thm: Z) (PreH1 : (thm_ins <> 0)) ,
  (store_sub_thm_res thm thm_ins t l )
|--
  EX (pq: partial_quant)  (st: term) ,
  “ (thm_subst_allres_rel t l pq st ) ”
  &&  (store_partial_quant thm thm_ins pq )
  **  (store_term thm_ins st )
).

Definition thm_apply_which_implies_wit_3 := 
(
forall (res: Z) (v_2: Z) (PreH1 : (v_2 = 0)) ,
  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v_2)
|--
  EX (v: Z) ,
  “ (v = 0) ”
  &&  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v)
) \/
(
forall (res: Z) (v_2: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (v_2 = 0)) ,
  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v_2)
|--
  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> 0)
).

Definition thm_apply_which_implies_wit_3_split_goal_spatial := 
forall (res: Z) (v_2: Z) (PreH1 : (v_2 <= INT_MAX)) (PreH2 : (v_2 >= INT_MIN)) (PreH3 : (v_2 = 0)) ,
  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v_2)
|--
  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> 0)
.

Definition thm_apply_which_implies_wit_4 := 
(
forall (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (st: term) (pq: partial_quant) (PreH1 : ((term_alpha_eqn (st) (g)) = 0)) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X ) ”
  &&  emp
) \/
(
forall (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (st: term) (pq: partial_quant) (PreH1 : ((term_alpha_eqn (st) (g)) = 0)) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X ) ”
  &&  emp
).

Definition thm_apply_which_implies_wit_4_split_goal_1 := 
forall (X: (solve_res -> (unit -> Prop))) (g: term) (l: (@list var_sub)) (t: term) (st: term) (pq: partial_quant) (PreH1 : ((term_alpha_eqn (st) (g)) = 0)) (PreH2 : (thm_subst_allres_rel t l pq st )) (PreH3 : (safeExec ATrue (thm_app_rel (t) (l) (g)) X )) ,
  (safeExec ATrue (bind ((check_rel (st) (g))) (get_list)) X )
.

Definition check_list_gen_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (target_pre: Z) (thm_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((term * (@list term)) -> (@ StateRelMonad.M  unit B))) (targ_low_level_spec_aux: term) (theo_low_level_spec_aux: term) ,
  “ (safeExec ATrue (bind ((check_rel (theo_low_level_spec_aux) (targ_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (store_term thm_pre theo_low_level_spec_aux )
  **  (store_term target_pre targ_low_level_spec_aux )
|--
EX (theo_low_level_spec: term) (targ_low_level_spec: term) (X_low_level_spec: ((term * (@list term)) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (check_rel (theo_low_level_spec) (targ_low_level_spec)) X_low_level_spec ) ”
  &&  (store_term thm_pre theo_low_level_spec )
  **  (store_term target_pre targ_low_level_spec ))
  **
  ((EX t_2 l_2 retval_2,
  “ (safeExec ATrue (return ((makepair (t_2) (l_2)))) X_low_level_spec ) ”
  &&  (store_term target_pre targ_low_level_spec )
  **  (sll_term_list retval_2 l_2 ))
  -*
  (EX t l retval,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) ((makepair (t) (l)))) X_low_level_spec_aux ) ”
  &&  (store_term target_pre targ_low_level_spec_aux )
  **  (sll_term_list retval l )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.

Axiom proof_of_sub_thm_safety_wit_1 : sub_thm_safety_wit_1.
Axiom proof_of_sub_thm_safety_wit_2 : sub_thm_safety_wit_2.
Axiom proof_of_sub_thm_safety_wit_3 : sub_thm_safety_wit_3.
Axiom proof_of_sub_thm_return_wit_1 : sub_thm_return_wit_1.
Axiom proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Axiom proof_of_sub_thm_return_wit_3 : sub_thm_return_wit_3.
Axiom proof_of_sub_thm_partial_solve_wit_1_pure : sub_thm_partial_solve_wit_1_pure.
Axiom proof_of_sub_thm_partial_solve_wit_1 : sub_thm_partial_solve_wit_1.
Axiom proof_of_sub_thm_partial_solve_wit_2_pure : sub_thm_partial_solve_wit_2_pure.
Axiom proof_of_sub_thm_partial_solve_wit_2 : sub_thm_partial_solve_wit_2.
Axiom proof_of_sub_thm_partial_solve_wit_3_pure : sub_thm_partial_solve_wit_3_pure.
Axiom proof_of_sub_thm_partial_solve_wit_3 : sub_thm_partial_solve_wit_3.
Axiom proof_of_sub_thm_partial_solve_wit_4 : sub_thm_partial_solve_wit_4.
Axiom proof_of_sub_thm_which_implies_wit_1 : sub_thm_which_implies_wit_1.
Axiom proof_of_sub_thm_which_implies_wit_2 : sub_thm_which_implies_wit_2.
Axiom proof_of_separate_imply_safety_wit_1 : separate_imply_safety_wit_1.
Axiom proof_of_separate_imply_safety_wit_2 : separate_imply_safety_wit_2.
Axiom proof_of_separate_imply_safety_wit_3 : separate_imply_safety_wit_3.
Axiom proof_of_separate_imply_safety_wit_4 : separate_imply_safety_wit_4.
Axiom proof_of_separate_imply_safety_wit_5 : separate_imply_safety_wit_5.
Axiom proof_of_separate_imply_safety_wit_6 : separate_imply_safety_wit_6.
Axiom proof_of_separate_imply_safety_wit_7 : separate_imply_safety_wit_7.
Axiom proof_of_separate_imply_safety_wit_8 : separate_imply_safety_wit_8.
Axiom proof_of_separate_imply_return_wit_1 : separate_imply_return_wit_1.
Axiom proof_of_separate_imply_return_wit_2 : separate_imply_return_wit_2.
Axiom proof_of_separate_imply_return_wit_3 : separate_imply_return_wit_3.
Axiom proof_of_separate_imply_return_wit_4 : separate_imply_return_wit_4.
Axiom proof_of_separate_imply_return_wit_5 : separate_imply_return_wit_5.
Axiom proof_of_separate_imply_partial_solve_wit_1 : separate_imply_partial_solve_wit_1.
Axiom proof_of_separate_imply_partial_solve_wit_2_pure : separate_imply_partial_solve_wit_2_pure.
Axiom proof_of_separate_imply_partial_solve_wit_2 : separate_imply_partial_solve_wit_2.
Axiom proof_of_separate_imply_partial_solve_wit_3 : separate_imply_partial_solve_wit_3.
Axiom proof_of_separate_imply_partial_solve_wit_4_pure : separate_imply_partial_solve_wit_4_pure.
Axiom proof_of_separate_imply_partial_solve_wit_4 : separate_imply_partial_solve_wit_4.
Axiom proof_of_separate_imply_partial_solve_wit_5 : separate_imply_partial_solve_wit_5.
Axiom proof_of_separate_imply_partial_solve_wit_6_pure : separate_imply_partial_solve_wit_6_pure.
Axiom proof_of_separate_imply_partial_solve_wit_6 : separate_imply_partial_solve_wit_6.
Axiom proof_of_separate_imply_partial_solve_wit_7 : separate_imply_partial_solve_wit_7.
Axiom proof_of_separate_imply_which_implies_wit_1 : separate_imply_which_implies_wit_1.
Axiom proof_of_separate_imply_which_implies_wit_2 : separate_imply_which_implies_wit_2.
Axiom proof_of_separate_imply_which_implies_wit_3 : separate_imply_which_implies_wit_3.
Axiom proof_of_separate_imply_which_implies_wit_4 : separate_imply_which_implies_wit_4.
Axiom proof_of_separate_imply_which_implies_wit_5 : separate_imply_which_implies_wit_5.
Axiom proof_of_separate_imply_which_implies_wit_6 : separate_imply_which_implies_wit_6.
Axiom proof_of_check_list_gen_safety_wit_1 : check_list_gen_safety_wit_1.
Axiom proof_of_check_list_gen_safety_wit_2 : check_list_gen_safety_wit_2.
Axiom proof_of_check_list_gen_safety_wit_3 : check_list_gen_safety_wit_3.
Axiom proof_of_check_list_gen_safety_wit_4 : check_list_gen_safety_wit_4.
Axiom proof_of_check_list_gen_entail_wit_1 : check_list_gen_entail_wit_1.
Axiom proof_of_check_list_gen_entail_wit_2 : check_list_gen_entail_wit_2.
Axiom proof_of_check_list_gen_return_wit_1 : check_list_gen_return_wit_1.
Axiom proof_of_check_list_gen_return_wit_2 : check_list_gen_return_wit_2.
Axiom proof_of_check_list_gen_partial_solve_wit_1 : check_list_gen_partial_solve_wit_1.
Axiom proof_of_check_list_gen_partial_solve_wit_2 : check_list_gen_partial_solve_wit_2.
Axiom proof_of_check_list_gen_partial_solve_wit_3 : check_list_gen_partial_solve_wit_3.
Axiom proof_of_check_list_gen_partial_solve_wit_4 : check_list_gen_partial_solve_wit_4.
Axiom proof_of_check_list_gen_partial_solve_wit_5 : check_list_gen_partial_solve_wit_5.
Axiom proof_of_check_list_gen_partial_solve_wit_6 : check_list_gen_partial_solve_wit_6.
Axiom proof_of_check_list_gen_partial_solve_wit_7_pure : check_list_gen_partial_solve_wit_7_pure.
Axiom proof_of_check_list_gen_partial_solve_wit_7 : check_list_gen_partial_solve_wit_7.
Axiom proof_of_check_list_gen_partial_solve_wit_8_pure : check_list_gen_partial_solve_wit_8_pure.
Axiom proof_of_check_list_gen_partial_solve_wit_8 : check_list_gen_partial_solve_wit_8.
Axiom proof_of_check_list_gen_partial_solve_wit_9 : check_list_gen_partial_solve_wit_9.
Axiom proof_of_check_list_gen_partial_solve_wit_10 : check_list_gen_partial_solve_wit_10.
Axiom proof_of_check_list_gen_partial_solve_wit_11 : check_list_gen_partial_solve_wit_11.
Axiom proof_of_check_list_gen_which_implies_wit_1 : check_list_gen_which_implies_wit_1.
Axiom proof_of_check_list_gen_which_implies_wit_2 : check_list_gen_which_implies_wit_2.
Axiom proof_of_check_list_gen_which_implies_wit_3 : check_list_gen_which_implies_wit_3.
Axiom proof_of_check_list_gen_which_implies_wit_4 : check_list_gen_which_implies_wit_4.
Axiom proof_of_thm_apply_safety_wit_1 : thm_apply_safety_wit_1.
Axiom proof_of_thm_apply_safety_wit_2 : thm_apply_safety_wit_2.
Axiom proof_of_thm_apply_safety_wit_3 : thm_apply_safety_wit_3.
Axiom proof_of_thm_apply_safety_wit_4 : thm_apply_safety_wit_4.
Axiom proof_of_thm_apply_safety_wit_5 : thm_apply_safety_wit_5.
Axiom proof_of_thm_apply_safety_wit_6 : thm_apply_safety_wit_6.
Axiom proof_of_thm_apply_return_wit_1 : thm_apply_return_wit_1.
Axiom proof_of_thm_apply_return_wit_2 : thm_apply_return_wit_2.
Axiom proof_of_thm_apply_return_wit_3 : thm_apply_return_wit_3.
Axiom proof_of_thm_apply_partial_solve_wit_1 : thm_apply_partial_solve_wit_1.
Axiom proof_of_thm_apply_partial_solve_wit_2 : thm_apply_partial_solve_wit_2.
Axiom proof_of_thm_apply_partial_solve_wit_3 : thm_apply_partial_solve_wit_3.
Axiom proof_of_thm_apply_partial_solve_wit_4_pure : thm_apply_partial_solve_wit_4_pure.
Axiom proof_of_thm_apply_partial_solve_wit_4 : thm_apply_partial_solve_wit_4.
Axiom proof_of_thm_apply_partial_solve_wit_5 : thm_apply_partial_solve_wit_5.
Axiom proof_of_thm_apply_partial_solve_wit_6_pure : thm_apply_partial_solve_wit_6_pure.
Axiom proof_of_thm_apply_partial_solve_wit_6 : thm_apply_partial_solve_wit_6.
Axiom proof_of_thm_apply_partial_solve_wit_7 : thm_apply_partial_solve_wit_7.
Axiom proof_of_thm_apply_partial_solve_wit_8_pure : thm_apply_partial_solve_wit_8_pure.
Axiom proof_of_thm_apply_partial_solve_wit_8 : thm_apply_partial_solve_wit_8.
Axiom proof_of_thm_apply_partial_solve_wit_9_pure : thm_apply_partial_solve_wit_9_pure.
Axiom proof_of_thm_apply_partial_solve_wit_9 : thm_apply_partial_solve_wit_9.
Axiom proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Axiom proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Axiom proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.
Axiom proof_of_thm_apply_which_implies_wit_4 : thm_apply_which_implies_wit_4.
Axiom proof_of_check_list_gen_derive_low_level_spec_aux_by_low_level_spec : check_list_gen_derive_low_level_spec_aux_by_low_level_spec.

End VC_Correct.
