From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
From SimpleC.Verification Require Import SafeExecPrelude.
Require Import ast_lib.
Require Import thm_apply_lib.
Require Import malloc.
Require Import super_poly_sll2.
Local Open Scope sac.
From SimpleC.Verification Require Import safeexec_strategy_goal.
From SimpleC.Verification Require Import safeexec_strategy_proof.

(*----- Function subst_var -----*)

Definition subst_var_safety_wit_1 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition subst_var_safety_wit_2 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition subst_var_safety_wit_3 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition subst_var_safety_wit_4 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 <> (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition subst_var_safety_wit_5 :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 <> (termtypeID (trm)))) (PreH8 : (3 <> (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ False ”
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 <> (termtypeID (trm)))) (PreH8 : (3 <> (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ False ”
).

Definition subst_var_safety_wit_5_split_goal_1 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 <> (termtypeID (trm)))) (PreH8 : (3 <> (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ False ”
.

Definition subst_var_return_wit_1 :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = 0)) (PreH3 : (retval = (list_Z_cmp (var) (src_str)))) (PreH4 : (t_pre <> 0)) (PreH5 : (trm = (TermVar (var)))) (PreH6 : (t_pre <> 0)) (PreH7 : (den_pre <> 0)) (PreH8 : (src_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (0 = (termtypeID (trm)))),
  (store_string den_pre den_str )
  **  (store_string retval_2 den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> retval_2)
|--
  “ (t_pre = t_pre) ”
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = 0)) (PreH5 : (retval = (list_Z_cmp (var) (src_str)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm = (TermVar (var)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 = (termtypeID (trm)))),
  (store_string den_pre den_str )
  **  (store_string retval_2 den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
).

Definition subst_var_return_wit_1_split_goal_spatial :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = 0)) (PreH5 : (retval = (list_Z_cmp (var) (src_str)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm = (TermVar (var)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 = (termtypeID (trm)))),
  (store_string den_pre den_str )
  **  (store_string retval_2 den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_2 :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm)))),
  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  “ (t_pre = t_pre) ”
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval = (list_Z_cmp (var) (src_str)))) (PreH5 : (t_pre <> 0)) (PreH6 : (trm = (TermVar (var)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 = (termtypeID (trm)))),
  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
).

Definition subst_var_return_wit_2_split_goal_spatial :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval = (list_Z_cmp (var) (src_str)))) (PreH5 : (t_pre <> 0)) (PreH6 : (trm = (TermVar (var)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 = (termtypeID (trm)))),
  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_3 :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (typ: const_type) (con: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (trm = (TermConst (typ) (con)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm)))) (PreH8 : (1 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (t_pre = t_pre) ”
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (typ: const_type) (con: Z) (PreH1 : (con <= INT_MAX)) (PreH2 : ((ctID (typ)) <= INT_MAX)) (PreH3 : ((termtypeID (trm)) <= INT_MAX)) (PreH4 : (con >= INT_MIN)) (PreH5 : ((ctID (typ)) >= INT_MIN)) (PreH6 : ((termtypeID (trm)) >= INT_MIN)) (PreH7 : (t_pre <> 0)) (PreH8 : (trm = (TermConst (typ) (con)))) (PreH9 : (t_pre <> 0)) (PreH10 : (den_pre <> 0)) (PreH11 : (src_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (0 <> (termtypeID (trm)))) (PreH14 : (1 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
).

Definition subst_var_return_wit_3_split_goal_spatial :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (typ: const_type) (con: Z) (PreH1 : (con <= INT_MAX)) (PreH2 : ((ctID (typ)) <= INT_MAX)) (PreH3 : ((termtypeID (trm)) <= INT_MAX)) (PreH4 : (con >= INT_MIN)) (PreH5 : ((ctID (typ)) >= INT_MIN)) (PreH6 : ((termtypeID (trm)) >= INT_MIN)) (PreH7 : (t_pre <> 0)) (PreH8 : (trm = (TermConst (typ) (con)))) (PreH9 : (t_pre <> 0)) (PreH10 : (den_pre <> 0)) (PreH11 : (src_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (0 <> (termtypeID (trm)))) (PreH14 : (1 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_4 :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = z)) (PreH2 : (retval = y)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm)))) (PreH10 : (1 <> (termtypeID (trm)))) (PreH11 : (2 = (termtypeID (trm)))),
  (store_term z (term_subst_v (den_str) (src_str) (rt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  “ (t_pre = t_pre) ”
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval_2 = z)) (PreH4 : (retval = y)) (PreH5 : (t_pre <> 0)) (PreH6 : (trm = (TermApply (lt) (rt)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 <> (termtypeID (trm)))) (PreH12 : (1 <> (termtypeID (trm)))) (PreH13 : (2 = (termtypeID (trm)))),
  (store_term z (term_subst_v (den_str) (src_str) (rt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
).

Definition subst_var_return_wit_4_split_goal_spatial :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval_2 = z)) (PreH4 : (retval = y)) (PreH5 : (t_pre <> 0)) (PreH6 : (trm = (TermApply (lt) (rt)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 <> (termtypeID (trm)))) (PreH12 : (1 <> (termtypeID (trm)))) (PreH13 : (2 = (termtypeID (trm)))),
  (store_term z (term_subst_v (den_str) (src_str) (rt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_5 :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = z)) (PreH2 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm)))) (PreH10 : (1 <> (termtypeID (trm)))) (PreH11 : (2 <> (termtypeID (trm)))) (PreH12 : (3 = (termtypeID (trm)))) (PreH13 : (retval <> 0)),
  (store_term z (term_subst_v (den_str) (src_str) (qterm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  “ (t_pre = t_pre) ”
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : (retval_2 = z)) (PreH6 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH7 : (t_pre <> 0)) (PreH8 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH9 : (t_pre <> 0)) (PreH10 : (den_pre <> 0)) (PreH11 : (src_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (0 <> (termtypeID (trm)))) (PreH14 : (1 <> (termtypeID (trm)))) (PreH15 : (2 <> (termtypeID (trm)))) (PreH16 : (3 = (termtypeID (trm)))) (PreH17 : (retval <> 0)),
  (store_term z (term_subst_v (den_str) (src_str) (qterm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
).

Definition subst_var_return_wit_5_split_goal_spatial :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : (retval_2 = z)) (PreH6 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH7 : (t_pre <> 0)) (PreH8 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH9 : (t_pre <> 0)) (PreH10 : (den_pre <> 0)) (PreH11 : (src_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (0 <> (termtypeID (trm)))) (PreH14 : (1 <> (termtypeID (trm)))) (PreH15 : (2 <> (termtypeID (trm)))) (PreH16 : (3 = (termtypeID (trm)))) (PreH17 : (retval <> 0)),
  (store_term z (term_subst_v (den_str) (src_str) (qterm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_return_wit_6 :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH2 : (t_pre <> 0)) (PreH3 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm)))) (PreH9 : (1 <> (termtypeID (trm)))) (PreH10 : (2 <> (termtypeID (trm)))) (PreH11 : (3 = (termtypeID (trm)))) (PreH12 : (retval = 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
|--
  “ (t_pre = t_pre) ”
  &&  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm)))) (PreH13 : (1 <> (termtypeID (trm)))) (PreH14 : (2 <> (termtypeID (trm)))) (PreH15 : (3 = (termtypeID (trm)))) (PreH16 : (retval = 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
).

Definition subst_var_return_wit_6_split_goal_spatial :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm)))) (PreH13 : (1 <> (termtypeID (trm)))) (PreH14 : (2 <> (termtypeID (trm)))) (PreH15 : (3 = (termtypeID (trm)))) (PreH16 : (retval = 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
|--
  (store_term t_pre (term_subst_v (den_str) (src_str) (trm)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
.

Definition subst_var_partial_solve_wit_1 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (den_pre <> 0)) (PreH2 : (src_pre <> 0)) (PreH3 : (t_pre <> 0)),
  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  (store_term t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_2_pure :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 = (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 0) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_var_partial_solve_wit_2_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_2 := subst_var_partial_solve_wit_2_pure -> subst_var_partial_solve_wit_2_aux.

Definition subst_var_partial_solve_wit_3 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (PreH1 : (t_pre <> 0)) (PreH2 : (trm = (TermVar (var)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (t_pre <> 0) ”
  &&  “ (trm = (TermVar (var))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm))) ”
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_4_pure :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm)))),
  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string den_pre den_str )
|--
  “ (y <> 0) ”
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (retval = (list_Z_cmp (var) (src_str)))) (PreH5 : (t_pre <> 0)) (PreH6 : (trm = (TermVar (var)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 = (termtypeID (trm)))),
  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string den_pre den_str )
|--
  “ (y <> 0) ”
).

Definition subst_var_partial_solve_wit_4_pure_split_goal_1 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (retval = (list_Z_cmp (var) (src_str)))) (PreH5 : (t_pre <> 0)) (PreH6 : (trm = (TermVar (var)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 = (termtypeID (trm)))),
  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string den_pre den_str )
|--
  “ (y <> 0) ”
.

Definition subst_var_partial_solve_wit_4_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm)))),
  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  “ (y <> 0) ”
  &&  “ (retval = 0) ”
  &&  “ (retval = (list_Z_cmp (var) (src_str))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm = (TermVar (var))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm))) ”
  &&  (store_string y var )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_4 := subst_var_partial_solve_wit_4_pure -> subst_var_partial_solve_wit_4_aux.

Definition subst_var_partial_solve_wit_5 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm)))),
  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string den_pre den_str )
|--
  “ (retval = 0) ”
  &&  “ (retval = (list_Z_cmp (var) (src_str))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm = (TermVar (var))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm))) ”
  &&  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
.

Definition subst_var_partial_solve_wit_6_pure :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 = (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 1) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_var_partial_solve_wit_6_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 1) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm))) ”
  &&  “ (1 = (termtypeID (trm))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_6 := subst_var_partial_solve_wit_6_pure -> subst_var_partial_solve_wit_6_aux.

Definition subst_var_partial_solve_wit_7_pure :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 = (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 2) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_var_partial_solve_wit_7_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 2) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm))) ”
  &&  “ (1 <> (termtypeID (trm))) ”
  &&  “ (2 = (termtypeID (trm))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_7 := subst_var_partial_solve_wit_7_pure -> subst_var_partial_solve_wit_7_aux.

Definition subst_var_partial_solve_wit_8_pure :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : (t_pre <> 0)) (PreH2 : (trm = (TermApply (lt) (rt)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm)))) (PreH8 : (1 <> (termtypeID (trm)))) (PreH9 : (2 = (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (y <> 0) ”
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm)))) (PreH10 : (1 <> (termtypeID (trm)))) (PreH11 : (2 = (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (y <> 0) ”
).

Definition subst_var_partial_solve_wit_8_pure_split_goal_1 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm)))) (PreH10 : (1 <> (termtypeID (trm)))) (PreH11 : (2 = (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (y <> 0) ”
.

Definition subst_var_partial_solve_wit_8_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : (t_pre <> 0)) (PreH2 : (trm = (TermApply (lt) (rt)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm)))) (PreH8 : (1 <> (termtypeID (trm)))) (PreH9 : (2 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (y <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm = (TermApply (lt) (rt))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm))) ”
  &&  “ (1 <> (termtypeID (trm))) ”
  &&  “ (2 = (termtypeID (trm))) ”
  &&  (store_term y lt )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
.

Definition subst_var_partial_solve_wit_8 := subst_var_partial_solve_wit_8_pure -> subst_var_partial_solve_wit_8_aux.

Definition subst_var_partial_solve_wit_9_pure :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : (retval = y)) (PreH2 : (t_pre <> 0)) (PreH3 : (trm = (TermApply (lt) (rt)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm)))) (PreH9 : (1 <> (termtypeID (trm)))) (PreH10 : (2 = (termtypeID (trm)))),
  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval = y)) (PreH4 : (t_pre <> 0)) (PreH5 : (trm = (TermApply (lt) (rt)))) (PreH6 : (t_pre <> 0)) (PreH7 : (den_pre <> 0)) (PreH8 : (src_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (0 <> (termtypeID (trm)))) (PreH11 : (1 <> (termtypeID (trm)))) (PreH12 : (2 = (termtypeID (trm)))),
  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (z <> 0) ”
).

Definition subst_var_partial_solve_wit_9_pure_split_goal_1 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : ((termtypeID (trm)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) >= INT_MIN)) (PreH3 : (retval = y)) (PreH4 : (t_pre <> 0)) (PreH5 : (trm = (TermApply (lt) (rt)))) (PreH6 : (t_pre <> 0)) (PreH7 : (den_pre <> 0)) (PreH8 : (src_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (0 <> (termtypeID (trm)))) (PreH11 : (1 <> (termtypeID (trm)))) (PreH12 : (2 = (termtypeID (trm)))),
  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (z <> 0) ”
.

Definition subst_var_partial_solve_wit_9_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : (retval = y)) (PreH2 : (t_pre <> 0)) (PreH3 : (trm = (TermApply (lt) (rt)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm)))) (PreH9 : (1 <> (termtypeID (trm)))) (PreH10 : (2 = (termtypeID (trm)))),
  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  (store_string den_pre den_str )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
  &&  “ (retval = y) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm = (TermApply (lt) (rt))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm))) ”
  &&  “ (1 <> (termtypeID (trm))) ”
  &&  “ (2 = (termtypeID (trm))) ”
  &&  (store_term z rt )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
  **  (store_term y (term_subst_v (den_str) (src_str) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
.

Definition subst_var_partial_solve_wit_9 := subst_var_partial_solve_wit_9_pure -> subst_var_partial_solve_wit_9_aux.

Definition subst_var_partial_solve_wit_10_pure :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 <> (termtypeID (trm)))) (PreH8 : (3 = (termtypeID (trm)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 3) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_var_partial_solve_wit_10_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm)))) (PreH6 : (1 <> (termtypeID (trm)))) (PreH7 : (2 <> (termtypeID (trm)))) (PreH8 : (3 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ ((termtypeID (trm)) = 3) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm))) ”
  &&  “ (1 <> (termtypeID (trm))) ”
  &&  “ (2 <> (termtypeID (trm))) ”
  &&  “ (3 = (termtypeID (trm))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_10 := subst_var_partial_solve_wit_10_pure -> subst_var_partial_solve_wit_10_aux.

Definition subst_var_partial_solve_wit_11 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : (t_pre <> 0)) (PreH2 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm)))) (PreH8 : (1 <> (termtypeID (trm)))) (PreH9 : (2 <> (termtypeID (trm)))) (PreH10 : (3 = (termtypeID (trm)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
|--
  “ (t_pre <> 0) ”
  &&  “ (trm = (TermQuant (qt) (qvar) (qterm))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm))) ”
  &&  “ (1 <> (termtypeID (trm))) ”
  &&  “ (2 <> (termtypeID (trm))) ”
  &&  “ (3 = (termtypeID (trm))) ”
  &&  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
.

Definition subst_var_partial_solve_wit_12_pure :=
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH2 : (t_pre <> 0)) (PreH3 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm)))) (PreH9 : (1 <> (termtypeID (trm)))) (PreH10 : (2 <> (termtypeID (trm)))) (PreH11 : (3 = (termtypeID (trm)))) (PreH12 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string den_pre den_str )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
) \/
(
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm)))) (PreH13 : (1 <> (termtypeID (trm)))) (PreH14 : (2 <> (termtypeID (trm)))) (PreH15 : (3 = (termtypeID (trm)))) (PreH16 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string den_pre den_str )
|--
  “ (z <> 0) ”
).

Definition subst_var_partial_solve_wit_12_pure_split_goal_1 :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm)))) (PreH13 : (1 <> (termtypeID (trm)))) (PreH14 : (2 <> (termtypeID (trm)))) (PreH15 : (3 = (termtypeID (trm)))) (PreH16 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string den_pre den_str )
|--
  “ (z <> 0) ”
.

Definition subst_var_partial_solve_wit_12_aux :=
forall (den_str: (@list Z)) (src_str: (@list Z)) (trm: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : (retval = (list_Z_cmp (qvar) (src_str)))) (PreH2 : (t_pre <> 0)) (PreH3 : (trm = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm)))) (PreH9 : (1 <> (termtypeID (trm)))) (PreH10 : (2 <> (termtypeID (trm)))) (PreH11 : (3 = (termtypeID (trm)))) (PreH12 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_string den_pre den_str )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
  &&  “ (retval = (list_Z_cmp (qvar) (src_str))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm = (TermQuant (qt) (qvar) (qterm))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm))) ”
  &&  “ (1 <> (termtypeID (trm))) ”
  &&  “ (2 <> (termtypeID (trm))) ”
  &&  “ (3 = (termtypeID (trm))) ”
  &&  “ (retval <> 0) ”
  &&  (store_term z qterm )
  **  (store_string src_pre src_str )
  **  (store_string den_pre den_str )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
.

Definition subst_var_partial_solve_wit_12 := subst_var_partial_solve_wit_12_pure -> subst_var_partial_solve_wit_12_aux.

Definition subst_var_which_implies_wit_1 :=
(
forall (trm: term) (t: Z),
  (store_term t trm )
|--
  “ (t <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
) \/
(
forall (trm: term) (t: Z),
  (store_term t trm )
|--
  “ (t <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
).

Definition subst_var_which_implies_wit_1_split_goal_1 :=
forall (trm: term) (t: Z),
  (store_term t trm )
|--
  “ (t <> 0) ”
.

Definition subst_var_which_implies_wit_1_split_goal_spatial :=
forall (trm: term) (t: Z),
  (store_term t trm )
|--
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
.

Definition subst_var_which_implies_wit_2 :=
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 0)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (y: Z) (var: (@list Z)),
  “ (t <> 0) ”
  &&  “ (trm = (TermVar (var))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
) \/
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 0)) (PreH2 : (t <> 0)),
  (store_term' t trm )
|--
  EX (y: Z) (var: (@list Z)),
  “ (t <> 0) ”
  &&  “ (trm = (TermVar (var))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
).

Definition subst_var_which_implies_wit_3 :=
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 1)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (typ: const_type) (con: Z),
  “ (t <> 0) ”
  &&  “ (trm = (TermConst (typ) (con))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
) \/
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 1)) (PreH2 : (t <> 0)),
  (store_term' t trm )
|--
  EX (typ: const_type) (con: Z),
  “ (t <> 0) ”
  &&  “ (trm = (TermConst (typ) (con))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
).

Definition subst_var_which_implies_wit_4 :=
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 2)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (z: Z) (y: Z) (lt: term) (rt: term),
  “ (t <> 0) ”
  &&  “ (trm = (TermApply (lt) (rt))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
) \/
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 2)) (PreH2 : (t <> 0)),
  (store_term' t trm )
|--
  EX (z: Z) (y: Z) (lt: term) (rt: term),
  “ (t <> 0) ”
  &&  “ (trm = (TermApply (lt) (rt))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
).

Definition subst_var_which_implies_wit_5 :=
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 3)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
|--
  EX (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term),
  “ (t <> 0) ”
  &&  “ (trm = (TermQuant (qt) (qvar) (qterm))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
) \/
(
forall (trm: term) (t: Z) (PreH1 : ((termtypeID (trm)) = 3)) (PreH2 : (t <> 0)),
  (store_term' t trm )
|--
  EX (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term),
  “ (t <> 0) ”
  &&  “ (trm = (TermQuant (qt) (qvar) (qterm))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
).

(*----- Function subst_term -----*)

Definition subst_term_safety_wit_1 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition subst_term_safety_wit_2 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition subst_term_safety_wit_3 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition subst_term_safety_wit_4 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 <> (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition subst_term_safety_wit_5 :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 <> (termtypeID (trm_implementation)))) (PreH8 : (3 <> (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ False ”
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 <> (termtypeID (trm_implementation)))) (PreH8 : (3 <> (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ False ”
).

Definition subst_term_safety_wit_5_split_goal_1 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 <> (termtypeID (trm_implementation)))) (PreH8 : (3 <> (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ False ”
.

Definition subst_term_return_wit_1 :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_2 = (list_Z_cmp (var) (src_str_implementation)))) (PreH4 : (t_pre <> 0)) (PreH5 : (trm_implementation = (TermVar (var)))) (PreH6 : (t_pre <> 0)) (PreH7 : (den_pre <> 0)) (PreH8 : (src_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (0 = (termtypeID (trm_implementation)))),
  (store_term den_pre den_term_implementation )
  **  (store_term retval den_term_implementation )
  **  (store_string src_pre src_str_implementation )
|--
  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_2 = (list_Z_cmp (var) (src_str_implementation)))) (PreH4 : (t_pre <> 0)) (PreH5 : (trm_implementation = (TermVar (var)))) (PreH6 : (t_pre <> 0)) (PreH7 : (den_pre <> 0)) (PreH8 : (src_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (0 = (termtypeID (trm_implementation)))),
  (store_term den_pre den_term_implementation )
  **  (store_term retval den_term_implementation )
  **  (store_string src_pre src_str_implementation )
|--
  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
).

Definition subst_term_return_wit_1_split_goal_spatial :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_2 = (list_Z_cmp (var) (src_str_implementation)))) (PreH4 : (t_pre <> 0)) (PreH5 : (trm_implementation = (TermVar (var)))) (PreH6 : (t_pre <> 0)) (PreH7 : (den_pre <> 0)) (PreH8 : (src_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (0 = (termtypeID (trm_implementation)))),
  (store_term den_pre den_term_implementation )
  **  (store_term retval den_term_implementation )
  **  (store_string src_pre src_str_implementation )
|--
  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
.

Definition subst_term_return_wit_2 :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str_implementation)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm_implementation)))),
  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval = (list_Z_cmp (var) (src_str_implementation)))) (PreH5 : (t_pre <> 0)) (PreH6 : (trm_implementation = (TermVar (var)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 = (termtypeID (trm_implementation)))),
  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
).

Definition subst_term_return_wit_2_split_goal_spatial :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (retval = (list_Z_cmp (var) (src_str_implementation)))) (PreH5 : (t_pre <> 0)) (PreH6 : (trm_implementation = (TermVar (var)))) (PreH7 : (t_pre <> 0)) (PreH8 : (den_pre <> 0)) (PreH9 : (src_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (0 = (termtypeID (trm_implementation)))),
  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
.

Definition subst_term_return_wit_3 :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (typ: const_type) (con: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermConst (typ) (con)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm_implementation)))) (PreH8 : (1 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (typ: const_type) (con: Z) (PreH1 : (con <= INT_MAX)) (PreH2 : ((ctID (typ)) <= INT_MAX)) (PreH3 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH4 : (con >= INT_MIN)) (PreH5 : ((ctID (typ)) >= INT_MIN)) (PreH6 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH7 : (t_pre <> 0)) (PreH8 : (trm_implementation = (TermConst (typ) (con)))) (PreH9 : (t_pre <> 0)) (PreH10 : (den_pre <> 0)) (PreH11 : (src_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (0 <> (termtypeID (trm_implementation)))) (PreH14 : (1 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
).

Definition subst_term_return_wit_3_split_goal_spatial :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (typ: const_type) (con: Z) (PreH1 : (con <= INT_MAX)) (PreH2 : ((ctID (typ)) <= INT_MAX)) (PreH3 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH4 : (con >= INT_MIN)) (PreH5 : ((ctID (typ)) >= INT_MIN)) (PreH6 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH7 : (t_pre <> 0)) (PreH8 : (trm_implementation = (TermConst (typ) (con)))) (PreH9 : (t_pre <> 0)) (PreH10 : (den_pre <> 0)) (PreH11 : (src_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (0 <> (termtypeID (trm_implementation)))) (PreH14 : (1 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
.

Definition subst_term_return_wit_4 :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (lt: term) (rt: term) (retval: Z) (retval_2: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermApply (lt) (rt)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm_implementation)))) (PreH8 : (1 <> (termtypeID (trm_implementation)))) (PreH9 : (2 = (termtypeID (trm_implementation)))),
  (store_term retval_2 (term_subst_t (den_term_implementation) (src_str_implementation) (rt)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (lt: term) (rt: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm_implementation)))) (PreH10 : (1 <> (termtypeID (trm_implementation)))) (PreH11 : (2 = (termtypeID (trm_implementation)))),
  (store_term retval_2 (term_subst_t (den_term_implementation) (src_str_implementation) (rt)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
).

Definition subst_term_return_wit_4_split_goal_spatial :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (lt: term) (rt: term) (retval: Z) (retval_2: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm_implementation)))) (PreH10 : (1 <> (termtypeID (trm_implementation)))) (PreH11 : (2 = (termtypeID (trm_implementation)))),
  (store_term retval_2 (term_subst_t (den_term_implementation) (src_str_implementation) (rt)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
.

Definition subst_term_return_wit_5 :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) (PreH1 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH2 : (t_pre <> 0)) (PreH3 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm_implementation)))) (PreH9 : (1 <> (termtypeID (trm_implementation)))) (PreH10 : (2 <> (termtypeID (trm_implementation)))) (PreH11 : (3 = (termtypeID (trm_implementation)))) (PreH12 : (retval <> 0)),
  (store_term retval_2 (term_subst_t (den_term_implementation) (src_str_implementation) (qterm)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm_implementation)))) (PreH13 : (1 <> (termtypeID (trm_implementation)))) (PreH14 : (2 <> (termtypeID (trm_implementation)))) (PreH15 : (3 = (termtypeID (trm_implementation)))) (PreH16 : (retval <> 0)),
  (store_term retval_2 (term_subst_t (den_term_implementation) (src_str_implementation) (qterm)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
).

Definition subst_term_return_wit_5_split_goal_spatial :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (retval_2: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm_implementation)))) (PreH13 : (1 <> (termtypeID (trm_implementation)))) (PreH14 : (2 <> (termtypeID (trm_implementation)))) (PreH15 : (3 = (termtypeID (trm_implementation)))) (PreH16 : (retval <> 0)),
  (store_term retval_2 (term_subst_t (den_term_implementation) (src_str_implementation) (qterm)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
.

Definition subst_term_return_wit_6 :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH2 : (t_pre <> 0)) (PreH3 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm_implementation)))) (PreH9 : (1 <> (termtypeID (trm_implementation)))) (PreH10 : (2 <> (termtypeID (trm_implementation)))) (PreH11 : (3 = (termtypeID (trm_implementation)))) (PreH12 : (retval = 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm_implementation)))) (PreH13 : (1 <> (termtypeID (trm_implementation)))) (PreH14 : (2 <> (termtypeID (trm_implementation)))) (PreH15 : (3 = (termtypeID (trm_implementation)))) (PreH16 : (retval = 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
).

Definition subst_term_return_wit_6_split_goal_spatial :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm_implementation)))) (PreH13 : (1 <> (termtypeID (trm_implementation)))) (PreH14 : (2 <> (termtypeID (trm_implementation)))) (PreH15 : (3 = (termtypeID (trm_implementation)))) (PreH16 : (retval = 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term_implementation )
|--
  (store_term t_pre (term_subst_t (den_term_implementation) (src_str_implementation) (trm_implementation)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
.

Definition subst_term_partial_solve_wit_1 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (den_pre <> 0)) (PreH2 : (src_pre <> 0)) (PreH3 : (t_pre <> 0)),
  (store_term t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  (store_term t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_2_pure :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 = (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 0) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_term_partial_solve_wit_2_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm_implementation))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_2 := subst_term_partial_solve_wit_2_pure -> subst_term_partial_solve_wit_2_aux.

Definition subst_term_partial_solve_wit_3 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermVar (var)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm_implementation))) ”
  &&  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_4_pure :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str_implementation)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm_implementation)))),
  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_term den_pre den_term_implementation )
|--
  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
.

Definition subst_term_partial_solve_wit_4_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (y: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str_implementation)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm_implementation)))),
  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_term den_pre den_term_implementation )
|--
  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
  &&  “ (retval = 0) ”
  &&  “ (retval = (list_Z_cmp (var) (src_str_implementation))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm_implementation))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_4 := subst_term_partial_solve_wit_4_pure -> subst_term_partial_solve_wit_4_aux.

Definition subst_term_partial_solve_wit_5 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str_implementation)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm_implementation)))),
  (store_term t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (retval = 0) ”
  &&  “ (retval = (list_Z_cmp (var) (src_str_implementation))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm_implementation))) ”
  &&  (store_term t_pre (TermVar (var)) )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_6 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (var: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (list_Z_cmp (var) (src_str_implementation)))) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermVar (var)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 = (termtypeID (trm_implementation)))),
  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (retval = 0) ”
  &&  “ (retval = (list_Z_cmp (var) (src_str_implementation))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 = (termtypeID (trm_implementation))) ”
  &&  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
.

Definition subst_term_partial_solve_wit_7_pure :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 = (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 1) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_term_partial_solve_wit_7_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 1) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm_implementation))) ”
  &&  “ (1 = (termtypeID (trm_implementation))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_7 := subst_term_partial_solve_wit_7_pure -> subst_term_partial_solve_wit_7_aux.

Definition subst_term_partial_solve_wit_8_pure :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 = (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 2) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_term_partial_solve_wit_8_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 2) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm_implementation))) ”
  &&  “ (1 <> (termtypeID (trm_implementation))) ”
  &&  “ (2 = (termtypeID (trm_implementation))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_8 := subst_term_partial_solve_wit_8_pure -> subst_term_partial_solve_wit_8_aux.

Definition subst_term_partial_solve_wit_9_pure :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermApply (lt) (rt)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm_implementation)))) (PreH8 : (1 <> (termtypeID (trm_implementation)))) (PreH9 : (2 = (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (y <> 0) ”
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm_implementation)))) (PreH10 : (1 <> (termtypeID (trm_implementation)))) (PreH11 : (2 = (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (y <> 0) ”
).

Definition subst_term_partial_solve_wit_9_pure_split_goal_1 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm_implementation)))) (PreH10 : (1 <> (termtypeID (trm_implementation)))) (PreH11 : (2 = (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (y <> 0) ”
.

Definition subst_term_partial_solve_wit_9_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (lt: term) (rt: term) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermApply (lt) (rt)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm_implementation)))) (PreH8 : (1 <> (termtypeID (trm_implementation)))) (PreH9 : (2 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (y <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermApply (lt) (rt))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm_implementation))) ”
  &&  “ (1 <> (termtypeID (trm_implementation))) ”
  &&  “ (2 = (termtypeID (trm_implementation))) ”
  &&  (store_term y lt )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
.

Definition subst_term_partial_solve_wit_9 := subst_term_partial_solve_wit_9_pure -> subst_term_partial_solve_wit_9_aux.

Definition subst_term_partial_solve_wit_10_pure :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermApply (lt) (rt)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm_implementation)))) (PreH8 : (1 <> (termtypeID (trm_implementation)))) (PreH9 : (2 = (termtypeID (trm_implementation)))),
  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm_implementation)))) (PreH10 : (1 <> (termtypeID (trm_implementation)))) (PreH11 : (2 = (termtypeID (trm_implementation)))),
  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (z <> 0) ”
).

Definition subst_term_partial_solve_wit_10_pure_split_goal_1 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t_pre <> 0)) (PreH4 : (trm_implementation = (TermApply (lt) (rt)))) (PreH5 : (t_pre <> 0)) (PreH6 : (den_pre <> 0)) (PreH7 : (src_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (0 <> (termtypeID (trm_implementation)))) (PreH10 : (1 <> (termtypeID (trm_implementation)))) (PreH11 : (2 = (termtypeID (trm_implementation)))),
  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
|--
  “ (z <> 0) ”
.

Definition subst_term_partial_solve_wit_10_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (lt: term) (rt: term) (retval: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermApply (lt) (rt)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm_implementation)))) (PreH8 : (1 <> (termtypeID (trm_implementation)))) (PreH9 : (2 = (termtypeID (trm_implementation)))),
  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  (store_term den_pre den_term_implementation )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term z rt )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermApply (lt) (rt))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm_implementation))) ”
  &&  “ (1 <> (termtypeID (trm_implementation))) ”
  &&  “ (2 = (termtypeID (trm_implementation))) ”
  &&  (store_term z rt )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
  **  (store_term retval (term_subst_t (den_term_implementation) (src_str_implementation) (lt)) )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> retval)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
.

Definition subst_term_partial_solve_wit_10 := subst_term_partial_solve_wit_10_pure -> subst_term_partial_solve_wit_10_aux.

Definition subst_term_partial_solve_wit_11_pure :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 <> (termtypeID (trm_implementation)))) (PreH8 : (3 = (termtypeID (trm_implementation)))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 3) ”
  &&  “ (t_pre <> 0) ”
.

Definition subst_term_partial_solve_wit_11_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (den_pre <> 0)) (PreH3 : (src_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (0 <> (termtypeID (trm_implementation)))) (PreH6 : (1 <> (termtypeID (trm_implementation)))) (PreH7 : (2 <> (termtypeID (trm_implementation)))) (PreH8 : (3 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ ((termtypeID (trm_implementation)) = 3) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm_implementation))) ”
  &&  “ (1 <> (termtypeID (trm_implementation))) ”
  &&  “ (2 <> (termtypeID (trm_implementation))) ”
  &&  “ (3 = (termtypeID (trm_implementation))) ”
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t_pre trm_implementation )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_11 := subst_term_partial_solve_wit_11_pure -> subst_term_partial_solve_wit_11_aux.

Definition subst_term_partial_solve_wit_12 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (PreH1 : (t_pre <> 0)) (PreH2 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH3 : (t_pre <> 0)) (PreH4 : (den_pre <> 0)) (PreH5 : (src_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (0 <> (termtypeID (trm_implementation)))) (PreH8 : (1 <> (termtypeID (trm_implementation)))) (PreH9 : (2 <> (termtypeID (trm_implementation)))) (PreH10 : (3 = (termtypeID (trm_implementation)))),
  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
|--
  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermQuant (qt) (qvar) (qterm))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm_implementation))) ”
  &&  “ (1 <> (termtypeID (trm_implementation))) ”
  &&  “ (2 <> (termtypeID (trm_implementation))) ”
  &&  “ (3 = (termtypeID (trm_implementation))) ”
  &&  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term_implementation )
.

Definition subst_term_partial_solve_wit_13_pure :=
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH2 : (t_pre <> 0)) (PreH3 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm_implementation)))) (PreH9 : (1 <> (termtypeID (trm_implementation)))) (PreH10 : (2 <> (termtypeID (trm_implementation)))) (PreH11 : (3 = (termtypeID (trm_implementation)))) (PreH12 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_term den_pre den_term_implementation )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
) \/
(
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm_implementation)))) (PreH13 : (1 <> (termtypeID (trm_implementation)))) (PreH14 : (2 <> (termtypeID (trm_implementation)))) (PreH15 : (3 = (termtypeID (trm_implementation)))) (PreH16 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_term den_pre den_term_implementation )
|--
  “ (z <> 0) ”
).

Definition subst_term_partial_solve_wit_13_pure_split_goal_1 :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : ((qtID (qt)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH3 : ((qtID (qt)) >= INT_MIN)) (PreH4 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH5 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH6 : (t_pre <> 0)) (PreH7 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH8 : (t_pre <> 0)) (PreH9 : (den_pre <> 0)) (PreH10 : (src_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (0 <> (termtypeID (trm_implementation)))) (PreH13 : (1 <> (termtypeID (trm_implementation)))) (PreH14 : (2 <> (termtypeID (trm_implementation)))) (PreH15 : (3 = (termtypeID (trm_implementation)))) (PreH16 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  ((( &( "den" ) )) # Ptr  |-> den_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (store_term den_pre den_term_implementation )
|--
  “ (z <> 0) ”
.

Definition subst_term_partial_solve_wit_13_aux :=
forall (den_term_implementation: term) (src_str_implementation: (@list Z)) (trm_implementation: term) (den_pre: Z) (src_pre: Z) (t_pre: Z) (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) (PreH1 : (retval = (list_Z_cmp (qvar) (src_str_implementation)))) (PreH2 : (t_pre <> 0)) (PreH3 : (trm_implementation = (TermQuant (qt) (qvar) (qterm)))) (PreH4 : (t_pre <> 0)) (PreH5 : (den_pre <> 0)) (PreH6 : (src_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (0 <> (termtypeID (trm_implementation)))) (PreH9 : (1 <> (termtypeID (trm_implementation)))) (PreH10 : (2 <> (termtypeID (trm_implementation)))) (PreH11 : (3 = (termtypeID (trm_implementation)))) (PreH12 : (retval <> 0)),
  (store_string y qvar )
  **  (store_string src_pre src_str_implementation )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_term z qterm )
  **  (store_term den_pre den_term_implementation )
|--
  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (z <> 0) ”
  &&  “ (retval = (list_Z_cmp (qvar) (src_str_implementation))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (trm_implementation = (TermQuant (qt) (qvar) (qterm))) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (den_pre <> 0) ”
  &&  “ (src_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (0 <> (termtypeID (trm_implementation))) ”
  &&  “ (1 <> (termtypeID (trm_implementation))) ”
  &&  “ (2 <> (termtypeID (trm_implementation))) ”
  &&  “ (3 = (termtypeID (trm_implementation))) ”
  &&  “ (retval <> 0) ”
  &&  (store_term z qterm )
  **  (store_string src_pre src_str_implementation )
  **  (store_term den_pre den_term_implementation )
  **  (store_string y qvar )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
.

Definition subst_term_partial_solve_wit_13 := subst_term_partial_solve_wit_13_pure -> subst_term_partial_solve_wit_13_aux.

Definition subst_term_which_implies_wit_1 :=
(
forall (trm_implementation: term) (t: Z),
  (store_term t trm_implementation )
|--
  “ (t <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t trm_implementation )
) \/
(
forall (trm_implementation: term) (t: Z),
  (store_term t trm_implementation )
|--
  “ (t <> 0) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t trm_implementation )
).

Definition subst_term_which_implies_wit_1_split_goal_1 :=
forall (trm_implementation: term) (t: Z),
  (store_term t trm_implementation )
|--
  “ (t <> 0) ”
.

Definition subst_term_which_implies_wit_1_split_goal_spatial :=
forall (trm_implementation: term) (t: Z),
  (store_term t trm_implementation )
|--
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t trm_implementation )
.

Definition subst_term_which_implies_wit_2 :=
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 0)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t trm_implementation )
|--
  EX (y: Z) (var: (@list Z)),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
) \/
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 0)) (PreH2 : (t <> 0)),
  (store_term' t trm_implementation )
|--
  EX (y: Z) (var: (@list Z)),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermVar (var))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
).

Definition subst_term_which_implies_wit_3 :=
(
forall (trm_implementation: term) (var: (@list Z)) (y: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (trm_implementation = (TermVar (var)))),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
|--
  (store_term t trm_implementation )
) \/
(
forall (trm_implementation: term) (var: (@list Z)) (y: Z) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t <> 0)) (PreH4 : (trm_implementation = (TermVar (var)))),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
|--
  (store_term t trm_implementation )
).

Definition subst_term_which_implies_wit_3_split_goal_spatial :=
forall (trm_implementation: term) (var: (@list Z)) (y: Z) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) <= INT_MAX)) (PreH2 : ((termtypeID (trm_implementation)) >= INT_MIN)) (PreH3 : (t <> 0)) (PreH4 : (trm_implementation = (TermVar (var)))),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Var")) # Ptr  |-> y)
  **  (store_string y var )
|--
  (store_term t trm_implementation )
.

Definition subst_term_which_implies_wit_4 :=
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 1)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t trm_implementation )
|--
  EX (typ: const_type) (con: Z),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermConst (typ) (con))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
) \/
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 1)) (PreH2 : (t <> 0)),
  (store_term' t trm_implementation )
|--
  EX (typ: const_type) (con: Z),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermConst (typ) (con))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (typ)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> con)
).

Definition subst_term_which_implies_wit_5 :=
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 2)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t trm_implementation )
|--
  EX (z: Z) (y: Z) (lt: term) (rt: term),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermApply (lt) (rt))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
) \/
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 2)) (PreH2 : (t <> 0)),
  (store_term' t trm_implementation )
|--
  EX (z: Z) (y: Z) (lt: term) (rt: term),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermApply (lt) (rt))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> z)
  **  (store_term y lt )
  **  (store_term z rt )
).

Definition subst_term_which_implies_wit_6 :=
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 3)) (PreH2 : (t <> 0)),
  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  (store_term' t trm_implementation )
|--
  EX (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermQuant (qt) (qvar) (qterm))) ”
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm_implementation)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
) \/
(
forall (trm_implementation: term) (t: Z) (PreH1 : ((termtypeID (trm_implementation)) = 3)) (PreH2 : (t <> 0)),
  (store_term' t trm_implementation )
|--
  EX (z: Z) (y: Z) (qt: quant_type) (qvar: (@list Z)) (qterm: term),
  “ (t <> 0) ”
  &&  “ (trm_implementation = (TermQuant (qt) (qvar) (qterm))) ”
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
).

Module Type VC_Correct.

Include safeexec_Strategy_Correct.

Axiom proof_of_subst_var_safety_wit_1 : subst_var_safety_wit_1.
Axiom proof_of_subst_var_safety_wit_2 : subst_var_safety_wit_2.
Axiom proof_of_subst_var_safety_wit_3 : subst_var_safety_wit_3.
Axiom proof_of_subst_var_safety_wit_4 : subst_var_safety_wit_4.
Axiom proof_of_subst_var_safety_wit_5 : subst_var_safety_wit_5.
Axiom proof_of_subst_var_return_wit_1 : subst_var_return_wit_1.
Axiom proof_of_subst_var_return_wit_2 : subst_var_return_wit_2.
Axiom proof_of_subst_var_return_wit_3 : subst_var_return_wit_3.
Axiom proof_of_subst_var_return_wit_4 : subst_var_return_wit_4.
Axiom proof_of_subst_var_return_wit_5 : subst_var_return_wit_5.
Axiom proof_of_subst_var_return_wit_6 : subst_var_return_wit_6.
Axiom proof_of_subst_var_partial_solve_wit_1 : subst_var_partial_solve_wit_1.
Axiom proof_of_subst_var_partial_solve_wit_2_pure : subst_var_partial_solve_wit_2_pure.
Axiom proof_of_subst_var_partial_solve_wit_2 : subst_var_partial_solve_wit_2.
Axiom proof_of_subst_var_partial_solve_wit_3 : subst_var_partial_solve_wit_3.
Axiom proof_of_subst_var_partial_solve_wit_4_pure : subst_var_partial_solve_wit_4_pure.
Axiom proof_of_subst_var_partial_solve_wit_4 : subst_var_partial_solve_wit_4.
Axiom proof_of_subst_var_partial_solve_wit_5 : subst_var_partial_solve_wit_5.
Axiom proof_of_subst_var_partial_solve_wit_6_pure : subst_var_partial_solve_wit_6_pure.
Axiom proof_of_subst_var_partial_solve_wit_6 : subst_var_partial_solve_wit_6.
Axiom proof_of_subst_var_partial_solve_wit_7_pure : subst_var_partial_solve_wit_7_pure.
Axiom proof_of_subst_var_partial_solve_wit_7 : subst_var_partial_solve_wit_7.
Axiom proof_of_subst_var_partial_solve_wit_8_pure : subst_var_partial_solve_wit_8_pure.
Axiom proof_of_subst_var_partial_solve_wit_8 : subst_var_partial_solve_wit_8.
Axiom proof_of_subst_var_partial_solve_wit_9_pure : subst_var_partial_solve_wit_9_pure.
Axiom proof_of_subst_var_partial_solve_wit_9 : subst_var_partial_solve_wit_9.
Axiom proof_of_subst_var_partial_solve_wit_10_pure : subst_var_partial_solve_wit_10_pure.
Axiom proof_of_subst_var_partial_solve_wit_10 : subst_var_partial_solve_wit_10.
Axiom proof_of_subst_var_partial_solve_wit_11 : subst_var_partial_solve_wit_11.
Axiom proof_of_subst_var_partial_solve_wit_12_pure : subst_var_partial_solve_wit_12_pure.
Axiom proof_of_subst_var_partial_solve_wit_12 : subst_var_partial_solve_wit_12.
Axiom proof_of_subst_var_which_implies_wit_1 : subst_var_which_implies_wit_1.
Axiom proof_of_subst_var_which_implies_wit_2 : subst_var_which_implies_wit_2.
Axiom proof_of_subst_var_which_implies_wit_3 : subst_var_which_implies_wit_3.
Axiom proof_of_subst_var_which_implies_wit_4 : subst_var_which_implies_wit_4.
Axiom proof_of_subst_var_which_implies_wit_5 : subst_var_which_implies_wit_5.
Axiom proof_of_subst_term_safety_wit_1 : subst_term_safety_wit_1.
Axiom proof_of_subst_term_safety_wit_2 : subst_term_safety_wit_2.
Axiom proof_of_subst_term_safety_wit_3 : subst_term_safety_wit_3.
Axiom proof_of_subst_term_safety_wit_4 : subst_term_safety_wit_4.
Axiom proof_of_subst_term_safety_wit_5 : subst_term_safety_wit_5.
Axiom proof_of_subst_term_return_wit_1 : subst_term_return_wit_1.
Axiom proof_of_subst_term_return_wit_2 : subst_term_return_wit_2.
Axiom proof_of_subst_term_return_wit_3 : subst_term_return_wit_3.
Axiom proof_of_subst_term_return_wit_4 : subst_term_return_wit_4.
Axiom proof_of_subst_term_return_wit_5 : subst_term_return_wit_5.
Axiom proof_of_subst_term_return_wit_6 : subst_term_return_wit_6.
Axiom proof_of_subst_term_partial_solve_wit_1 : subst_term_partial_solve_wit_1.
Axiom proof_of_subst_term_partial_solve_wit_2_pure : subst_term_partial_solve_wit_2_pure.
Axiom proof_of_subst_term_partial_solve_wit_2 : subst_term_partial_solve_wit_2.
Axiom proof_of_subst_term_partial_solve_wit_3 : subst_term_partial_solve_wit_3.
Axiom proof_of_subst_term_partial_solve_wit_4_pure : subst_term_partial_solve_wit_4_pure.
Axiom proof_of_subst_term_partial_solve_wit_4 : subst_term_partial_solve_wit_4.
Axiom proof_of_subst_term_partial_solve_wit_5 : subst_term_partial_solve_wit_5.
Axiom proof_of_subst_term_partial_solve_wit_6 : subst_term_partial_solve_wit_6.
Axiom proof_of_subst_term_partial_solve_wit_7_pure : subst_term_partial_solve_wit_7_pure.
Axiom proof_of_subst_term_partial_solve_wit_7 : subst_term_partial_solve_wit_7.
Axiom proof_of_subst_term_partial_solve_wit_8_pure : subst_term_partial_solve_wit_8_pure.
Axiom proof_of_subst_term_partial_solve_wit_8 : subst_term_partial_solve_wit_8.
Axiom proof_of_subst_term_partial_solve_wit_9_pure : subst_term_partial_solve_wit_9_pure.
Axiom proof_of_subst_term_partial_solve_wit_9 : subst_term_partial_solve_wit_9.
Axiom proof_of_subst_term_partial_solve_wit_10_pure : subst_term_partial_solve_wit_10_pure.
Axiom proof_of_subst_term_partial_solve_wit_10 : subst_term_partial_solve_wit_10.
Axiom proof_of_subst_term_partial_solve_wit_11_pure : subst_term_partial_solve_wit_11_pure.
Axiom proof_of_subst_term_partial_solve_wit_11 : subst_term_partial_solve_wit_11.
Axiom proof_of_subst_term_partial_solve_wit_12 : subst_term_partial_solve_wit_12.
Axiom proof_of_subst_term_partial_solve_wit_13_pure : subst_term_partial_solve_wit_13_pure.
Axiom proof_of_subst_term_partial_solve_wit_13 : subst_term_partial_solve_wit_13.
Axiom proof_of_subst_term_which_implies_wit_1 : subst_term_which_implies_wit_1.
Axiom proof_of_subst_term_which_implies_wit_2 : subst_term_which_implies_wit_2.
Axiom proof_of_subst_term_which_implies_wit_3 : subst_term_which_implies_wit_3.
Axiom proof_of_subst_term_which_implies_wit_4 : subst_term_which_implies_wit_4.
Axiom proof_of_subst_term_which_implies_wit_5 : subst_term_which_implies_wit_5.
Axiom proof_of_subst_term_which_implies_wit_6 : subst_term_which_implies_wit_6.

End VC_Correct.
