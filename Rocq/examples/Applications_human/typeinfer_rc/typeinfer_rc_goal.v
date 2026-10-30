From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc.
Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.typeinfer_rc Require Import typeinfer_rc_strategy_goal.
From SimpleC.EE.Applications_human.typeinfer_rc Require Import typeinfer_rc_strategy_proof.

(*----- Function copy_atype -----*)

Definition copy_atype_safety_wit_1_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (rc_valid M_nonnull )) (PreH3 : (0 < (rc_count (M_nonnull) (t_pre)))) (PreH4 : ((rc_count (M_nonnull) (t_pre)) < INT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_nonnull )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition copy_atype_safety_wit_2_null :=
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (rc_valid M_null )),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_null )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition copy_atype_safety_wit_3_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (rc_valid M_nonnull )) (PreH4 : (0 < (rc_count (M_nonnull) (t_pre)))) (PreH5 : ((rc_count (M_nonnull) (t_pre)) < INT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_nonnull )
|--
  “ False ”
.

Definition copy_atype_safety_wit_4_null :=
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_null )
|--
  “ False ”
.

Definition copy_atype_safety_wit_5_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : (0 < (rc_count (M_nonnull) (t_pre)))) (PreH6 : ((rc_count (M_nonnull) (t_pre)) < INT_MAX)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (((rc_count (M_nonnull) (t_pre)) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((rc_count (M_nonnull) (t_pre)) + 1 )) ”
.

Definition copy_atype_safety_wit_6_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : (0 < (rc_count (M_nonnull) (t_pre)))) (PreH6 : ((rc_count (M_nonnull) (t_pre)) < INT_MAX)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition copy_atype_return_wit_1_nonnull :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : (0 < (rc_count (M_nonnull) (t_pre)))) (PreH6 : ((rc_count (M_nonnull) (t_pre)) < INT_MAX)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) + 1 ))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
|--
  EX (M_post: RcState),
  “ (t_pre = t_pre) ”
  &&  “ (retain_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_nonnull M_post ) ”
  &&  (store_world M_post )
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) + 1 ) <= INT_MAX)) (PreH2 : (((rc_count (M_nonnull) (t_pre)) + 1 ) >= INT_MIN)) (PreH3 : (node_at M_nonnull t_pre n )) (PreH4 : (t_pre <> 0)) (PreH5 : (t_pre <> 0)) (PreH6 : (rc_valid M_nonnull )) (PreH7 : (0 < (rc_count (M_nonnull) (t_pre)))) (PreH8 : ((rc_count (M_nonnull) (t_pre)) < INT_MAX)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) + 1 ))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
|--
  EX (M_post: RcState),
  “ (retain_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_nonnull M_post ) ”
  &&  (store_world M_post )
).

Definition copy_atype_return_wit_2_null :=
(
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  (store_world M_null )
|--
  EX (M_post: RcState),
  “ (t_pre = t_pre) ”
  &&  “ (retain_rel M_null t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_null M_post ) ”
  &&  (store_world M_post )
) \/
(
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  TT && emp 
|--
  “ (rc_preserves M_null M_null ) ”
  &&  “ (retain_rel M_null 0 M_null ) ”
  &&  emp
).

Definition copy_atype_return_wit_2_null_split_goal_1 :=
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  (rc_preserves M_null M_null )
.

Definition copy_atype_return_wit_2_null_split_goal_2 :=
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  (retain_rel M_null 0 M_null )
.

Definition copy_atype_partial_solve_wit_1_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (rc_valid M_nonnull )) (PreH4 : (0 < (rc_count (M_nonnull) (t_pre)))) (PreH5 : ((rc_count (M_nonnull) (t_pre)) < INT_MAX)),
  (store_world M_nonnull )
|--
  EX (n: TypeNode),
  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ (0 < (rc_count (M_nonnull) (t_pre))) ”
  &&  “ ((rc_count (M_nonnull) (t_pre)) < INT_MAX) ”
  &&  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
.

(*----- Function free_atype -----*)

Definition free_atype_safety_wit_1_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (rc_valid M_nonnull )) (PreH3 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_nonnull )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_atype_safety_wit_2_null :=
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (rc_valid M_null )),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_null )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_atype_safety_wit_3_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (rc_valid M_nonnull )) (PreH4 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_nonnull )
|--
  “ False ”
.

Definition free_atype_safety_wit_4_null :=
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_world M_null )
|--
  “ False ”
.

Definition free_atype_safety_wit_5_nonnull :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((rc_count (M_nonnull) (t_pre)) - 1 )) ”
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((rc_count (M_nonnull) (t_pre)) - 1 )) ”
).

Definition free_atype_safety_wit_5_nonnull_split_goal_1 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX) ”
.

Definition free_atype_safety_wit_5_nonnull_split_goal_2 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ ((INT_MIN) <= ((rc_count (M_nonnull) (t_pre)) - 1 )) ”
.

Definition free_atype_safety_wit_6_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition free_atype_safety_wit_7_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (node_at M_nonnull t_pre n )) (PreH2 : (t_pre <> 0)) (PreH3 : (t_pre <> 0)) (PreH4 : (rc_valid M_nonnull )) (PreH5 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition free_atype_safety_wit_8_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH2 : (node_at M_nonnull t_pre n )) (PreH3 : (t_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (rc_valid M_nonnull )) (PreH6 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition free_atype_safety_wit_9_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 1)) (PreH2 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH3 : (node_at M_nonnull t_pre n )) (PreH4 : (t_pre <> 0)) (PreH5 : (t_pre <> 0)) (PreH6 : (rc_valid M_nonnull )) (PreH7 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition free_atype_entail_wit_1_1_nonnull :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n_2: TypeNode) (M_post_2: RcState) (M_post_3: RcState) (PreH1 : (release_rel M_post_2 (node_b (n_2)) M_post_3 )) (PreH2 : (rc_valid M_post_3 )) (PreH3 : (release_rel (rc_delete (M_nonnull) (t_pre) (n_2)) (node_a (n_2)) M_post_2 )) (PreH4 : (rc_valid M_post_2 )) (PreH5 : ((node_tag (n_2)) = 1)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n_2)) )) (PreH7 : ((node_tag (n_2)) = 1)) (PreH8 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH9 : (node_at M_nonnull t_pre n_2 )) (PreH10 : (t_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (rc_valid M_nonnull )) (PreH13 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post_3 )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  EX (n: TypeNode) (M_post: RcState),
  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> 0)
  **  (store_node_payload t_pre n )
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n_2: TypeNode) (M_post_2: RcState) (M_post_3: RcState) (PreH1 : ((node_tag (n_2)) <= INT_MAX)) (PreH2 : ((node_tag (n_2)) >= INT_MIN)) (PreH3 : (release_rel M_post_2 (node_b (n_2)) M_post_3 )) (PreH4 : (rc_valid M_post_3 )) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n_2)) (node_a (n_2)) M_post_2 )) (PreH6 : (rc_valid M_post_2 )) (PreH7 : ((node_tag (n_2)) = 1)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n_2)) )) (PreH9 : ((node_tag (n_2)) = 1)) (PreH10 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH11 : (node_at M_nonnull t_pre n_2 )) (PreH12 : (t_pre <> 0)) (PreH13 : (t_pre <> 0)) (PreH14 : (rc_valid M_nonnull )) (PreH15 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post_3 )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
|--
  EX (n: TypeNode) (M_post: RcState),
  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
  **  (store_node_payload t_pre n )
).

Definition free_atype_entail_wit_1_2_nonnull :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n_2: TypeNode) (M_post_2: RcState) (M_post_3: RcState) (PreH1 : (release_rel M_post_2 (node_b (n_2)) M_post_3 )) (PreH2 : (rc_valid M_post_3 )) (PreH3 : (release_rel (rc_delete (M_nonnull) (t_pre) (n_2)) (node_a (n_2)) M_post_2 )) (PreH4 : (rc_valid M_post_2 )) (PreH5 : ((node_tag (n_2)) = 2)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n_2)) )) (PreH7 : ((node_tag (n_2)) = 2)) (PreH8 : ((node_tag (n_2)) <> 1)) (PreH9 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH10 : (node_at M_nonnull t_pre n_2 )) (PreH11 : (t_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (rc_valid M_nonnull )) (PreH14 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post_3 )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  EX (n: TypeNode) (M_post: RcState),
  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> 0)
  **  (store_node_payload t_pre n )
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n_2: TypeNode) (M_post_2: RcState) (M_post_3: RcState) (PreH1 : ((node_tag (n_2)) <= INT_MAX)) (PreH2 : ((node_tag (n_2)) >= INT_MIN)) (PreH3 : (release_rel M_post_2 (node_b (n_2)) M_post_3 )) (PreH4 : (rc_valid M_post_3 )) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n_2)) (node_a (n_2)) M_post_2 )) (PreH6 : (rc_valid M_post_2 )) (PreH7 : ((node_tag (n_2)) = 2)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n_2)) )) (PreH9 : ((node_tag (n_2)) = 2)) (PreH10 : ((node_tag (n_2)) <> 1)) (PreH11 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH12 : (node_at M_nonnull t_pre n_2 )) (PreH13 : (t_pre <> 0)) (PreH14 : (t_pre <> 0)) (PreH15 : (rc_valid M_nonnull )) (PreH16 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post_3 )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n_2)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
|--
  EX (n: TypeNode) (M_post: RcState),
  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
  **  (store_node_payload t_pre n )
).

Definition free_atype_entail_wit_1_3_nonnull :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n_2: TypeNode) (PreH1 : ((node_tag (n_2)) <> 2)) (PreH2 : ((node_tag (n_2)) <> 1)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH4 : (node_at M_nonnull t_pre n_2 )) (PreH5 : (t_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (rc_valid M_nonnull )) (PreH8 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  EX (n: TypeNode) (M_post: RcState),
  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> 0)
  **  (store_node_payload t_pre n )
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n_2: TypeNode) (PreH1 : ((node_tag (n_2)) <> 2)) (PreH2 : ((node_tag (n_2)) <> 1)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH4 : (node_at M_nonnull t_pre n_2 )) (PreH5 : (t_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (rc_valid M_nonnull )) (PreH8 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
|--
  EX (n: TypeNode) (M_post: RcState),
  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
  **  (store_node_payload t_pre n )
).

Definition free_atype_return_wit_1_null :=
(
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  (store_world M_null )
|--
  EX (M_post: RcState),
  “ (release_rel M_null t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
) \/
(
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  TT && emp 
|--
  “ (release_rel M_null 0 M_null ) ”
  &&  emp
).

Definition free_atype_return_wit_1_null_split_goal_1 :=
forall (M_null: RcState) (t_pre: Z) (PreH1 : (t_pre = 0)) (PreH2 : (t_pre = 0)) (PreH3 : (rc_valid M_null )),
  (release_rel M_null 0 M_null )
.

Definition free_atype_return_wit_2_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (M_post_2: RcState) (PreH1 : (release_rel M_nonnull t_pre M_post_2 )) (PreH2 : (rc_valid M_post_2 )),
  (store_world M_post_2 )
|--
  EX (M_post: RcState),
  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
.

Definition free_atype_return_wit_3_nonnull :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <> 0)) (PreH2 : (node_at M_nonnull t_pre n )) (PreH3 : (t_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (rc_valid M_nonnull )) (PreH6 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
|--
  EX (M_post: RcState),
  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <> 0)) (PreH4 : (node_at M_nonnull t_pre n )) (PreH5 : (t_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (rc_valid M_nonnull )) (PreH8 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
|--
  EX (M_post: RcState),
  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  (store_world M_post )
).

Definition free_atype_partial_solve_wit_1_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (PreH1 : (t_pre <> 0)) (PreH2 : (t_pre <> 0)) (PreH3 : (rc_valid M_nonnull )) (PreH4 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_nonnull )
|--
  EX (n: TypeNode),
  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> (rc_count (M_nonnull) (t_pre)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
.

Definition free_atype_partial_solve_wit_2_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH2 : (node_at M_nonnull t_pre n )) (PreH3 : (t_pre <> 0)) (PreH4 : (t_pre <> 0)) (PreH5 : (rc_valid M_nonnull )) (PreH6 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))) )
|--
  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
.

Definition free_atype_partial_solve_wit_3_nonnull_pure :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 1)) (PreH2 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH3 : (node_at M_nonnull t_pre n )) (PreH4 : (t_pre <> 0)) (PreH5 : (t_pre <> 0)) (PreH6 : (rc_valid M_nonnull )) (PreH7 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (rc_valid M_nonnull ) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 1)) (PreH6 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH7 : (node_at M_nonnull t_pre n )) (PreH8 : (t_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (rc_valid M_nonnull )) (PreH11 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
).

Definition free_atype_partial_solve_wit_3_nonnull_pure_split_goal_1 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 1)) (PreH6 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH7 : (node_at M_nonnull t_pre n )) (PreH8 : (t_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (rc_valid M_nonnull )) (PreH11 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
.

Definition free_atype_partial_solve_wit_3_nonnull_aux :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 1)) (PreH2 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH3 : (node_at M_nonnull t_pre n )) (PreH4 : (t_pre <> 0)) (PreH5 : (t_pre <> 0)) (PreH6 : (rc_valid M_nonnull )) (PreH7 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid M_nonnull ) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
.

Definition free_atype_partial_solve_wit_3_nonnull := free_atype_partial_solve_wit_3_nonnull_pure -> free_atype_partial_solve_wit_3_nonnull_aux.

Definition free_atype_partial_solve_wit_4_nonnull_pure :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 1)) (PreH2 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH3 : ((node_tag (n)) = 1)) (PreH4 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH5 : (node_at M_nonnull t_pre n )) (PreH6 : (t_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (rc_valid M_nonnull )) (PreH9 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
  &&  “ ((node_a (n)) <> 0) ”
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 1)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH9 : (node_at M_nonnull t_pre n )) (PreH10 : (t_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (rc_valid M_nonnull )) (PreH13 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_a (n)) <> 0) ”
  &&  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
).

Definition free_atype_partial_solve_wit_4_nonnull_pure_split_goal_1 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 1)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH9 : (node_at M_nonnull t_pre n )) (PreH10 : (t_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (rc_valid M_nonnull )) (PreH13 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_a (n)) <> 0) ”
.

Definition free_atype_partial_solve_wit_4_nonnull_pure_split_goal_2 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 1)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH9 : (node_at M_nonnull t_pre n )) (PreH10 : (t_pre <> 0)) (PreH11 : (t_pre <> 0)) (PreH12 : (rc_valid M_nonnull )) (PreH13 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
.

Definition free_atype_partial_solve_wit_4_nonnull_aux :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 1)) (PreH2 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH3 : ((node_tag (n)) = 1)) (PreH4 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH5 : (node_at M_nonnull t_pre n )) (PreH6 : (t_pre <> 0)) (PreH7 : (t_pre <> 0)) (PreH8 : (rc_valid M_nonnull )) (PreH9 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
  &&  “ ((node_a (n)) <> 0) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
.

Definition free_atype_partial_solve_wit_4_nonnull := free_atype_partial_solve_wit_4_nonnull_pure -> free_atype_partial_solve_wit_4_nonnull_aux.

Definition free_atype_partial_solve_wit_5_nonnull_pure :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH2 : (rc_valid M_post )) (PreH3 : ((node_tag (n)) = 1)) (PreH4 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH5 : ((node_tag (n)) = 1)) (PreH6 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH7 : (node_at M_nonnull t_pre n )) (PreH8 : (t_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (rc_valid M_nonnull )) (PreH11 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
  &&  “ ((node_b (n)) <> 0) ”
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH6 : (rc_valid M_post )) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH9 : ((node_tag (n)) = 1)) (PreH10 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH11 : (node_at M_nonnull t_pre n )) (PreH12 : (t_pre <> 0)) (PreH13 : (t_pre <> 0)) (PreH14 : (rc_valid M_nonnull )) (PreH15 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_b (n)) <> 0) ”
  &&  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
).

Definition free_atype_partial_solve_wit_5_nonnull_pure_split_goal_1 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH6 : (rc_valid M_post )) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH9 : ((node_tag (n)) = 1)) (PreH10 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH11 : (node_at M_nonnull t_pre n )) (PreH12 : (t_pre <> 0)) (PreH13 : (t_pre <> 0)) (PreH14 : (rc_valid M_nonnull )) (PreH15 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_b (n)) <> 0) ”
.

Definition free_atype_partial_solve_wit_5_nonnull_pure_split_goal_2 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH6 : (rc_valid M_post )) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH9 : ((node_tag (n)) = 1)) (PreH10 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH11 : (node_at M_nonnull t_pre n )) (PreH12 : (t_pre <> 0)) (PreH13 : (t_pre <> 0)) (PreH14 : (rc_valid M_nonnull )) (PreH15 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
.

Definition free_atype_partial_solve_wit_5_nonnull_aux :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH2 : (rc_valid M_post )) (PreH3 : ((node_tag (n)) = 1)) (PreH4 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH5 : ((node_tag (n)) = 1)) (PreH6 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH7 : (node_at M_nonnull t_pre n )) (PreH8 : (t_pre <> 0)) (PreH9 : (t_pre <> 0)) (PreH10 : (rc_valid M_nonnull )) (PreH11 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
  &&  “ ((node_b (n)) <> 0) ”
  &&  “ (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
.

Definition free_atype_partial_solve_wit_5_nonnull := free_atype_partial_solve_wit_5_nonnull_pure -> free_atype_partial_solve_wit_5_nonnull_aux.

Definition free_atype_partial_solve_wit_6_nonnull_pure :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 2)) (PreH2 : ((node_tag (n)) <> 1)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH4 : (node_at M_nonnull t_pre n )) (PreH5 : (t_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (rc_valid M_nonnull )) (PreH8 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ (rc_valid M_nonnull ) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 2)) (PreH6 : ((node_tag (n)) <> 1)) (PreH7 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH8 : (node_at M_nonnull t_pre n )) (PreH9 : (t_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (rc_valid M_nonnull )) (PreH12 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
).

Definition free_atype_partial_solve_wit_6_nonnull_pure_split_goal_1 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 2)) (PreH6 : ((node_tag (n)) <> 1)) (PreH7 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH8 : (node_at M_nonnull t_pre n )) (PreH9 : (t_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (rc_valid M_nonnull )) (PreH12 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
|--
  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
.

Definition free_atype_partial_solve_wit_6_nonnull_aux :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 2)) (PreH2 : ((node_tag (n)) <> 1)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH4 : (node_at M_nonnull t_pre n )) (PreH5 : (t_pre <> 0)) (PreH6 : (t_pre <> 0)) (PreH7 : (rc_valid M_nonnull )) (PreH8 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid M_nonnull ) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((rc_count (M_nonnull) (t_pre)) = 1) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  (store_world_missing M_nonnull (cons ((field_key (t_pre) (Tag))) ((cons ((field_key (t_pre) (RefCount))) ((@nil TypeFieldKey))))) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
.

Definition free_atype_partial_solve_wit_6_nonnull := free_atype_partial_solve_wit_6_nonnull_pure -> free_atype_partial_solve_wit_6_nonnull_aux.

Definition free_atype_partial_solve_wit_7_nonnull_pure :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 2)) (PreH2 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH3 : ((node_tag (n)) = 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH6 : (node_at M_nonnull t_pre n )) (PreH7 : (t_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (rc_valid M_nonnull )) (PreH10 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
  &&  “ ((node_a (n)) <> 0) ”
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 2)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : ((node_tag (n)) <> 1)) (PreH9 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH10 : (node_at M_nonnull t_pre n )) (PreH11 : (t_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (rc_valid M_nonnull )) (PreH14 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_a (n)) <> 0) ”
  &&  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
).

Definition free_atype_partial_solve_wit_7_nonnull_pure_split_goal_1 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 2)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : ((node_tag (n)) <> 1)) (PreH9 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH10 : (node_at M_nonnull t_pre n )) (PreH11 : (t_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (rc_valid M_nonnull )) (PreH14 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_a (n)) <> 0) ”
.

Definition free_atype_partial_solve_wit_7_nonnull_pure_split_goal_2 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : ((node_tag (n)) = 2)) (PreH6 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : ((node_tag (n)) <> 1)) (PreH9 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH10 : (node_at M_nonnull t_pre n )) (PreH11 : (t_pre <> 0)) (PreH12 : (t_pre <> 0)) (PreH13 : (rc_valid M_nonnull )) (PreH14 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
.

Definition free_atype_partial_solve_wit_7_nonnull_aux :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 2)) (PreH2 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH3 : ((node_tag (n)) = 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH6 : (node_at M_nonnull t_pre n )) (PreH7 : (t_pre <> 0)) (PreH8 : (t_pre <> 0)) (PreH9 : (rc_valid M_nonnull )) (PreH10 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((rc_reserved ((rc_delete (M_nonnull) (t_pre) (n))) ((node_a (n)))) > 0) ”
  &&  “ ((node_a (n)) <> 0) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  (store_world (rc_delete (M_nonnull) (t_pre) (n)) )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
.

Definition free_atype_partial_solve_wit_7_nonnull := free_atype_partial_solve_wit_7_nonnull_pure -> free_atype_partial_solve_wit_7_nonnull_aux.

Definition free_atype_partial_solve_wit_8_nonnull_pure :=
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH2 : (rc_valid M_post )) (PreH3 : ((node_tag (n)) = 2)) (PreH4 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH5 : ((node_tag (n)) = 2)) (PreH6 : ((node_tag (n)) <> 1)) (PreH7 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH8 : (node_at M_nonnull t_pre n )) (PreH9 : (t_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (rc_valid M_nonnull )) (PreH12 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
  &&  “ ((node_b (n)) <> 0) ”
) \/
(
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH6 : (rc_valid M_post )) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH9 : ((node_tag (n)) = 2)) (PreH10 : ((node_tag (n)) <> 1)) (PreH11 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH12 : (node_at M_nonnull t_pre n )) (PreH13 : (t_pre <> 0)) (PreH14 : (t_pre <> 0)) (PreH15 : (rc_valid M_nonnull )) (PreH16 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_b (n)) <> 0) ”
  &&  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
).

Definition free_atype_partial_solve_wit_8_nonnull_pure_split_goal_1 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH6 : (rc_valid M_post )) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH9 : ((node_tag (n)) = 2)) (PreH10 : ((node_tag (n)) <> 1)) (PreH11 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH12 : (node_at M_nonnull t_pre n )) (PreH13 : (t_pre <> 0)) (PreH14 : (t_pre <> 0)) (PreH15 : (rc_valid M_nonnull )) (PreH16 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((node_b (n)) <> 0) ”
.

Definition free_atype_partial_solve_wit_8_nonnull_pure_split_goal_2 :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (((rc_count (M_nonnull) (t_pre)) - 1 ) <= INT_MAX)) (PreH2 : ((node_tag (n)) <= INT_MAX)) (PreH3 : (((rc_count (M_nonnull) (t_pre)) - 1 ) >= INT_MIN)) (PreH4 : ((node_tag (n)) >= INT_MIN)) (PreH5 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH6 : (rc_valid M_post )) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH9 : ((node_tag (n)) = 2)) (PreH10 : ((node_tag (n)) <> 1)) (PreH11 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH12 : (node_at M_nonnull t_pre n )) (PreH13 : (t_pre <> 0)) (PreH14 : (t_pre <> 0)) (PreH15 : (rc_valid M_nonnull )) (PreH16 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
.

Definition free_atype_partial_solve_wit_8_nonnull_aux :=
forall (M_nonnull: RcState) (t_pre: Z) (n: TypeNode) (M_post: RcState) (PreH1 : (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post )) (PreH2 : (rc_valid M_post )) (PreH3 : ((node_tag (n)) = 2)) (PreH4 : (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) )) (PreH5 : ((node_tag (n)) = 2)) (PreH6 : ((node_tag (n)) <> 1)) (PreH7 : (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0)) (PreH8 : (node_at M_nonnull t_pre n )) (PreH9 : (t_pre <> 0)) (PreH10 : (t_pre <> 0)) (PreH11 : (rc_valid M_nonnull )) (PreH12 : ((rc_reserved (M_nonnull) (t_pre)) > 0)),
  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) ((node_b (n)))) > 0) ”
  &&  “ ((node_b (n)) <> 0) ”
  &&  “ (release_rel (rc_delete (M_nonnull) (t_pre) (n)) (node_a (n)) M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ (rc_valid (rc_delete (M_nonnull) (t_pre) (n)) ) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ (((rc_count (M_nonnull) (t_pre)) - 1 ) = 0) ”
  &&  “ (node_at M_nonnull t_pre n ) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ ((rc_reserved (M_nonnull) (t_pre)) > 0) ”
  &&  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> ((rc_count (M_nonnull) (t_pre)) - 1 ))
.

Definition free_atype_partial_solve_wit_8_nonnull := free_atype_partial_solve_wit_8_nonnull_pure -> free_atype_partial_solve_wit_8_nonnull_aux.

Definition free_atype_partial_solve_wit_9_nonnull :=
forall (M_nonnull: RcState) (t_pre: Z) (M_post: RcState) (n: TypeNode) (PreH1 : (release_rel M_nonnull t_pre M_post )) (PreH2 : (rc_valid M_post )),
  (store_world M_post )
  **  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> 0)
  **  (store_node_payload t_pre n )
|--
  “ (release_rel M_nonnull t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  ((&((t_pre)  # "atype" ->ₛ "refcnt")) # Int  |-> 0)
  **  (store_node_payload t_pre n )
  **  (store_world M_post )
.

Definition free_atype_which_implies_wit_1 :=
(
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 1)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))) )
|--
  “ ((node_tag (n)) = 1) ”
  &&  “ (rc_valid (rc_delete (M_nonnull) (t) (n)) ) ”
  &&  ((&((t)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t) (n)) )
) \/
(
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 1)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Payload1))) ((cons ((field_key (t) (Payload0))) ((cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))))))) )
|--
  “ (rc_valid (rc_delete (M_nonnull) (t) (n)) ) ”
  &&  (store_world (rc_delete (M_nonnull) (t) (n)) )
).

Definition free_atype_which_implies_wit_1_split_goal_1 :=
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 1)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Payload1))) ((cons ((field_key (t) (Payload0))) ((cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))))))) )
|--
  “ (rc_valid (rc_delete (M_nonnull) (t) (n)) ) ”
.

Definition free_atype_which_implies_wit_1_split_goal_spatial :=
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 1)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Payload1))) ((cons ((field_key (t) (Payload0))) ((cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))))))) )
|--
  (store_world (rc_delete (M_nonnull) (t) (n)) )
.

Definition free_atype_which_implies_wit_2 :=
(
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 2)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))) )
|--
  “ ((node_tag (n)) = 2) ”
  &&  “ (rc_valid (rc_delete (M_nonnull) (t) (n)) ) ”
  &&  ((&((t)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world (rc_delete (M_nonnull) (t) (n)) )
) \/
(
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 2)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Payload1))) ((cons ((field_key (t) (Payload0))) ((cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))))))) )
|--
  “ (rc_valid (rc_delete (M_nonnull) (t) (n)) ) ”
  &&  (store_world (rc_delete (M_nonnull) (t) (n)) )
).

Definition free_atype_which_implies_wit_2_split_goal_1 :=
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 2)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Payload1))) ((cons ((field_key (t) (Payload0))) ((cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))))))) )
|--
  “ (rc_valid (rc_delete (M_nonnull) (t) (n)) ) ”
.

Definition free_atype_which_implies_wit_2_split_goal_spatial :=
forall (M_nonnull: RcState) (n: TypeNode) (t: Z) (PreH1 : (rc_valid M_nonnull )) (PreH2 : (node_at M_nonnull t n )) (PreH3 : ((rc_count (M_nonnull) (t)) = 1)) (PreH4 : ((rc_reserved (M_nonnull) (t)) > 0)) (PreH5 : ((node_tag (n)) = 2)),
  (store_world_missing M_nonnull (cons ((field_key (t) (Payload1))) ((cons ((field_key (t) (Payload0))) ((cons ((field_key (t) (Tag))) ((cons ((field_key (t) (RefCount))) ((@nil TypeFieldKey))))))))) )
|--
  (store_world (rc_delete (M_nonnull) (t) (n)) )
.

(*----- Function atype_unify -----*)

Definition atype_unify_safety_wit_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= 3)) (PreH2 : (0 <= (node_tag (n)))) (PreH3 : (node_at M_verify t1_pre n )) (PreH4 : (rc_valid M_verify )) (PreH5 : (store_type M_verify t1_pre tr1_verify )) (PreH6 : (store_type M_verify t2_pre tr2_verify )) (PreH7 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify_safety_wit_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s_verify (node_a (n)) tr )) (PreH3 : (store_type M_verify retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr1_verify = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH17 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify_safety_wit_3 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1_verify = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M_verify t1_pre n )) (PreH12 : (rc_valid M_verify )) (PreH13 : (store_type M_verify t1_pre tr1_verify )) (PreH14 : (store_type M_verify t2_pre tr2_verify )) (PreH15 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH16 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify_entail_wit_1_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr_2: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s_verify (node_a (n)) tr_2 )) (PreH3 : (store_type M_verify retval tr_2 )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr1_verify = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH17 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (retval = 0) ”
  &&  “ forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr )) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval = 0) ”
  &&  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify_entail_wit_1_2 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1_verify = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M_verify t1_pre n )) (PreH12 : (rc_valid M_verify )) (PreH13 : (store_type M_verify t1_pre tr1_verify )) (PreH14 : (store_type M_verify t2_pre tr2_verify )) (PreH15 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH16 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (retval = 0) ”
  &&  “ forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr )) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval = 0) ”
  &&  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1_verify = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M_verify t1_pre n )) (PreH12 : (rc_valid M_verify )) (PreH13 : (store_type M_verify t1_pre tr1_verify )) (PreH14 : (store_type M_verify t2_pre tr2_verify )) (PreH15 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH16 : (retval = 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n))) (0)) = n) ”
  &&  emp
).

Definition atype_unify_entail_wit_1_2_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1_verify = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M_verify t1_pre n )) (PreH12 : (rc_valid M_verify )) (PreH13 : (store_type M_verify t1_pre tr1_verify )) (PreH14 : (store_type M_verify t2_pre tr2_verify )) (PreH15 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH16 : (retval = 0)),
  ((Node (3) ((node_a (n))) (0)) = n)
.

Definition atype_unify_entail_wit_2_1 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s_verify (node_a (n)) tr )) (PreH3 : (store_type M_verify retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr1_verify = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH17 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (retval <> 0) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ (store_type M_verify retval tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval <> 0) ”
  &&  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s_verify (node_a (n)) tr )) (PreH3 : (store_type M_verify retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr1_verify = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH17 : (retval <> 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n))) (0)) = n) ”
  &&  emp
).

Definition atype_unify_entail_wit_2_1_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s_verify (node_a (n)) tr )) (PreH3 : (store_type M_verify retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr1_verify = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH17 : (retval <> 0)),
  ((Node (3) ((node_a (n))) (0)) = n)
.

Definition atype_unify_entail_wit_2_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr_2: TypeTree), ~((solution_at s_verify (node_a (n)) tr_2 ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1_verify = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M_verify t1_pre n )) (PreH12 : (rc_valid M_verify )) (PreH13 : (store_type M_verify t1_pre tr1_verify )) (PreH14 : (store_type M_verify t2_pre tr2_verify )) (PreH15 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH16 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  EX (tr: TypeTree),
  “ (retval <> 0) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ (store_type M_verify retval tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval <> 0) ”
  &&  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify_return_wit_1 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2_verify )) (PreH3 : (store_type M_post_3 t1_pre tr1_verify )) (PreH4 : (retval = 0)) (PreH5 : (unify_rel tr1_verify tr2_verify s_verify s_post_3 )) (PreH6 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M_verify M_post_3 )) (PreH9 : (rc_reservations_same M_verify M_post_3 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M_verify t1_pre n )) (PreH14 : (rc_valid M_verify )) (PreH15 : (store_type M_verify t1_pre tr1_verify )) (PreH16 : (store_type M_verify t2_pre tr2_verify )) (PreH17 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1_verify tr2_verify s_verify s_post ) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_verify M_post ) ”
  &&  “ (rc_reservations_same M_verify M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2_verify )) (PreH3 : (store_type M_post_3 t1_pre tr1_verify )) (PreH4 : (retval = 0)) (PreH5 : (unify_rel tr1_verify tr2_verify s_verify s_post_3 )) (PreH6 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M_verify M_post_3 )) (PreH9 : (rc_reservations_same M_verify M_post_3 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M_verify t1_pre n )) (PreH14 : (rc_valid M_verify )) (PreH15 : (store_type M_verify t1_pre tr1_verify )) (PreH16 : (store_type M_verify t2_pre tr2_verify )) (PreH17 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  TT && emp 
|--
  “ (infer_result 0 M_verify s_verify t1_pre t2_pre 0 M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify_return_wit_1_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2_verify )) (PreH3 : (store_type M_post_3 t1_pre tr1_verify )) (PreH4 : (retval = 0)) (PreH5 : (unify_rel tr1_verify tr2_verify s_verify s_post_3 )) (PreH6 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M_verify M_post_3 )) (PreH9 : (rc_reservations_same M_verify M_post_3 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M_verify t1_pre n )) (PreH14 : (rc_valid M_verify )) (PreH15 : (store_type M_verify t1_pre tr1_verify )) (PreH16 : (store_type M_verify t2_pre tr2_verify )) (PreH17 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  (infer_result 0 M_verify s_verify t1_pre t2_pre 0 M_post_3 s_post_3 )
.

Definition atype_unify_return_wit_2 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2_verify )) (PreH3 : (store_type M_post_3 t1_pre tr1_verify )) (PreH4 : (retval <> 0)) (PreH5 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH6 : (rc_valid M_post_3 )) (PreH7 : (rc_preserves M_verify M_post_3 )) (PreH8 : (rc_reservations_same M_verify M_post_3 )) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_verify M_post_2 ) ”
  &&  “ (rc_reservations_same M_verify M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2_verify )) (PreH3 : (store_type M_post_3 t1_pre tr1_verify )) (PreH4 : (retval <> 0)) (PreH5 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH6 : (rc_valid M_post_3 )) (PreH7 : (rc_preserves M_verify M_post_3 )) (PreH8 : (rc_reservations_same M_verify M_post_3 )) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  TT && emp 
|--
  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify_return_wit_2_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2_verify )) (PreH3 : (store_type M_post_3 t1_pre tr1_verify )) (PreH4 : (retval <> 0)) (PreH5 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH6 : (rc_valid M_post_3 )) (PreH7 : (rc_preserves M_verify M_post_3 )) (PreH8 : (rc_reservations_same M_verify M_post_3 )) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )
.

Definition atype_unify_return_wit_3 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2_verify )) (PreH4 : (store_type M_post_3 t1_pre tr1_verify )) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_verify tr2_verify s_verify s_post_3 )) (PreH7 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH8 : (rc_valid M_post_3 )) (PreH9 : (rc_preserves M_verify M_post_3 )) (PreH10 : (rc_reservations_same M_verify M_post_3 )) (PreH11 : (retval_2 = 0)) (PreH12 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH13 : ((node_a (n)) < 100)) (PreH14 : (0 <= (node_a (n)))) (PreH15 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (n = (Node (3) ((node_a (n))) (0)))) (PreH17 : (tr1_verify = (TVar ((node_a (n)))))) (PreH18 : ((node_tag (n)) = 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M_verify t1_pre n )) (PreH22 : (rc_valid M_verify )) (PreH23 : (store_type M_verify t1_pre tr1_verify )) (PreH24 : (store_type M_verify t2_pre tr2_verify )) (PreH25 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH26 : (retval_2 = 0)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1_verify tr2_verify s_verify s_post ) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_verify M_post ) ”
  &&  “ (rc_reservations_same M_verify M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2_verify )) (PreH4 : (store_type M_post_3 t1_pre tr1_verify )) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_verify tr2_verify s_verify s_post_3 )) (PreH7 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH8 : (rc_valid M_post_3 )) (PreH9 : (rc_preserves M_verify M_post_3 )) (PreH10 : (rc_reservations_same M_verify M_post_3 )) (PreH11 : (retval_2 = 0)) (PreH12 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH13 : ((node_a (n)) < 100)) (PreH14 : (0 <= (node_a (n)))) (PreH15 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (n = (Node (3) ((node_a (n))) (0)))) (PreH17 : (tr1_verify = (TVar ((node_a (n)))))) (PreH18 : ((node_tag (n)) = 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M_verify t1_pre n )) (PreH22 : (rc_valid M_verify )) (PreH23 : (store_type M_verify t1_pre tr1_verify )) (PreH24 : (store_type M_verify t2_pre tr2_verify )) (PreH25 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH26 : (retval_2 = 0)),
  TT && emp 
|--
  “ (infer_result 0 M_verify s_verify t1_pre t2_pre 0 M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify_return_wit_3_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2_verify )) (PreH4 : (store_type M_post_3 t1_pre tr1_verify )) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_verify tr2_verify s_verify s_post_3 )) (PreH7 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH8 : (rc_valid M_post_3 )) (PreH9 : (rc_preserves M_verify M_post_3 )) (PreH10 : (rc_reservations_same M_verify M_post_3 )) (PreH11 : (retval_2 = 0)) (PreH12 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH13 : ((node_a (n)) < 100)) (PreH14 : (0 <= (node_a (n)))) (PreH15 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (n = (Node (3) ((node_a (n))) (0)))) (PreH17 : (tr1_verify = (TVar ((node_a (n)))))) (PreH18 : ((node_tag (n)) = 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M_verify t1_pre n )) (PreH22 : (rc_valid M_verify )) (PreH23 : (store_type M_verify t1_pre tr1_verify )) (PreH24 : (store_type M_verify t2_pre tr2_verify )) (PreH25 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH26 : (retval_2 = 0)),
  (infer_result 0 M_verify s_verify t1_pre t2_pre 0 M_post_3 s_post_3 )
.

Definition atype_unify_return_wit_4 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2_verify )) (PreH4 : (store_type M_post_3 t1_pre tr1_verify )) (PreH5 : (retval <> 0)) (PreH6 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M_verify M_post_3 )) (PreH9 : (rc_reservations_same M_verify M_post_3 )) (PreH10 : (retval_2 = 0)) (PreH11 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr1_verify = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M_verify t1_pre n )) (PreH21 : (rc_valid M_verify )) (PreH22 : (store_type M_verify t1_pre tr1_verify )) (PreH23 : (store_type M_verify t2_pre tr2_verify )) (PreH24 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH25 : (retval_2 = 0)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_verify M_post_2 ) ”
  &&  “ (rc_reservations_same M_verify M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2_verify )) (PreH4 : (store_type M_post_3 t1_pre tr1_verify )) (PreH5 : (retval <> 0)) (PreH6 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M_verify M_post_3 )) (PreH9 : (rc_reservations_same M_verify M_post_3 )) (PreH10 : (retval_2 = 0)) (PreH11 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr1_verify = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M_verify t1_pre n )) (PreH21 : (rc_valid M_verify )) (PreH22 : (store_type M_verify t1_pre tr1_verify )) (PreH23 : (store_type M_verify t2_pre tr2_verify )) (PreH24 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH25 : (retval_2 = 0)),
  TT && emp 
|--
  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify_return_wit_4_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t1_pre n )) (PreH2 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2_verify )) (PreH4 : (store_type M_post_3 t1_pre tr1_verify )) (PreH5 : (retval <> 0)) (PreH6 : (infer_result 1 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M_verify M_post_3 )) (PreH9 : (rc_reservations_same M_verify M_post_3 )) (PreH10 : (retval_2 = 0)) (PreH11 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr1_verify = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M_verify t1_pre n )) (PreH21 : (rc_valid M_verify )) (PreH22 : (store_type M_verify t1_pre tr1_verify )) (PreH23 : (store_type M_verify t2_pre tr2_verify )) (PreH24 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH25 : (retval_2 = 0)),
  (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 )
.

Definition atype_unify_return_wit_5 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t1_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1_verify )) (PreH8 : (store_type M_post_4 t2_pre tr2_verify )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel tr_out tr2_verify s_verify s_post_3 )) (PreH11 : (infer_result 1 M_post_3 s_verify retval_3 t2_pre retval M_post_4 s_post_3 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_3 t2_pre tr2_verify )) (PreH18 : (store_type M_post_3 t1_pre tr1_verify )) (PreH19 : (store_type M_post_3 retval_2 tr )) (PreH20 : (repr_result M_verify s_verify (node_a (n)) retval_3 M_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M_verify M_post_3 )) (PreH23 : (store_type M_post_3 retval_3 tr_out )) (PreH24 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M_verify retval_3 M_post_3 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s_verify (node_a (n)) tr )) (PreH28 : (store_type M_verify retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr1_verify = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M_verify t1_pre n )) (PreH38 : (rc_valid M_verify )) (PreH39 : (store_type M_verify t1_pre tr1_verify )) (PreH40 : (store_type M_verify t2_pre tr2_verify )) (PreH41 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1_verify tr2_verify s_verify s_post ) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_verify M_post ) ”
  &&  “ (rc_reservations_same M_verify M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t1_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1_verify )) (PreH8 : (store_type M_post_4 t2_pre tr2_verify )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel tr_out tr2_verify s_verify s_post_3 )) (PreH11 : (infer_result 1 M_post_3 s_verify retval_3 t2_pre retval M_post_4 s_post_3 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_3 t2_pre tr2_verify )) (PreH18 : (store_type M_post_3 t1_pre tr1_verify )) (PreH19 : (store_type M_post_3 retval_2 tr )) (PreH20 : (repr_result M_verify s_verify (node_a (n)) retval_3 M_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M_verify M_post_3 )) (PreH23 : (store_type M_post_3 retval_3 tr_out )) (PreH24 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M_verify retval_3 M_post_3 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s_verify (node_a (n)) tr )) (PreH28 : (store_type M_verify retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr1_verify = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M_verify t1_pre n )) (PreH38 : (rc_valid M_verify )) (PreH39 : (store_type M_verify t1_pre tr1_verify )) (PreH40 : (store_type M_verify t2_pre tr2_verify )) (PreH41 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1_verify tr2_verify s_verify s_post ) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_verify M_post ) ”
  &&  “ (rc_reservations_same M_verify M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
).

Definition atype_unify_return_wit_6 :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t1_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1_verify )) (PreH8 : (store_type M_post_4 t2_pre tr2_verify )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 1 M_post_3 s_verify retval_3 t2_pre retval M_post_4 s_post_3 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (node_at M_post_3 t1_pre n )) (PreH15 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_3 t2_pre tr2_verify )) (PreH17 : (store_type M_post_3 t1_pre tr1_verify )) (PreH18 : (store_type M_post_3 retval_2 tr )) (PreH19 : (repr_result M_verify s_verify (node_a (n)) retval_3 M_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M_verify M_post_3 )) (PreH22 : (store_type M_post_3 retval_3 tr_out )) (PreH23 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M_verify retval_3 M_post_3 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s_verify (node_a (n)) tr )) (PreH27 : (store_type M_verify retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr1_verify = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M_verify t1_pre n )) (PreH37 : (rc_valid M_verify )) (PreH38 : (store_type M_verify t1_pre tr1_verify )) (PreH39 : (store_type M_verify t2_pre tr2_verify )) (PreH40 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH41 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_verify M_post_2 ) ”
  &&  “ (rc_reservations_same M_verify M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t1_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1_verify )) (PreH8 : (store_type M_post_4 t2_pre tr2_verify )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 1 M_post_3 s_verify retval_3 t2_pre retval M_post_4 s_post_3 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (node_at M_post_3 t1_pre n )) (PreH15 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_3 t2_pre tr2_verify )) (PreH17 : (store_type M_post_3 t1_pre tr1_verify )) (PreH18 : (store_type M_post_3 retval_2 tr )) (PreH19 : (repr_result M_verify s_verify (node_a (n)) retval_3 M_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M_verify M_post_3 )) (PreH22 : (store_type M_post_3 retval_3 tr_out )) (PreH23 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M_verify retval_3 M_post_3 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s_verify (node_a (n)) tr )) (PreH27 : (store_type M_verify retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr1_verify = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M_verify t1_pre n )) (PreH37 : (rc_valid M_verify )) (PreH38 : (store_type M_verify t1_pre tr1_verify )) (PreH39 : (store_type M_verify t2_pre tr2_verify )) (PreH40 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH41 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_verify M_post_2 ) ”
  &&  “ (rc_reservations_same M_verify M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
).

Definition atype_unify_partial_solve_wit_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (PreH1 : (rc_valid M_verify )) (PreH2 : (store_type M_verify t1_pre tr1_verify )) (PreH3 : (store_type M_verify t2_pre tr2_verify )) (PreH4 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  (store_world M_verify )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  EX (n: TypeNode),
  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
.

Definition atype_unify_partial_solve_wit_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M_verify t1_pre n )) (PreH5 : (rc_valid M_verify )) (PreH6 : (store_type M_verify t1_pre tr1_verify )) (PreH7 : (store_type M_verify t2_pre tr2_verify )) (PreH8 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
.

Definition atype_unify_partial_solve_wit_3_pure :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr1_verify = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M_verify t1_pre n )) (PreH10 : (rc_valid M_verify )) (PreH11 : (store_type M_verify t1_pre tr1_verify )) (PreH12 : (store_type M_verify t2_pre tr2_verify )) (PreH13 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
.

Definition atype_unify_partial_solve_wit_3_aux :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr1_verify = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M_verify t1_pre n )) (PreH10 : (rc_valid M_verify )) (PreH11 : (store_type M_verify t1_pre tr1_verify )) (PreH12 : (store_type M_verify t2_pre tr2_verify )) (PreH13 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify_partial_solve_wit_3 := atype_unify_partial_solve_wit_3_pure -> atype_unify_partial_solve_wit_3_aux.

Definition atype_unify_partial_solve_wit_4_pure :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s_verify (node_a (n)) tr )) (PreH3 : (store_type M_verify retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr1_verify = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH17 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (solution_at s_verify (node_a (n)) tr )) (PreH5 : (store_type M_verify retval tr )) (PreH6 : ((node_a (n)) < 100)) (PreH7 : (0 <= (node_a (n)))) (PreH8 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH9 : (n = (Node (3) ((node_a (n))) (0)))) (PreH10 : (tr1_verify = (TVar ((node_a (n)))))) (PreH11 : ((node_tag (n)) = 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M_verify t1_pre n )) (PreH15 : (rc_valid M_verify )) (PreH16 : (store_type M_verify t1_pre tr1_verify )) (PreH17 : (store_type M_verify t2_pre tr2_verify )) (PreH18 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH19 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
).

Definition atype_unify_partial_solve_wit_4_pure_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (solution_at s_verify (node_a (n)) tr )) (PreH5 : (store_type M_verify retval tr )) (PreH6 : ((node_a (n)) < 100)) (PreH7 : (0 <= (node_a (n)))) (PreH8 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH9 : (n = (Node (3) ((node_a (n))) (0)))) (PreH10 : (tr1_verify = (TVar ((node_a (n)))))) (PreH11 : ((node_tag (n)) = 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M_verify t1_pre n )) (PreH15 : (rc_valid M_verify )) (PreH16 : (store_type M_verify t1_pre tr1_verify )) (PreH17 : (store_type M_verify t2_pre tr2_verify )) (PreH18 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH19 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
.

Definition atype_unify_partial_solve_wit_4_pure_split_goal_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (solution_at s_verify (node_a (n)) tr )) (PreH5 : (store_type M_verify retval tr )) (PreH6 : ((node_a (n)) < 100)) (PreH7 : (0 <= (node_a (n)))) (PreH8 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH9 : (n = (Node (3) ((node_a (n))) (0)))) (PreH10 : (tr1_verify = (TVar ((node_a (n)))))) (PreH11 : ((node_tag (n)) = 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M_verify t1_pre n )) (PreH15 : (rc_valid M_verify )) (PreH16 : (store_type M_verify t1_pre tr1_verify )) (PreH17 : (store_type M_verify t2_pre tr2_verify )) (PreH18 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH19 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
.

Definition atype_unify_partial_solve_wit_4_aux :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s_verify (node_a (n)) tr )) (PreH3 : (store_type M_verify retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr1_verify = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M_verify t1_pre n )) (PreH13 : (rc_valid M_verify )) (PreH14 : (store_type M_verify t1_pre tr1_verify )) (PreH15 : (store_type M_verify t2_pre tr2_verify )) (PreH16 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH17 : (retval <> 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M_verify q out_tr ) /\ (repr_rel_node s_verify (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M_verify) (q)) < INT_MAX)) ”
  &&  “ (retval <> 0) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ (store_type M_verify retval tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
.

Definition atype_unify_partial_solve_wit_4 := atype_unify_partial_solve_wit_4_pure -> atype_unify_partial_solve_wit_4_aux.

Definition atype_unify_partial_solve_wit_5_pure :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2_verify )) (PreH4 : (store_type M_post t1_pre tr1_verify )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M_verify s_verify (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M_verify M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M_verify retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s_verify (node_a (n)) tr )) (PreH14 : (store_type M_verify retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1_verify = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M_verify t1_pre n )) (PreH24 : (rc_valid M_verify )) (PreH25 : (store_type M_verify t1_pre tr1_verify )) (PreH26 : (store_type M_verify t2_pre tr2_verify )) (PreH27 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH28 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_verify )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (store_type M_post t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 1 M_post s_verify retval t2_pre ) ”
  &&  “ (repr_rel_node s_verify tr_out tr_out ) ”
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2_verify )) (PreH4 : (store_type M_post t1_pre tr1_verify )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M_verify s_verify (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M_verify M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M_verify retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s_verify (node_a (n)) tr )) (PreH14 : (store_type M_verify retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1_verify = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M_verify t1_pre n )) (PreH24 : (rc_valid M_verify )) (PreH25 : (store_type M_verify t1_pre tr1_verify )) (PreH26 : (store_type M_verify t2_pre tr2_verify )) (PreH27 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH28 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_verify )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (repr_rel_node s_verify tr_out tr_out ) ”
  &&  “ (rc_capacity 1 M_post s_verify retval t2_pre ) ”
).

Definition atype_unify_partial_solve_wit_5_pure_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2_verify )) (PreH4 : (store_type M_post t1_pre tr1_verify )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M_verify s_verify (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M_verify M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M_verify retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s_verify (node_a (n)) tr )) (PreH14 : (store_type M_verify retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1_verify = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M_verify t1_pre n )) (PreH24 : (rc_valid M_verify )) (PreH25 : (store_type M_verify t1_pre tr1_verify )) (PreH26 : (store_type M_verify t2_pre tr2_verify )) (PreH27 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH28 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_verify )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (repr_rel_node s_verify tr_out tr_out ) ”
.

Definition atype_unify_partial_solve_wit_5_pure_split_goal_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2_verify )) (PreH4 : (store_type M_post t1_pre tr1_verify )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M_verify s_verify (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M_verify M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M_verify retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s_verify (node_a (n)) tr )) (PreH14 : (store_type M_verify retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1_verify = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M_verify t1_pre n )) (PreH24 : (rc_valid M_verify )) (PreH25 : (store_type M_verify t1_pre tr1_verify )) (PreH26 : (store_type M_verify t2_pre tr2_verify )) (PreH27 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH28 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_verify )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 1 M_post s_verify retval t2_pre ) ”
.

Definition atype_unify_partial_solve_wit_5_aux :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2_verify )) (PreH4 : (store_type M_post t1_pre tr1_verify )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M_verify s_verify (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M_verify M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M_verify retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s_verify (node_a (n)) tr )) (PreH14 : (store_type M_verify retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1_verify = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M_verify t1_pre n )) (PreH24 : (rc_valid M_verify )) (PreH25 : (store_type M_verify t1_pre tr1_verify )) (PreH26 : (store_type M_verify t2_pre tr2_verify )) (PreH27 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH28 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_verify )
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (store_type M_post t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 1 M_post s_verify retval t2_pre ) ”
  &&  “ (repr_rel_node s_verify tr_out tr_out ) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post t2_pre tr2_verify ) ”
  &&  “ (store_type M_post t1_pre tr1_verify ) ”
  &&  “ (store_type M_post retval_2 tr ) ”
  &&  “ (repr_result M_verify s_verify (node_a (n)) retval M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_verify M_post ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out ) ”
  &&  “ (retain_rel M_verify retval M_post ) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ (store_type M_verify retval_2 tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval_2 <> 0) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_verify )
.

Definition atype_unify_partial_solve_wit_5 := atype_unify_partial_solve_wit_5_pure -> atype_unify_partial_solve_wit_5_aux.

Definition atype_unify_partial_solve_wit_6_pure :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1_verify )) (PreH6 : (store_type M_post t2_pre tr2_verify )) (PreH7 : (retval_3 = 0)) (PreH8 : (unify_rel tr_out tr2_verify s_verify s_post )) (PreH9 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M_post_2 M_post )) (PreH12 : (rc_reservations_same M_post_2 M_post )) (PreH13 : (node_at M_post_2 t1_pre n )) (PreH14 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (store_type M_post_2 t2_pre tr2_verify )) (PreH16 : (store_type M_post_2 t1_pre tr1_verify )) (PreH17 : (store_type M_post_2 retval_2 tr )) (PreH18 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH19 : (rc_valid M_post_2 )) (PreH20 : (rc_preserves M_verify M_post_2 )) (PreH21 : (store_type M_post_2 retval tr_out )) (PreH22 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH23 : (retain_rel M_verify retval M_post_2 )) (PreH24 : (retval_2 <> 0)) (PreH25 : (solution_at s_verify (node_a (n)) tr )) (PreH26 : (store_type M_verify retval_2 tr )) (PreH27 : ((node_a (n)) < 100)) (PreH28 : (0 <= (node_a (n)))) (PreH29 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH30 : (n = (Node (3) ((node_a (n))) (0)))) (PreH31 : (tr1_verify = (TVar ((node_a (n)))))) (PreH32 : ((node_tag (n)) = 3)) (PreH33 : ((node_tag (n)) <= 3)) (PreH34 : (0 <= (node_tag (n)))) (PreH35 : (node_at M_verify t1_pre n )) (PreH36 : (rc_valid M_verify )) (PreH37 : (store_type M_verify t1_pre tr1_verify )) (PreH38 : (store_type M_verify t2_pre tr2_verify )) (PreH39 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH40 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1_verify )) (PreH8 : (store_type M_post t2_pre tr2_verify )) (PreH9 : (retval_3 = 0)) (PreH10 : (unify_rel tr_out tr2_verify s_verify s_post )) (PreH11 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M_post_2 M_post )) (PreH14 : (rc_reservations_same M_post_2 M_post )) (PreH15 : (node_at M_post_2 t1_pre n )) (PreH16 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_2 t2_pre tr2_verify )) (PreH18 : (store_type M_post_2 t1_pre tr1_verify )) (PreH19 : (store_type M_post_2 retval_2 tr )) (PreH20 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH21 : (rc_valid M_post_2 )) (PreH22 : (rc_preserves M_verify M_post_2 )) (PreH23 : (store_type M_post_2 retval tr_out )) (PreH24 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M_verify retval M_post_2 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s_verify (node_a (n)) tr )) (PreH28 : (store_type M_verify retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr1_verify = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M_verify t1_pre n )) (PreH38 : (rc_valid M_verify )) (PreH39 : (store_type M_verify t1_pre tr1_verify )) (PreH40 : (store_type M_verify t2_pre tr2_verify )) (PreH41 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (retval <> 0) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
).

Definition atype_unify_partial_solve_wit_6_pure_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1_verify )) (PreH8 : (store_type M_post t2_pre tr2_verify )) (PreH9 : (retval_3 = 0)) (PreH10 : (unify_rel tr_out tr2_verify s_verify s_post )) (PreH11 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M_post_2 M_post )) (PreH14 : (rc_reservations_same M_post_2 M_post )) (PreH15 : (node_at M_post_2 t1_pre n )) (PreH16 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_2 t2_pre tr2_verify )) (PreH18 : (store_type M_post_2 t1_pre tr1_verify )) (PreH19 : (store_type M_post_2 retval_2 tr )) (PreH20 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH21 : (rc_valid M_post_2 )) (PreH22 : (rc_preserves M_verify M_post_2 )) (PreH23 : (store_type M_post_2 retval tr_out )) (PreH24 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M_verify retval M_post_2 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s_verify (node_a (n)) tr )) (PreH28 : (store_type M_verify retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr1_verify = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M_verify t1_pre n )) (PreH38 : (rc_valid M_verify )) (PreH39 : (store_type M_verify t1_pre tr1_verify )) (PreH40 : (store_type M_verify t2_pre tr2_verify )) (PreH41 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (retval <> 0) ”
.

Definition atype_unify_partial_solve_wit_6_pure_split_goal_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1_verify )) (PreH8 : (store_type M_post t2_pre tr2_verify )) (PreH9 : (retval_3 = 0)) (PreH10 : (unify_rel tr_out tr2_verify s_verify s_post )) (PreH11 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M_post_2 M_post )) (PreH14 : (rc_reservations_same M_post_2 M_post )) (PreH15 : (node_at M_post_2 t1_pre n )) (PreH16 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_2 t2_pre tr2_verify )) (PreH18 : (store_type M_post_2 t1_pre tr1_verify )) (PreH19 : (store_type M_post_2 retval_2 tr )) (PreH20 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH21 : (rc_valid M_post_2 )) (PreH22 : (rc_preserves M_verify M_post_2 )) (PreH23 : (store_type M_post_2 retval tr_out )) (PreH24 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M_verify retval M_post_2 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s_verify (node_a (n)) tr )) (PreH28 : (store_type M_verify retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr1_verify = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M_verify t1_pre n )) (PreH38 : (rc_valid M_verify )) (PreH39 : (store_type M_verify t1_pre tr1_verify )) (PreH40 : (store_type M_verify t2_pre tr2_verify )) (PreH41 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (retval)) > 0) ”
.

Definition atype_unify_partial_solve_wit_6_aux :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1_verify )) (PreH6 : (store_type M_post t2_pre tr2_verify )) (PreH7 : (retval_3 = 0)) (PreH8 : (unify_rel tr_out tr2_verify s_verify s_post )) (PreH9 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M_post_2 M_post )) (PreH12 : (rc_reservations_same M_post_2 M_post )) (PreH13 : (node_at M_post_2 t1_pre n )) (PreH14 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (store_type M_post_2 t2_pre tr2_verify )) (PreH16 : (store_type M_post_2 t1_pre tr1_verify )) (PreH17 : (store_type M_post_2 retval_2 tr )) (PreH18 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH19 : (rc_valid M_post_2 )) (PreH20 : (rc_preserves M_verify M_post_2 )) (PreH21 : (store_type M_post_2 retval tr_out )) (PreH22 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH23 : (retain_rel M_verify retval M_post_2 )) (PreH24 : (retval_2 <> 0)) (PreH25 : (solution_at s_verify (node_a (n)) tr )) (PreH26 : (store_type M_verify retval_2 tr )) (PreH27 : ((node_a (n)) < 100)) (PreH28 : (0 <= (node_a (n)))) (PreH29 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH30 : (n = (Node (3) ((node_a (n))) (0)))) (PreH31 : (tr1_verify = (TVar ((node_a (n)))))) (PreH32 : ((node_tag (n)) = 3)) (PreH33 : ((node_tag (n)) <= 3)) (PreH34 : (0 <= (node_tag (n)))) (PreH35 : (node_at M_verify t1_pre n )) (PreH36 : (rc_valid M_verify )) (PreH37 : (store_type M_verify t1_pre tr1_verify )) (PreH38 : (store_type M_verify t2_pre tr2_verify )) (PreH39 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH40 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (store_type M_post retval_2 tr ) ”
  &&  “ (store_type M_post t1_pre tr1_verify ) ”
  &&  “ (store_type M_post t2_pre tr2_verify ) ”
  &&  “ (retval_3 = 0) ”
  &&  “ (unify_rel tr_out tr2_verify s_verify s_post ) ”
  &&  “ (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_post_2 M_post ) ”
  &&  “ (rc_reservations_same M_post_2 M_post ) ”
  &&  “ (node_at M_post_2 t1_pre n ) ”
  &&  “ (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post_2 t2_pre tr2_verify ) ”
  &&  “ (store_type M_post_2 t1_pre tr1_verify ) ”
  &&  “ (store_type M_post_2 retval_2 tr ) ”
  &&  “ (repr_result M_verify s_verify (node_a (n)) retval M_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_verify M_post_2 ) ”
  &&  “ (store_type M_post_2 retval tr_out ) ”
  &&  “ (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out ) ”
  &&  “ (retain_rel M_verify retval M_post_2 ) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ (store_type M_verify retval_2 tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval_2 <> 0) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify_partial_solve_wit_6 := atype_unify_partial_solve_wit_6_pure -> atype_unify_partial_solve_wit_6_aux.

Definition atype_unify_partial_solve_wit_7_pure :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1_verify )) (PreH6 : (store_type M_post t2_pre tr2_verify )) (PreH7 : (retval_3 <> 0)) (PreH8 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M_post_2 M_post )) (PreH11 : (rc_reservations_same M_post_2 M_post )) (PreH12 : (node_at M_post_2 t1_pre n )) (PreH13 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (store_type M_post_2 t2_pre tr2_verify )) (PreH15 : (store_type M_post_2 t1_pre tr1_verify )) (PreH16 : (store_type M_post_2 retval_2 tr )) (PreH17 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH18 : (rc_valid M_post_2 )) (PreH19 : (rc_preserves M_verify M_post_2 )) (PreH20 : (store_type M_post_2 retval tr_out )) (PreH21 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH22 : (retain_rel M_verify retval M_post_2 )) (PreH23 : (retval_2 <> 0)) (PreH24 : (solution_at s_verify (node_a (n)) tr )) (PreH25 : (store_type M_verify retval_2 tr )) (PreH26 : ((node_a (n)) < 100)) (PreH27 : (0 <= (node_a (n)))) (PreH28 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH29 : (n = (Node (3) ((node_a (n))) (0)))) (PreH30 : (tr1_verify = (TVar ((node_a (n)))))) (PreH31 : ((node_tag (n)) = 3)) (PreH32 : ((node_tag (n)) <= 3)) (PreH33 : (0 <= (node_tag (n)))) (PreH34 : (node_at M_verify t1_pre n )) (PreH35 : (rc_valid M_verify )) (PreH36 : (store_type M_verify t1_pre tr1_verify )) (PreH37 : (store_type M_verify t2_pre tr2_verify )) (PreH38 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH39 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1_verify )) (PreH8 : (store_type M_post t2_pre tr2_verify )) (PreH9 : (retval_3 <> 0)) (PreH10 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M_post_2 M_post )) (PreH13 : (rc_reservations_same M_post_2 M_post )) (PreH14 : (node_at M_post_2 t1_pre n )) (PreH15 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_2 t2_pre tr2_verify )) (PreH17 : (store_type M_post_2 t1_pre tr1_verify )) (PreH18 : (store_type M_post_2 retval_2 tr )) (PreH19 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH20 : (rc_valid M_post_2 )) (PreH21 : (rc_preserves M_verify M_post_2 )) (PreH22 : (store_type M_post_2 retval tr_out )) (PreH23 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M_verify retval M_post_2 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s_verify (node_a (n)) tr )) (PreH27 : (store_type M_verify retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr1_verify = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M_verify t1_pre n )) (PreH37 : (rc_valid M_verify )) (PreH38 : (store_type M_verify t1_pre tr1_verify )) (PreH39 : (store_type M_verify t2_pre tr2_verify )) (PreH40 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH41 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (retval <> 0) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
).

Definition atype_unify_partial_solve_wit_7_pure_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1_verify )) (PreH8 : (store_type M_post t2_pre tr2_verify )) (PreH9 : (retval_3 <> 0)) (PreH10 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M_post_2 M_post )) (PreH13 : (rc_reservations_same M_post_2 M_post )) (PreH14 : (node_at M_post_2 t1_pre n )) (PreH15 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_2 t2_pre tr2_verify )) (PreH17 : (store_type M_post_2 t1_pre tr1_verify )) (PreH18 : (store_type M_post_2 retval_2 tr )) (PreH19 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH20 : (rc_valid M_post_2 )) (PreH21 : (rc_preserves M_verify M_post_2 )) (PreH22 : (store_type M_post_2 retval tr_out )) (PreH23 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M_verify retval M_post_2 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s_verify (node_a (n)) tr )) (PreH27 : (store_type M_verify retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr1_verify = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M_verify t1_pre n )) (PreH37 : (rc_valid M_verify )) (PreH38 : (store_type M_verify t1_pre tr1_verify )) (PreH39 : (store_type M_verify t2_pre tr2_verify )) (PreH40 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH41 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (retval <> 0) ”
.

Definition atype_unify_partial_solve_wit_7_pure_split_goal_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1_verify )) (PreH8 : (store_type M_post t2_pre tr2_verify )) (PreH9 : (retval_3 <> 0)) (PreH10 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M_post_2 M_post )) (PreH13 : (rc_reservations_same M_post_2 M_post )) (PreH14 : (node_at M_post_2 t1_pre n )) (PreH15 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_2 t2_pre tr2_verify )) (PreH17 : (store_type M_post_2 t1_pre tr1_verify )) (PreH18 : (store_type M_post_2 retval_2 tr )) (PreH19 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH20 : (rc_valid M_post_2 )) (PreH21 : (rc_preserves M_verify M_post_2 )) (PreH22 : (store_type M_post_2 retval tr_out )) (PreH23 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M_verify retval M_post_2 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s_verify (node_a (n)) tr )) (PreH27 : (store_type M_verify retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr1_verify = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M_verify t1_pre n )) (PreH37 : (rc_valid M_verify )) (PreH38 : (store_type M_verify t1_pre tr1_verify )) (PreH39 : (store_type M_verify t2_pre tr2_verify )) (PreH40 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH41 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (retval)) > 0) ”
.

Definition atype_unify_partial_solve_wit_7_aux :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1_verify )) (PreH6 : (store_type M_post t2_pre tr2_verify )) (PreH7 : (retval_3 <> 0)) (PreH8 : (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M_post_2 M_post )) (PreH11 : (rc_reservations_same M_post_2 M_post )) (PreH12 : (node_at M_post_2 t1_pre n )) (PreH13 : (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (store_type M_post_2 t2_pre tr2_verify )) (PreH15 : (store_type M_post_2 t1_pre tr1_verify )) (PreH16 : (store_type M_post_2 retval_2 tr )) (PreH17 : (repr_result M_verify s_verify (node_a (n)) retval M_post_2 )) (PreH18 : (rc_valid M_post_2 )) (PreH19 : (rc_preserves M_verify M_post_2 )) (PreH20 : (store_type M_post_2 retval tr_out )) (PreH21 : (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out )) (PreH22 : (retain_rel M_verify retval M_post_2 )) (PreH23 : (retval_2 <> 0)) (PreH24 : (solution_at s_verify (node_a (n)) tr )) (PreH25 : (store_type M_verify retval_2 tr )) (PreH26 : ((node_a (n)) < 100)) (PreH27 : (0 <= (node_a (n)))) (PreH28 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH29 : (n = (Node (3) ((node_a (n))) (0)))) (PreH30 : (tr1_verify = (TVar ((node_a (n)))))) (PreH31 : ((node_tag (n)) = 3)) (PreH32 : ((node_tag (n)) <= 3)) (PreH33 : (0 <= (node_tag (n)))) (PreH34 : (node_at M_verify t1_pre n )) (PreH35 : (rc_valid M_verify )) (PreH36 : (store_type M_verify t1_pre tr1_verify )) (PreH37 : (store_type M_verify t2_pre tr2_verify )) (PreH38 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH39 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (store_type M_post retval_2 tr ) ”
  &&  “ (store_type M_post t1_pre tr1_verify ) ”
  &&  “ (store_type M_post t2_pre tr2_verify ) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (infer_result 1 M_post_2 s_verify retval t2_pre retval_3 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_post_2 M_post ) ”
  &&  “ (rc_reservations_same M_post_2 M_post ) ”
  &&  “ (node_at M_post_2 t1_pre n ) ”
  &&  “ (node_at M_post_2 t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post_2 t2_pre tr2_verify ) ”
  &&  “ (store_type M_post_2 t1_pre tr1_verify ) ”
  &&  “ (store_type M_post_2 retval_2 tr ) ”
  &&  “ (repr_result M_verify s_verify (node_a (n)) retval M_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_verify M_post_2 ) ”
  &&  “ (store_type M_post_2 retval tr_out ) ”
  &&  “ (repr_rel_node s_verify (TVar ((node_a (n)))) tr_out ) ”
  &&  “ (retain_rel M_verify retval M_post_2 ) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (solution_at s_verify (node_a (n)) tr ) ”
  &&  “ (store_type M_verify retval_2 tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval_2 <> 0) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify_partial_solve_wit_7 := atype_unify_partial_solve_wit_7_pure -> atype_unify_partial_solve_wit_7_aux.

Definition atype_unify_partial_solve_wit_8_pure :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1_verify = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M_verify t1_pre n )) (PreH12 : (rc_valid M_verify )) (PreH13 : (store_type M_verify t1_pre tr1_verify )) (PreH14 : (store_type M_verify t2_pre tr2_verify )) (PreH15 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH16 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH5 : ((node_a (n)) < 100)) (PreH6 : (0 <= (node_a (n)))) (PreH7 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (n = (Node (3) ((node_a (n))) (0)))) (PreH9 : (tr1_verify = (TVar ((node_a (n)))))) (PreH10 : ((node_tag (n)) = 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M_verify t1_pre n )) (PreH14 : (rc_valid M_verify )) (PreH15 : (store_type M_verify t1_pre tr1_verify )) (PreH16 : (store_type M_verify t2_pre tr2_verify )) (PreH17 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH18 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
  &&  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
).

Definition atype_unify_partial_solve_wit_8_pure_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH5 : ((node_a (n)) < 100)) (PreH6 : (0 <= (node_a (n)))) (PreH7 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (n = (Node (3) ((node_a (n))) (0)))) (PreH9 : (tr1_verify = (TVar ((node_a (n)))))) (PreH10 : ((node_tag (n)) = 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M_verify t1_pre n )) (PreH14 : (rc_valid M_verify )) (PreH15 : (store_type M_verify t1_pre tr1_verify )) (PreH16 : (store_type M_verify t2_pre tr2_verify )) (PreH17 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH18 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
.

Definition atype_unify_partial_solve_wit_8_pure_split_goal_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH5 : ((node_a (n)) < 100)) (PreH6 : (0 <= (node_a (n)))) (PreH7 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (n = (Node (3) ((node_a (n))) (0)))) (PreH9 : (tr1_verify = (TVar ((node_a (n)))))) (PreH10 : ((node_tag (n)) = 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M_verify t1_pre n )) (PreH14 : (rc_valid M_verify )) (PreH15 : (store_type M_verify t1_pre tr1_verify )) (PreH16 : (store_type M_verify t2_pre tr2_verify )) (PreH17 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH18 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
.

Definition atype_unify_partial_solve_wit_8_aux :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1_verify = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M_verify t1_pre n )) (PreH12 : (rc_valid M_verify )) (PreH13 : (store_type M_verify t1_pre tr1_verify )) (PreH14 : (store_type M_verify t2_pre tr2_verify )) (PreH15 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )) (PreH16 : (retval = 0)),
  (store_solution M_verify ( &( "res" ) ) s_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_verify (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
  &&  “ (retval = 0) ”
  &&  “ forall (tr: TypeTree), ~((solution_at s_verify (node_a (n)) tr )) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M_verify t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1_verify = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (retval = 0) ”
  &&  (store_world M_verify )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
.

Definition atype_unify_partial_solve_wit_8 := atype_unify_partial_solve_wit_8_pure -> atype_unify_partial_solve_wit_8_aux.

Definition atype_unify_partial_solve_wit_9_pure :=
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M_verify t1_pre n )) (PreH5 : (rc_valid M_verify )) (PreH6 : (store_type M_verify t1_pre tr1_verify )) (PreH7 : (store_type M_verify t2_pre tr2_verify )) (PreH8 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
) \/
(
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M_verify t1_pre n )) (PreH7 : (rc_valid M_verify )) (PreH8 : (store_type M_verify t1_pre tr1_verify )) (PreH9 : (store_type M_verify t2_pre tr2_verify )) (PreH10 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
  &&  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
).

Definition atype_unify_partial_solve_wit_9_pure_split_goal_1 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M_verify t1_pre n )) (PreH7 : (rc_valid M_verify )) (PreH8 : (store_type M_verify t1_pre tr1_verify )) (PreH9 : (store_type M_verify t2_pre tr2_verify )) (PreH10 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
.

Definition atype_unify_partial_solve_wit_9_pure_split_goal_2 :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M_verify t1_pre n )) (PreH7 : (rc_valid M_verify )) (PreH8 : (store_type M_verify t1_pre tr1_verify )) (PreH9 : (store_type M_verify t2_pre tr2_verify )) (PreH10 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
.

Definition atype_unify_partial_solve_wit_9_aux :=
forall (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_verify: sol) (M_verify: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M_verify t1_pre n )) (PreH5 : (rc_valid M_verify )) (PreH6 : (store_type M_verify t1_pre tr1_verify )) (PreH7 : (store_type M_verify t2_pre tr2_verify )) (PreH8 : (rc_capacity 0 M_verify s_verify t1_pre t2_pre )),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M_verify (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
|--
  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 1 M_verify s_verify t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s_verify tr1_verify tr1_verify ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M_verify t1_pre n ) ”
  &&  “ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  (store_world M_verify )
  **  (store_solution M_verify ( &( "res" ) ) s_verify )
.

Definition atype_unify_partial_solve_wit_9 := atype_unify_partial_solve_wit_9_pure -> atype_unify_partial_solve_wit_9_aux.

(*----- Function atype_unify1 -----*)

Definition atype_unify1_safety_wit_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= 3)) (PreH2 : (0 <= (node_tag (n)))) (PreH3 : (node_at M t2_pre n )) (PreH4 : (rc_valid M )) (PreH5 : (store_type M t1_pre tr1 )) (PreH6 : (store_type M t2_pre tr2 )) (PreH7 : (repr_rel_node s tr1 tr1 )) (PreH8 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify1_safety_wit_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s (node_a (n)) tr )) (PreH3 : (store_type M retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr2 = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH18 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify1_safety_wit_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH17 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify1_entail_wit_1_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr_2: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s (node_a (n)) tr_2 )) (PreH3 : (store_type M retval tr_2 )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr2 = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH18 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (retval = 0) ”
  &&  “ forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr )) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval = 0) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify1_entail_wit_1_2 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH17 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (retval = 0) ”
  &&  “ forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr )) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval = 0) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH17 : (retval = 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n))) (0)) = n) ”
  &&  emp
).

Definition atype_unify1_entail_wit_1_2_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH17 : (retval = 0)),
  ((Node (3) ((node_a (n))) (0)) = n)
.

Definition atype_unify1_entail_wit_2_1 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s (node_a (n)) tr )) (PreH3 : (store_type M retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr2 = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH18 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (retval <> 0) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ (store_type M retval tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval <> 0) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s (node_a (n)) tr )) (PreH3 : (store_type M retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr2 = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH18 : (retval <> 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n))) (0)) = n) ”
  &&  emp
).

Definition atype_unify1_entail_wit_2_1_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s (node_a (n)) tr )) (PreH3 : (store_type M retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr2 = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH18 : (retval <> 0)),
  ((Node (3) ((node_a (n))) (0)) = n)
.

Definition atype_unify1_entail_wit_2_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr_2: TypeTree), ~((solution_at s (node_a (n)) tr_2 ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH17 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  EX (tr: TypeTree),
  “ (retval <> 0) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ (store_type M retval tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval <> 0) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify1_return_wit_1 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2 )) (PreH3 : (store_type M_post_3 t1_pre tr1 )) (PreH4 : (retval = 0)) (PreH5 : (unify_rel tr1 tr2 s s_post_3 )) (PreH6 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M M_post_3 )) (PreH9 : (rc_reservations_same M M_post_3 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t2_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (rc_capacity 1 M s t1_pre t2_pre )),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2 )) (PreH3 : (store_type M_post_3 t1_pre tr1 )) (PreH4 : (retval = 0)) (PreH5 : (unify_rel tr1 tr2 s s_post_3 )) (PreH6 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M M_post_3 )) (PreH9 : (rc_reservations_same M M_post_3 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t2_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (rc_capacity 1 M s t1_pre t2_pre )),
  TT && emp 
|--
  “ (infer_result 1 M s t1_pre t2_pre 0 M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify1_return_wit_1_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2 )) (PreH3 : (store_type M_post_3 t1_pre tr1 )) (PreH4 : (retval = 0)) (PreH5 : (unify_rel tr1 tr2 s s_post_3 )) (PreH6 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M M_post_3 )) (PreH9 : (rc_reservations_same M M_post_3 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t2_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (rc_capacity 1 M s t1_pre t2_pre )),
  (infer_result 1 M s t1_pre t2_pre 0 M_post_3 s_post_3 )
.

Definition atype_unify1_return_wit_2 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2 )) (PreH3 : (store_type M_post_3 t1_pre tr1 )) (PreH4 : (retval <> 0)) (PreH5 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH6 : (rc_valid M_post_3 )) (PreH7 : (rc_preserves M M_post_3 )) (PreH8 : (rc_reservations_same M M_post_3 )) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2 )) (PreH3 : (store_type M_post_3 t1_pre tr1 )) (PreH4 : (retval <> 0)) (PreH5 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH6 : (rc_valid M_post_3 )) (PreH7 : (rc_preserves M M_post_3 )) (PreH8 : (rc_reservations_same M M_post_3 )) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )),
  TT && emp 
|--
  “ (infer_result 1 M s t1_pre t2_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify1_return_wit_2_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (store_type M_post_3 t2_pre tr2 )) (PreH3 : (store_type M_post_3 t1_pre tr1 )) (PreH4 : (retval <> 0)) (PreH5 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH6 : (rc_valid M_post_3 )) (PreH7 : (rc_preserves M M_post_3 )) (PreH8 : (rc_reservations_same M M_post_3 )) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )),
  (infer_result 1 M s t1_pre t2_pre retval M_post_3 s_post_3 )
.

Definition atype_unify1_return_wit_3 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1 tr2 s s_post_3 )) (PreH7 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH8 : (rc_valid M_post_3 )) (PreH9 : (rc_preserves M M_post_3 )) (PreH10 : (rc_reservations_same M M_post_3 )) (PreH11 : (retval_2 = 0)) (PreH12 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH13 : ((node_a (n)) < 100)) (PreH14 : (0 <= (node_a (n)))) (PreH15 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (n = (Node (3) ((node_a (n))) (0)))) (PreH17 : (tr2 = (TVar ((node_a (n)))))) (PreH18 : ((node_tag (n)) = 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t2_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH27 : (retval_2 = 0)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1 tr2 s s_post_3 )) (PreH7 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH8 : (rc_valid M_post_3 )) (PreH9 : (rc_preserves M M_post_3 )) (PreH10 : (rc_reservations_same M M_post_3 )) (PreH11 : (retval_2 = 0)) (PreH12 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH13 : ((node_a (n)) < 100)) (PreH14 : (0 <= (node_a (n)))) (PreH15 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (n = (Node (3) ((node_a (n))) (0)))) (PreH17 : (tr2 = (TVar ((node_a (n)))))) (PreH18 : ((node_tag (n)) = 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t2_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH27 : (retval_2 = 0)),
  TT && emp 
|--
  “ (infer_result 1 M s t1_pre t2_pre 0 M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify1_return_wit_3_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1 tr2 s s_post_3 )) (PreH7 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH8 : (rc_valid M_post_3 )) (PreH9 : (rc_preserves M M_post_3 )) (PreH10 : (rc_reservations_same M M_post_3 )) (PreH11 : (retval_2 = 0)) (PreH12 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH13 : ((node_a (n)) < 100)) (PreH14 : (0 <= (node_a (n)))) (PreH15 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (n = (Node (3) ((node_a (n))) (0)))) (PreH17 : (tr2 = (TVar ((node_a (n)))))) (PreH18 : ((node_tag (n)) = 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t2_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH27 : (retval_2 = 0)),
  (infer_result 1 M s t1_pre t2_pre 0 M_post_3 s_post_3 )
.

Definition atype_unify1_return_wit_4 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (retval <> 0)) (PreH6 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M M_post_3 )) (PreH9 : (rc_reservations_same M M_post_3 )) (PreH10 : (retval_2 = 0)) (PreH11 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr2 = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t2_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH26 : (retval_2 = 0)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (retval <> 0)) (PreH6 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M M_post_3 )) (PreH9 : (rc_reservations_same M M_post_3 )) (PreH10 : (retval_2 = 0)) (PreH11 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr2 = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t2_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH26 : (retval_2 = 0)),
  TT && emp 
|--
  “ (infer_result 1 M s t1_pre t2_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify1_return_wit_4_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (node_at M_post_3 t2_pre n )) (PreH2 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (retval <> 0)) (PreH6 : (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )) (PreH7 : (rc_valid M_post_3 )) (PreH8 : (rc_preserves M M_post_3 )) (PreH9 : (rc_reservations_same M M_post_3 )) (PreH10 : (retval_2 = 0)) (PreH11 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr2 = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t2_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH26 : (retval_2 = 0)),
  (infer_result 1 M s t1_pre t2_pre retval M_post_3 s_post_3 )
.

Definition atype_unify1_return_wit_5 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t2_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel tr1 tr_out s s_post_3 )) (PreH11 : (infer_result 2 M_post_3 s t1_pre retval_3 retval M_post_4 s_post_3 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (node_at M_post_3 t2_pre n )) (PreH16 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 retval_2 tr )) (PreH20 : (repr_result M s (node_a (n)) retval_3 M_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (store_type M_post_3 retval_3 tr_out )) (PreH24 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M retval_3 M_post_3 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s (node_a (n)) tr )) (PreH28 : (store_type M retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr2 = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M t2_pre n )) (PreH38 : (rc_valid M )) (PreH39 : (store_type M t1_pre tr1 )) (PreH40 : (store_type M t2_pre tr2 )) (PreH41 : (repr_rel_node s tr1 tr1 )) (PreH42 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH43 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t2_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel tr1 tr_out s s_post_3 )) (PreH11 : (infer_result 2 M_post_3 s t1_pre retval_3 retval M_post_4 s_post_3 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (node_at M_post_3 t2_pre n )) (PreH16 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 retval_2 tr )) (PreH20 : (repr_result M s (node_a (n)) retval_3 M_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (store_type M_post_3 retval_3 tr_out )) (PreH24 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M retval_3 M_post_3 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s (node_a (n)) tr )) (PreH28 : (store_type M retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr2 = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M t2_pre n )) (PreH38 : (rc_valid M )) (PreH39 : (store_type M t1_pre tr1 )) (PreH40 : (store_type M t2_pre tr2 )) (PreH41 : (repr_rel_node s tr1 tr1 )) (PreH42 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH43 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
).

Definition atype_unify1_return_wit_6 :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t2_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 2 M_post_3 s t1_pre retval_3 retval M_post_4 s_post_3 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (node_at M_post_3 t2_pre n )) (PreH15 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_3 t2_pre tr2 )) (PreH17 : (store_type M_post_3 t1_pre tr1 )) (PreH18 : (store_type M_post_3 retval_2 tr )) (PreH19 : (repr_result M s (node_a (n)) retval_3 M_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (store_type M_post_3 retval_3 tr_out )) (PreH23 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M retval_3 M_post_3 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s (node_a (n)) tr )) (PreH27 : (store_type M retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr2 = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M t2_pre n )) (PreH37 : (rc_valid M )) (PreH38 : (store_type M t1_pre tr1 )) (PreH39 : (store_type M t2_pre tr2 )) (PreH40 : (repr_rel_node s tr1 tr1 )) (PreH41 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_3: RcState) (retval_3: Z) (M_post_4: RcState) (s_post_3: sol) (retval: Z) (M_post_5: RcState) (PreH1 : (release_rel M_post_4 retval_3 M_post_5 )) (PreH2 : (rc_valid M_post_5 )) (PreH3 : (node_at M_post_4 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post_4 t2_pre n )) (PreH5 : (store_type M_post_4 retval_3 tr_out )) (PreH6 : (store_type M_post_4 retval_2 tr )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 2 M_post_3 s t1_pre retval_3 retval M_post_4 s_post_3 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (node_at M_post_3 t2_pre n )) (PreH15 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_3 t2_pre tr2 )) (PreH17 : (store_type M_post_3 t1_pre tr1 )) (PreH18 : (store_type M_post_3 retval_2 tr )) (PreH19 : (repr_result M s (node_a (n)) retval_3 M_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (store_type M_post_3 retval_3 tr_out )) (PreH23 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M retval_3 M_post_3 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s (node_a (n)) tr )) (PreH27 : (store_type M retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr2 = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M t2_pre n )) (PreH37 : (rc_valid M )) (PreH38 : (store_type M t1_pre tr1 )) (PreH39 : (store_type M t2_pre tr2 )) (PreH40 : (repr_rel_node s tr1 tr1 )) (PreH41 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post_5 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 1 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
).

Definition atype_unify1_partial_solve_wit_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (PreH1 : (rc_valid M )) (PreH2 : (store_type M t1_pre tr1 )) (PreH3 : (store_type M t2_pre tr2 )) (PreH4 : (repr_rel_node s tr1 tr1 )) (PreH5 : (rc_capacity 1 M s t1_pre t2_pre )),
  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (n: TypeNode),
  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify1_partial_solve_wit_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t2_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify1_partial_solve_wit_3_pure :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr2 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t2_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
.

Definition atype_unify1_partial_solve_wit_3_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr2 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t2_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify1_partial_solve_wit_3 := atype_unify1_partial_solve_wit_3_pure -> atype_unify1_partial_solve_wit_3_aux.

Definition atype_unify1_partial_solve_wit_4_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s (node_a (n)) tr )) (PreH3 : (store_type M retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr2 = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH18 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (solution_at s (node_a (n)) tr )) (PreH5 : (store_type M retval tr )) (PreH6 : ((node_a (n)) < 100)) (PreH7 : (0 <= (node_a (n)))) (PreH8 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH9 : (n = (Node (3) ((node_a (n))) (0)))) (PreH10 : (tr2 = (TVar ((node_a (n)))))) (PreH11 : ((node_tag (n)) = 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t2_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH20 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
).

Definition atype_unify1_partial_solve_wit_4_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (solution_at s (node_a (n)) tr )) (PreH5 : (store_type M retval tr )) (PreH6 : ((node_a (n)) < 100)) (PreH7 : (0 <= (node_a (n)))) (PreH8 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH9 : (n = (Node (3) ((node_a (n))) (0)))) (PreH10 : (tr2 = (TVar ((node_a (n)))))) (PreH11 : ((node_tag (n)) = 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t2_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH20 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
.

Definition atype_unify1_partial_solve_wit_4_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (solution_at s (node_a (n)) tr )) (PreH5 : (store_type M retval tr )) (PreH6 : ((node_a (n)) < 100)) (PreH7 : (0 <= (node_a (n)))) (PreH8 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH9 : (n = (Node (3) ((node_a (n))) (0)))) (PreH10 : (tr2 = (TVar ((node_a (n)))))) (PreH11 : ((node_tag (n)) = 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t2_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH20 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
.

Definition atype_unify1_partial_solve_wit_4_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (solution_at s (node_a (n)) tr )) (PreH3 : (store_type M retval tr )) (PreH4 : ((node_a (n)) < 100)) (PreH5 : (0 <= (node_a (n)))) (PreH6 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (n = (Node (3) ((node_a (n))) (0)))) (PreH8 : (tr2 = (TVar ((node_a (n)))))) (PreH9 : ((node_tag (n)) = 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t2_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH18 : (retval <> 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a (n)))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
  &&  “ forall (q: Z), forall (out_tr: TypeTree), (((store_type M q out_tr ) /\ (repr_rel_node s (TVar ((node_a ((Node (3) ((node_a (n))) (0)))))) out_tr )) -> ((rc_count (M) (q)) < INT_MAX)) ”
  &&  “ (retval <> 0) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ (store_type M retval tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify1_partial_solve_wit_4 := atype_unify1_partial_solve_wit_4_pure -> atype_unify1_partial_solve_wit_4_aux.

Definition atype_unify1_partial_solve_wit_5_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t2_pre n )) (PreH2 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M s (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s (node_a (n)) tr )) (PreH14 : (store_type M retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr2 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t2_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH29 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 2 M_post s t1_pre retval ) ”
  &&  “ (repr_rel_node s tr_out tr_out ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t2_pre n )) (PreH2 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M s (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s (node_a (n)) tr )) (PreH14 : (store_type M retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr2 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t2_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH29 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (repr_rel_node s tr_out tr_out ) ”
  &&  “ (rc_capacity 2 M_post s t1_pre retval ) ”
).

Definition atype_unify1_partial_solve_wit_5_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t2_pre n )) (PreH2 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M s (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s (node_a (n)) tr )) (PreH14 : (store_type M retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr2 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t2_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH29 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (repr_rel_node s tr_out tr_out ) ”
.

Definition atype_unify1_partial_solve_wit_5_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t2_pre n )) (PreH2 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M s (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s (node_a (n)) tr )) (PreH14 : (store_type M retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr2 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t2_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH29 : (retval_2 <> 0)),
  ((( &( "r" ) )) # Int  |->_)
  **  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s )
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (rc_capacity 2 M_post s t1_pre retval ) ”
.

Definition atype_unify1_partial_solve_wit_5_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t2_pre n )) (PreH2 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post retval_2 tr )) (PreH6 : (repr_result M s (node_a (n)) retval M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (store_type M_post retval tr_out )) (PreH10 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH11 : (retain_rel M retval M_post )) (PreH12 : (retval_2 <> 0)) (PreH13 : (solution_at s (node_a (n)) tr )) (PreH14 : (store_type M retval_2 tr )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr2 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t2_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH29 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s )
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 2 M_post s t1_pre retval ) ”
  &&  “ (repr_rel_node s tr_out tr_out ) ”
  &&  “ (node_at M_post t2_pre n ) ”
  &&  “ (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post retval_2 tr ) ”
  &&  “ (repr_result M s (node_a (n)) retval M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (repr_rel_node s (TVar ((node_a (n)))) tr_out ) ”
  &&  “ (retain_rel M retval M_post ) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ (store_type M retval_2 tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval_2 <> 0) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s )
.

Definition atype_unify1_partial_solve_wit_5 := atype_unify1_partial_solve_wit_5_pure -> atype_unify1_partial_solve_wit_5_aux.

Definition atype_unify1_partial_solve_wit_6_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t2_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (retval_3 = 0)) (PreH8 : (unify_rel tr1 tr_out s s_post )) (PreH9 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M_post_2 M_post )) (PreH12 : (rc_reservations_same M_post_2 M_post )) (PreH13 : (node_at M_post_2 t2_pre n )) (PreH14 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (store_type M_post_2 t2_pre tr2 )) (PreH16 : (store_type M_post_2 t1_pre tr1 )) (PreH17 : (store_type M_post_2 retval_2 tr )) (PreH18 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH19 : (rc_valid M_post_2 )) (PreH20 : (rc_preserves M M_post_2 )) (PreH21 : (store_type M_post_2 retval tr_out )) (PreH22 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH23 : (retain_rel M retval M_post_2 )) (PreH24 : (retval_2 <> 0)) (PreH25 : (solution_at s (node_a (n)) tr )) (PreH26 : (store_type M retval_2 tr )) (PreH27 : ((node_a (n)) < 100)) (PreH28 : (0 <= (node_a (n)))) (PreH29 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH30 : (n = (Node (3) ((node_a (n))) (0)))) (PreH31 : (tr2 = (TVar ((node_a (n)))))) (PreH32 : ((node_tag (n)) = 3)) (PreH33 : ((node_tag (n)) <= 3)) (PreH34 : (0 <= (node_tag (n)))) (PreH35 : (node_at M t2_pre n )) (PreH36 : (rc_valid M )) (PreH37 : (store_type M t1_pre tr1 )) (PreH38 : (store_type M t2_pre tr2 )) (PreH39 : (repr_rel_node s tr1 tr1 )) (PreH40 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH41 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t2_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (retval_3 = 0)) (PreH10 : (unify_rel tr1 tr_out s s_post )) (PreH11 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M_post_2 M_post )) (PreH14 : (rc_reservations_same M_post_2 M_post )) (PreH15 : (node_at M_post_2 t2_pre n )) (PreH16 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_2 t2_pre tr2 )) (PreH18 : (store_type M_post_2 t1_pre tr1 )) (PreH19 : (store_type M_post_2 retval_2 tr )) (PreH20 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH21 : (rc_valid M_post_2 )) (PreH22 : (rc_preserves M M_post_2 )) (PreH23 : (store_type M_post_2 retval tr_out )) (PreH24 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M retval M_post_2 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s (node_a (n)) tr )) (PreH28 : (store_type M retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr2 = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M t2_pre n )) (PreH38 : (rc_valid M )) (PreH39 : (store_type M t1_pre tr1 )) (PreH40 : (store_type M t2_pre tr2 )) (PreH41 : (repr_rel_node s tr1 tr1 )) (PreH42 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH43 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (retval <> 0) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
).

Definition atype_unify1_partial_solve_wit_6_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t2_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (retval_3 = 0)) (PreH10 : (unify_rel tr1 tr_out s s_post )) (PreH11 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M_post_2 M_post )) (PreH14 : (rc_reservations_same M_post_2 M_post )) (PreH15 : (node_at M_post_2 t2_pre n )) (PreH16 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_2 t2_pre tr2 )) (PreH18 : (store_type M_post_2 t1_pre tr1 )) (PreH19 : (store_type M_post_2 retval_2 tr )) (PreH20 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH21 : (rc_valid M_post_2 )) (PreH22 : (rc_preserves M M_post_2 )) (PreH23 : (store_type M_post_2 retval tr_out )) (PreH24 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M retval M_post_2 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s (node_a (n)) tr )) (PreH28 : (store_type M retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr2 = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M t2_pre n )) (PreH38 : (rc_valid M )) (PreH39 : (store_type M t1_pre tr1 )) (PreH40 : (store_type M t2_pre tr2 )) (PreH41 : (repr_rel_node s tr1 tr1 )) (PreH42 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH43 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (retval <> 0) ”
.

Definition atype_unify1_partial_solve_wit_6_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t2_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (retval_3 = 0)) (PreH10 : (unify_rel tr1 tr_out s s_post )) (PreH11 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M_post_2 M_post )) (PreH14 : (rc_reservations_same M_post_2 M_post )) (PreH15 : (node_at M_post_2 t2_pre n )) (PreH16 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH17 : (store_type M_post_2 t2_pre tr2 )) (PreH18 : (store_type M_post_2 t1_pre tr1 )) (PreH19 : (store_type M_post_2 retval_2 tr )) (PreH20 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH21 : (rc_valid M_post_2 )) (PreH22 : (rc_preserves M M_post_2 )) (PreH23 : (store_type M_post_2 retval tr_out )) (PreH24 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH25 : (retain_rel M retval M_post_2 )) (PreH26 : (retval_2 <> 0)) (PreH27 : (solution_at s (node_a (n)) tr )) (PreH28 : (store_type M retval_2 tr )) (PreH29 : ((node_a (n)) < 100)) (PreH30 : (0 <= (node_a (n)))) (PreH31 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH32 : (n = (Node (3) ((node_a (n))) (0)))) (PreH33 : (tr2 = (TVar ((node_a (n)))))) (PreH34 : ((node_tag (n)) = 3)) (PreH35 : ((node_tag (n)) <= 3)) (PreH36 : (0 <= (node_tag (n)))) (PreH37 : (node_at M t2_pre n )) (PreH38 : (rc_valid M )) (PreH39 : (store_type M t1_pre tr1 )) (PreH40 : (store_type M t2_pre tr2 )) (PreH41 : (repr_rel_node s tr1 tr1 )) (PreH42 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH43 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ ((rc_reserved (M_post) (retval)) > 0) ”
.

Definition atype_unify1_partial_solve_wit_6_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t2_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (retval_3 = 0)) (PreH8 : (unify_rel tr1 tr_out s s_post )) (PreH9 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M_post_2 M_post )) (PreH12 : (rc_reservations_same M_post_2 M_post )) (PreH13 : (node_at M_post_2 t2_pre n )) (PreH14 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (store_type M_post_2 t2_pre tr2 )) (PreH16 : (store_type M_post_2 t1_pre tr1 )) (PreH17 : (store_type M_post_2 retval_2 tr )) (PreH18 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH19 : (rc_valid M_post_2 )) (PreH20 : (rc_preserves M M_post_2 )) (PreH21 : (store_type M_post_2 retval tr_out )) (PreH22 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH23 : (retain_rel M retval M_post_2 )) (PreH24 : (retval_2 <> 0)) (PreH25 : (solution_at s (node_a (n)) tr )) (PreH26 : (store_type M retval_2 tr )) (PreH27 : ((node_a (n)) < 100)) (PreH28 : (0 <= (node_a (n)))) (PreH29 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH30 : (n = (Node (3) ((node_a (n))) (0)))) (PreH31 : (tr2 = (TVar ((node_a (n)))))) (PreH32 : ((node_tag (n)) = 3)) (PreH33 : ((node_tag (n)) <= 3)) (PreH34 : (0 <= (node_tag (n)))) (PreH35 : (node_at M t2_pre n )) (PreH36 : (rc_valid M )) (PreH37 : (store_type M t1_pre tr1 )) (PreH38 : (store_type M t2_pre tr2 )) (PreH39 : (repr_rel_node s tr1 tr1 )) (PreH40 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH41 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (node_at M_post t2_pre n ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (store_type M_post retval_2 tr ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (retval_3 = 0) ”
  &&  “ (unify_rel tr1 tr_out s s_post ) ”
  &&  “ (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_post_2 M_post ) ”
  &&  “ (rc_reservations_same M_post_2 M_post ) ”
  &&  “ (node_at M_post_2 t2_pre n ) ”
  &&  “ (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post_2 t2_pre tr2 ) ”
  &&  “ (store_type M_post_2 t1_pre tr1 ) ”
  &&  “ (store_type M_post_2 retval_2 tr ) ”
  &&  “ (repr_result M s (node_a (n)) retval M_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (store_type M_post_2 retval tr_out ) ”
  &&  “ (repr_rel_node s (TVar ((node_a (n)))) tr_out ) ”
  &&  “ (retain_rel M retval M_post_2 ) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ (store_type M retval_2 tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval_2 <> 0) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify1_partial_solve_wit_6 := atype_unify1_partial_solve_wit_6_pure -> atype_unify1_partial_solve_wit_6_aux.

Definition atype_unify1_partial_solve_wit_7_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t2_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (retval_3 <> 0)) (PreH8 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M_post_2 M_post )) (PreH11 : (rc_reservations_same M_post_2 M_post )) (PreH12 : (node_at M_post_2 t2_pre n )) (PreH13 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (store_type M_post_2 t2_pre tr2 )) (PreH15 : (store_type M_post_2 t1_pre tr1 )) (PreH16 : (store_type M_post_2 retval_2 tr )) (PreH17 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH18 : (rc_valid M_post_2 )) (PreH19 : (rc_preserves M M_post_2 )) (PreH20 : (store_type M_post_2 retval tr_out )) (PreH21 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH22 : (retain_rel M retval M_post_2 )) (PreH23 : (retval_2 <> 0)) (PreH24 : (solution_at s (node_a (n)) tr )) (PreH25 : (store_type M retval_2 tr )) (PreH26 : ((node_a (n)) < 100)) (PreH27 : (0 <= (node_a (n)))) (PreH28 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH29 : (n = (Node (3) ((node_a (n))) (0)))) (PreH30 : (tr2 = (TVar ((node_a (n)))))) (PreH31 : ((node_tag (n)) = 3)) (PreH32 : ((node_tag (n)) <= 3)) (PreH33 : (0 <= (node_tag (n)))) (PreH34 : (node_at M t2_pre n )) (PreH35 : (rc_valid M )) (PreH36 : (store_type M t1_pre tr1 )) (PreH37 : (store_type M t2_pre tr2 )) (PreH38 : (repr_rel_node s tr1 tr1 )) (PreH39 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH40 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t2_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (retval_3 <> 0)) (PreH10 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M_post_2 M_post )) (PreH13 : (rc_reservations_same M_post_2 M_post )) (PreH14 : (node_at M_post_2 t2_pre n )) (PreH15 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_2 t2_pre tr2 )) (PreH17 : (store_type M_post_2 t1_pre tr1 )) (PreH18 : (store_type M_post_2 retval_2 tr )) (PreH19 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH20 : (rc_valid M_post_2 )) (PreH21 : (rc_preserves M M_post_2 )) (PreH22 : (store_type M_post_2 retval tr_out )) (PreH23 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M retval M_post_2 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s (node_a (n)) tr )) (PreH27 : (store_type M retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr2 = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M t2_pre n )) (PreH37 : (rc_valid M )) (PreH38 : (store_type M t1_pre tr1 )) (PreH39 : (store_type M t2_pre tr2 )) (PreH40 : (repr_rel_node s tr1 tr1 )) (PreH41 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (retval <> 0) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
).

Definition atype_unify1_partial_solve_wit_7_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t2_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (retval_3 <> 0)) (PreH10 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M_post_2 M_post )) (PreH13 : (rc_reservations_same M_post_2 M_post )) (PreH14 : (node_at M_post_2 t2_pre n )) (PreH15 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_2 t2_pre tr2 )) (PreH17 : (store_type M_post_2 t1_pre tr1 )) (PreH18 : (store_type M_post_2 retval_2 tr )) (PreH19 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH20 : (rc_valid M_post_2 )) (PreH21 : (rc_preserves M M_post_2 )) (PreH22 : (store_type M_post_2 retval tr_out )) (PreH23 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M retval M_post_2 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s (node_a (n)) tr )) (PreH27 : (store_type M retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr2 = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M t2_pre n )) (PreH37 : (rc_valid M )) (PreH38 : (store_type M t1_pre tr1 )) (PreH39 : (store_type M t2_pre tr2 )) (PreH40 : (repr_rel_node s tr1 tr1 )) (PreH41 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ (retval <> 0) ”
.

Definition atype_unify1_partial_solve_wit_7_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <= INT_MAX)) (PreH2 : (retval_3 >= INT_MIN)) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (node_at M_post t2_pre n )) (PreH5 : (store_type M_post retval tr_out )) (PreH6 : (store_type M_post retval_2 tr )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (retval_3 <> 0)) (PreH10 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M_post_2 M_post )) (PreH13 : (rc_reservations_same M_post_2 M_post )) (PreH14 : (node_at M_post_2 t2_pre n )) (PreH15 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH16 : (store_type M_post_2 t2_pre tr2 )) (PreH17 : (store_type M_post_2 t1_pre tr1 )) (PreH18 : (store_type M_post_2 retval_2 tr )) (PreH19 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH20 : (rc_valid M_post_2 )) (PreH21 : (rc_preserves M M_post_2 )) (PreH22 : (store_type M_post_2 retval tr_out )) (PreH23 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH24 : (retain_rel M retval M_post_2 )) (PreH25 : (retval_2 <> 0)) (PreH26 : (solution_at s (node_a (n)) tr )) (PreH27 : (store_type M retval_2 tr )) (PreH28 : ((node_a (n)) < 100)) (PreH29 : (0 <= (node_a (n)))) (PreH30 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH31 : (n = (Node (3) ((node_a (n))) (0)))) (PreH32 : (tr2 = (TVar ((node_a (n)))))) (PreH33 : ((node_tag (n)) = 3)) (PreH34 : ((node_tag (n)) <= 3)) (PreH35 : (0 <= (node_tag (n)))) (PreH36 : (node_at M t2_pre n )) (PreH37 : (rc_valid M )) (PreH38 : (store_type M t1_pre tr1 )) (PreH39 : (store_type M t2_pre tr2 )) (PreH40 : (repr_rel_node s tr1 tr1 )) (PreH41 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH42 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval_3)
  **  ((( &( "tp" ) )) # Ptr  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> retval)
|--
  “ ((rc_reserved (M_post) (retval)) > 0) ”
.

Definition atype_unify1_partial_solve_wit_7_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (tr: TypeTree) (retval_2: Z) (tr_out: TypeTree) (M_post_2: RcState) (retval: Z) (M_post: RcState) (s_post: sol) (retval_3: Z) (PreH1 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH2 : (node_at M_post t2_pre n )) (PreH3 : (store_type M_post retval tr_out )) (PreH4 : (store_type M_post retval_2 tr )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (retval_3 <> 0)) (PreH8 : (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M_post_2 M_post )) (PreH11 : (rc_reservations_same M_post_2 M_post )) (PreH12 : (node_at M_post_2 t2_pre n )) (PreH13 : (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (store_type M_post_2 t2_pre tr2 )) (PreH15 : (store_type M_post_2 t1_pre tr1 )) (PreH16 : (store_type M_post_2 retval_2 tr )) (PreH17 : (repr_result M s (node_a (n)) retval M_post_2 )) (PreH18 : (rc_valid M_post_2 )) (PreH19 : (rc_preserves M M_post_2 )) (PreH20 : (store_type M_post_2 retval tr_out )) (PreH21 : (repr_rel_node s (TVar ((node_a (n)))) tr_out )) (PreH22 : (retain_rel M retval M_post_2 )) (PreH23 : (retval_2 <> 0)) (PreH24 : (solution_at s (node_a (n)) tr )) (PreH25 : (store_type M retval_2 tr )) (PreH26 : ((node_a (n)) < 100)) (PreH27 : (0 <= (node_a (n)))) (PreH28 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH29 : (n = (Node (3) ((node_a (n))) (0)))) (PreH30 : (tr2 = (TVar ((node_a (n)))))) (PreH31 : ((node_tag (n)) = 3)) (PreH32 : ((node_tag (n)) <= 3)) (PreH33 : (0 <= (node_tag (n)))) (PreH34 : (node_at M t2_pre n )) (PreH35 : (rc_valid M )) (PreH36 : (store_type M t1_pre tr1 )) (PreH37 : (store_type M t2_pre tr2 )) (PreH38 : (repr_rel_node s tr1 tr1 )) (PreH39 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH40 : (retval_2 <> 0)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (node_at M_post t2_pre n ) ”
  &&  “ (store_type M_post retval tr_out ) ”
  &&  “ (store_type M_post retval_2 tr ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (retval_3 <> 0) ”
  &&  “ (infer_result 2 M_post_2 s t1_pre retval retval_3 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_post_2 M_post ) ”
  &&  “ (rc_reservations_same M_post_2 M_post ) ”
  &&  “ (node_at M_post_2 t2_pre n ) ”
  &&  “ (node_at M_post_2 t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post_2 t2_pre tr2 ) ”
  &&  “ (store_type M_post_2 t1_pre tr1 ) ”
  &&  “ (store_type M_post_2 retval_2 tr ) ”
  &&  “ (repr_result M s (node_a (n)) retval M_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (store_type M_post_2 retval tr_out ) ”
  &&  “ (repr_rel_node s (TVar ((node_a (n)))) tr_out ) ”
  &&  “ (retain_rel M retval M_post_2 ) ”
  &&  “ (retval_2 <> 0) ”
  &&  “ (solution_at s (node_a (n)) tr ) ”
  &&  “ (store_type M retval_2 tr ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval_2 <> 0) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify1_partial_solve_wit_7 := atype_unify1_partial_solve_wit_7_pure -> atype_unify1_partial_solve_wit_7_aux.

Definition atype_unify1_partial_solve_wit_8_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH17 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH5 : ((node_a (n)) < 100)) (PreH6 : (0 <= (node_a (n)))) (PreH7 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (n = (Node (3) ((node_a (n))) (0)))) (PreH9 : (tr2 = (TVar ((node_a (n)))))) (PreH10 : ((node_tag (n)) = 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t2_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH19 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
).

Definition atype_unify1_partial_solve_wit_8_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH5 : ((node_a (n)) < 100)) (PreH6 : (0 <= (node_a (n)))) (PreH7 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (n = (Node (3) ((node_a (n))) (0)))) (PreH9 : (tr2 = (TVar ((node_a (n)))))) (PreH10 : ((node_tag (n)) = 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t2_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH19 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (repr_rel_node s tr2 tr2 ) ”
.

Definition atype_unify1_partial_solve_wit_8_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : ((node_a (n)) <= INT_MAX)) (PreH2 : ((node_a (n)) >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH5 : ((node_a (n)) < 100)) (PreH6 : (0 <= (node_a (n)))) (PreH7 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (n = (Node (3) ((node_a (n))) (0)))) (PreH9 : (tr2 = (TVar ((node_a (n)))))) (PreH10 : ((node_tag (n)) = 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t2_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH19 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
.

Definition atype_unify1_partial_solve_wit_8_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr ))) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (rc_capacity 1 M s t1_pre t2_pre )) (PreH17 : (retval = 0)),
  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (retval = 0) ”
  &&  “ forall (tr: TypeTree), ~((solution_at s (node_a (n)) tr )) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  “ (retval = 0) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify1_partial_solve_wit_8 := atype_unify1_partial_solve_wit_8_pure -> atype_unify1_partial_solve_wit_8_aux.

Definition atype_unify1_partial_solve_wit_9_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t2_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M t2_pre n )) (PreH7 : (rc_valid M )) (PreH8 : (store_type M t1_pre tr1 )) (PreH9 : (store_type M t2_pre tr2 )) (PreH10 : (repr_rel_node s tr1 tr1 )) (PreH11 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
).

Definition atype_unify1_partial_solve_wit_9_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M t2_pre n )) (PreH7 : (rc_valid M )) (PreH8 : (store_type M t1_pre tr1 )) (PreH9 : (store_type M t2_pre tr2 )) (PreH10 : (repr_rel_node s tr1 tr1 )) (PreH11 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (repr_rel_node s tr2 tr2 ) ”
.

Definition atype_unify1_partial_solve_wit_9_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M t2_pre n )) (PreH7 : (rc_valid M )) (PreH8 : (store_type M t1_pre tr1 )) (PreH9 : (store_type M t2_pre tr2 )) (PreH10 : (repr_rel_node s tr1 tr1 )) (PreH11 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
.

Definition atype_unify1_partial_solve_wit_9_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t2_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (rc_capacity 1 M s t1_pre t2_pre )),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (rc_capacity 1 M s t1_pre t2_pre ) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify1_partial_solve_wit_9 := atype_unify1_partial_solve_wit_9_pure -> atype_unify1_partial_solve_wit_9_aux.

(*----- Function atype_unify2 -----*)

Definition atype_unify2_safety_wit_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (PreH1 : (rc_valid M )) (PreH2 : (store_type M t1_pre tr1 )) (PreH3 : (store_type M t2_pre tr2 )) (PreH4 : (repr_rel_node s tr1 tr1 )) (PreH5 : (repr_rel_node s tr2 tr2 )) (PreH6 : (rc_capacity 2 M s t1_pre t2_pre )),
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((False \/ (True /\ (t1_pre = t2_pre))) \/ (True /\ (t1_pre <> t2_pre))) ”
.

Definition atype_unify2_safety_wit_2_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= 3)) (PreH2 : (0 <= (node_tag (n)))) (PreH3 : (node_at M t1_pre n )) (PreH4 : (rc_valid M )) (PreH5 : (store_type M t1_pre tr1 )) (PreH6 : (store_type M t2_pre tr2 )) (PreH7 : (repr_rel_node s tr1 tr1 )) (PreH8 : (repr_rel_node s tr2 tr2 )) (PreH9 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH10 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify2_safety_wit_3_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <= 3)) (PreH2 : (0 <= (node_tag (n)))) (PreH3 : (node_at M t1_pre n )) (PreH4 : (rc_valid M )) (PreH5 : (store_type M t1_pre tr1 )) (PreH6 : (store_type M t2_pre tr2 )) (PreH7 : (repr_rel_node s tr1 tr1 )) (PreH8 : (repr_rel_node s tr2 tr2 )) (PreH9 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH10 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify2_safety_wit_4_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_5_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_6_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)) (PreH19 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_7_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)) (PreH19 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_8_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_9_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_10_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post) (retval_2)) )) (PreH9 : (node_at M_post t1_pre n )) (PreH10 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post t2_pre tr2 )) (PreH12 : (store_type M_post t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post )) (PreH15 : (rc_valid M_post )) (PreH16 : (rc_preserves M M_post )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre = t2_pre)) (PreH35 : (retval = 0)),
  (store_world (rc_publish (M_post) (retval_2)) )
  **  (store_solution (rc_publish (M_post) (retval_2)) ( &( "res" ) ) (sol_update (s) ((node_a (n))) (tr2)) )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_11_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post) (retval_2)) )) (PreH9 : (node_at M_post t1_pre n )) (PreH10 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post t2_pre tr2 )) (PreH12 : (store_type M_post t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post )) (PreH15 : (rc_valid M_post )) (PreH16 : (rc_preserves M M_post )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre <> t2_pre)) (PreH35 : (retval = 0)),
  (store_world (rc_publish (M_post) (retval_2)) )
  **  (store_solution (rc_publish (M_post) (retval_2)) ( &( "res" ) ) (sol_update (s) ((node_a (n))) (tr2)) )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_12_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t1_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (repr_rel_node s tr2 tr2 )) (PreH10 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH11 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify2_safety_wit_13_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n_2)) <= 3)) (PreH2 : (0 <= (node_tag (n_2)))) (PreH3 : (node_at M t2_pre n_2 )) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <= 3)) (PreH6 : (0 <= (node_tag (n)))) (PreH7 : (node_at M t1_pre n )) (PreH8 : (rc_valid M )) (PreH9 : (store_type M t1_pre tr1 )) (PreH10 : (store_type M t2_pre tr2 )) (PreH11 : (repr_rel_node s tr1 tr1 )) (PreH12 : (repr_rel_node s tr2 tr2 )) (PreH13 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH14 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify2_safety_wit_14_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 3)) (PreH2 : ((node_tag (n)) <> 3)) (PreH3 : ((node_tag (n)) <= 3)) (PreH4 : (0 <= (node_tag (n)))) (PreH5 : (node_at M t1_pre n )) (PreH6 : (rc_valid M )) (PreH7 : (store_type M t1_pre tr1 )) (PreH8 : (store_type M t2_pre tr2 )) (PreH9 : (repr_rel_node s tr1 tr1 )) (PreH10 : (repr_rel_node s tr2 tr2 )) (PreH11 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH12 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ False ”
.

Definition atype_unify2_safety_wit_15_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_16_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t2_pre n_2 )) (PreH12 : ((node_tag (n)) <> 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval <> 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_17_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_18_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (M_post: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post) (retval_2)) t2_pre n_2 )) (PreH3 : (node_at (rc_publish (M_post) (retval_2)) t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH4 : (store_type (rc_publish (M_post) (retval_2)) t2_pre tr2 )) (PreH5 : (store_type (rc_publish (M_post) (retval_2)) t1_pre tr1 )) (PreH6 : (store_type M_post retval_2 tr1 )) (PreH7 : (rc_valid (rc_publish (M_post) (retval_2)) )) (PreH8 : (rc_preserves M (rc_publish (M_post) (retval_2)) )) (PreH9 : (rc_reservations_same M (rc_publish (M_post) (retval_2)) )) (PreH10 : (node_at M_post t1_pre n )) (PreH11 : (node_at M_post t2_pre n_2 )) (PreH12 : (node_at M_post t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH13 : (store_type M_post t2_pre tr2 )) (PreH14 : (store_type M_post t1_pre tr1 )) (PreH15 : (retval_2 = t1_pre)) (PreH16 : (retain_rel M t1_pre M_post )) (PreH17 : (rc_valid M_post )) (PreH18 : (rc_preserves M M_post )) (PreH19 : (retval = 0)) (PreH20 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH21 : ((node_a (n_2)) < 100)) (PreH22 : (0 <= (node_a (n_2)))) (PreH23 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH24 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH25 : (tr2 = (TVar ((node_a (n_2)))))) (PreH26 : ((node_tag (n_2)) = 3)) (PreH27 : ((node_tag (n_2)) <= 3)) (PreH28 : (0 <= (node_tag (n_2)))) (PreH29 : (node_at M t2_pre n_2 )) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre <> t2_pre)) (PreH41 : (retval = 0)),
  (store_world (rc_publish (M_post) (retval_2)) )
  **  (store_solution (rc_publish (M_post) (retval_2)) ( &( "res" ) ) (sol_update (s) ((node_a (n_2))) (tr1)) )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_19_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> (node_tag (n_2)))) (PreH2 : ((node_tag (n_2)) <> 3)) (PreH3 : ((node_tag (n_2)) <= 3)) (PreH4 : (0 <= (node_tag (n_2)))) (PreH5 : (node_at M t2_pre n_2 )) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition atype_unify2_safety_wit_20_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) = (node_tag (n_2)))) (PreH2 : ((node_tag (n_2)) <> 3)) (PreH3 : ((node_tag (n_2)) <= 3)) (PreH4 : (0 <= (node_tag (n_2)))) (PreH5 : (node_at M t2_pre n_2 )) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_21_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <> 3)) (PreH3 : ((node_tag (n)) <= 3)) (PreH4 : (0 <= (node_tag (n)))) (PreH5 : (node_at M t1_pre n )) (PreH6 : (rc_valid M )) (PreH7 : (store_type M t1_pre tr1 )) (PreH8 : (store_type M t2_pre tr2 )) (PreH9 : (repr_rel_node s tr1 tr1 )) (PreH10 : (repr_rel_node s tr2 tr2 )) (PreH11 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH12 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_22_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t2_pre n_2 )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (store_type M_post (node_a (n_2)) a_2 )) (PreH8 : (store_type M_post (node_b (n_2)) b_2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel a a_2 s s_post )) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TArrow (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TArrow (a) (b)))) (PreH21 : ((node_tag (n)) = 1)) (PreH22 : ((node_tag (n)) = (node_tag (n_2)))) (PreH23 : ((node_tag (n_2)) <> 3)) (PreH24 : ((node_tag (n_2)) <= 3)) (PreH25 : (0 <= (node_tag (n_2)))) (PreH26 : (node_at M t2_pre n_2 )) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <= 3)) (PreH29 : (0 <= (node_tag (n)))) (PreH30 : (node_at M t1_pre n )) (PreH31 : (rc_valid M )) (PreH32 : (store_type M t1_pre tr1 )) (PreH33 : (store_type M t2_pre tr2 )) (PreH34 : (repr_rel_node s tr1 tr1 )) (PreH35 : (repr_rel_node s tr2 tr2 )) (PreH36 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH37 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_23_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t2_pre n_2 )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (store_type M_post (node_a (n_2)) a_2 )) (PreH8 : (store_type M_post (node_b (n_2)) b_2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (rc_reservations_same M M_post )) (PreH14 : (store_type M (node_b (n_2)) b_2 )) (PreH15 : (store_type M (node_a (n_2)) a_2 )) (PreH16 : (tr2 = (TArrow (a_2) (b_2)))) (PreH17 : (store_type M (node_b (n)) b )) (PreH18 : (store_type M (node_a (n)) a )) (PreH19 : (tr1 = (TArrow (a) (b)))) (PreH20 : ((node_tag (n)) = 1)) (PreH21 : ((node_tag (n)) = (node_tag (n_2)))) (PreH22 : ((node_tag (n_2)) <> 3)) (PreH23 : ((node_tag (n_2)) <= 3)) (PreH24 : (0 <= (node_tag (n_2)))) (PreH25 : (node_at M t2_pre n_2 )) (PreH26 : ((node_tag (n)) <> 3)) (PreH27 : ((node_tag (n)) <= 3)) (PreH28 : (0 <= (node_tag (n)))) (PreH29 : (node_at M t1_pre n )) (PreH30 : (rc_valid M )) (PreH31 : (store_type M t1_pre tr1 )) (PreH32 : (store_type M t2_pre tr2 )) (PreH33 : (repr_rel_node s tr1 tr1 )) (PreH34 : (repr_rel_node s tr2 tr2 )) (PreH35 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH36 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_24_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (store_type M_post t2_pre tr2 )) (PreH3 : (store_type M_post t1_pre tr1 )) (PreH4 : (store_type M_post (node_a (n)) a )) (PreH5 : (store_type M_post (node_b (n)) b )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel a a s s_post )) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M M_post )) (PreH11 : (rc_reservations_same M M_post )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TArrow (a) (b)))) (PreH15 : ((node_tag (n)) = 1)) (PreH16 : ((node_tag (n)) <> 3)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_25_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (store_type M_post t2_pre tr2 )) (PreH3 : (store_type M_post t1_pre tr1 )) (PreH4 : (store_type M_post (node_a (n)) a )) (PreH5 : (store_type M_post (node_b (n)) b )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH8 : (rc_valid M_post )) (PreH9 : (rc_preserves M M_post )) (PreH10 : (rc_reservations_same M M_post )) (PreH11 : (store_type M (node_b (n)) b )) (PreH12 : (store_type M (node_a (n)) a )) (PreH13 : (tr1 = (TArrow (a) (b)))) (PreH14 : ((node_tag (n)) = 1)) (PreH15 : ((node_tag (n)) <> 3)) (PreH16 : ((node_tag (n)) <> 3)) (PreH17 : ((node_tag (n)) <= 3)) (PreH18 : (0 <= (node_tag (n)))) (PreH19 : (node_at M t1_pre n )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_26_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TArrow (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TArrow (a) (b)))) (PreH22 : ((node_tag (n)) = 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_27_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TArrow (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TArrow (a) (b)))) (PreH21 : ((node_tag (n)) = 1)) (PreH22 : ((node_tag (n)) = (node_tag (n_2)))) (PreH23 : ((node_tag (n_2)) <> 3)) (PreH24 : ((node_tag (n_2)) <= 3)) (PreH25 : (0 <= (node_tag (n_2)))) (PreH26 : (node_at M t2_pre n_2 )) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <= 3)) (PreH29 : (0 <= (node_tag (n)))) (PreH30 : (node_at M t1_pre n )) (PreH31 : (rc_valid M )) (PreH32 : (store_type M t1_pre tr1 )) (PreH33 : (store_type M t2_pre tr2 )) (PreH34 : (repr_rel_node s tr1 tr1 )) (PreH35 : (repr_rel_node s tr2 tr2 )) (PreH36 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH37 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_28_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TArrow (a) (b)))) (PreH16 : ((node_tag (n)) = 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_29_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M M_post )) (PreH11 : (rc_reservations_same M M_post )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TArrow (a) (b)))) (PreH15 : ((node_tag (n)) = 1)) (PreH16 : ((node_tag (n)) <> 3)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_30_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 1)) (PreH2 : ((node_tag (n)) <> 3)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M t1_pre n )) (PreH7 : (rc_valid M )) (PreH8 : (store_type M t1_pre tr1 )) (PreH9 : (store_type M t2_pre tr2 )) (PreH10 : (repr_rel_node s tr1 tr1 )) (PreH11 : (repr_rel_node s tr2 tr2 )) (PreH12 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH13 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition atype_unify2_safety_wit_31_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> 1)) (PreH2 : ((node_tag (n)) = (node_tag (n_2)))) (PreH3 : ((node_tag (n_2)) <> 3)) (PreH4 : ((node_tag (n_2)) <= 3)) (PreH5 : (0 <= (node_tag (n_2)))) (PreH6 : (node_at M t2_pre n_2 )) (PreH7 : ((node_tag (n)) <> 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition atype_unify2_safety_wit_32_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (store_type M_post t2_pre tr2 )) (PreH3 : (store_type M_post t1_pre tr1 )) (PreH4 : (store_type M_post (node_a (n)) a )) (PreH5 : (store_type M_post (node_b (n)) b )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel a a s s_post )) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M M_post )) (PreH11 : (rc_reservations_same M M_post )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TApply (a) (b)))) (PreH15 : ((node_tag (n)) = 2)) (PreH16 : ((node_tag (n)) <> 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_33_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (store_type M_post t2_pre tr2 )) (PreH3 : (store_type M_post t1_pre tr1 )) (PreH4 : (store_type M_post (node_a (n)) a )) (PreH5 : (store_type M_post (node_b (n)) b )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH8 : (rc_valid M_post )) (PreH9 : (rc_preserves M M_post )) (PreH10 : (rc_reservations_same M M_post )) (PreH11 : (store_type M (node_b (n)) b )) (PreH12 : (store_type M (node_a (n)) a )) (PreH13 : (tr1 = (TApply (a) (b)))) (PreH14 : ((node_tag (n)) = 2)) (PreH15 : ((node_tag (n)) <> 1)) (PreH16 : ((node_tag (n)) <> 3)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_34_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t2_pre n_2 )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (store_type M_post (node_a (n_2)) a_2 )) (PreH8 : (store_type M_post (node_b (n_2)) b_2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel a a_2 s s_post )) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TApply (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TApply (a) (b)))) (PreH21 : ((node_tag (n)) = 2)) (PreH22 : ((node_tag (n)) <> 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_35_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t2_pre n_2 )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (store_type M_post (node_a (n_2)) a_2 )) (PreH8 : (store_type M_post (node_b (n_2)) b_2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (rc_reservations_same M M_post )) (PreH14 : (store_type M (node_b (n_2)) b_2 )) (PreH15 : (store_type M (node_a (n_2)) a_2 )) (PreH16 : (tr2 = (TApply (a_2) (b_2)))) (PreH17 : (store_type M (node_b (n)) b )) (PreH18 : (store_type M (node_a (n)) a )) (PreH19 : (tr1 = (TApply (a) (b)))) (PreH20 : ((node_tag (n)) = 2)) (PreH21 : ((node_tag (n)) <> 1)) (PreH22 : ((node_tag (n)) = (node_tag (n_2)))) (PreH23 : ((node_tag (n_2)) <> 3)) (PreH24 : ((node_tag (n_2)) <= 3)) (PreH25 : (0 <= (node_tag (n_2)))) (PreH26 : (node_at M t2_pre n_2 )) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <= 3)) (PreH29 : (0 <= (node_tag (n)))) (PreH30 : (node_at M t1_pre n )) (PreH31 : (rc_valid M )) (PreH32 : (store_type M t1_pre tr1 )) (PreH33 : (store_type M t2_pre tr2 )) (PreH34 : (repr_rel_node s tr1 tr1 )) (PreH35 : (repr_rel_node s tr2 tr2 )) (PreH36 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH37 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_36_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TApply (a) (b)))) (PreH16 : ((node_tag (n)) = 2)) (PreH17 : ((node_tag (n)) <> 1)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <> 3)) (PreH20 : ((node_tag (n)) <= 3)) (PreH21 : (0 <= (node_tag (n)))) (PreH22 : (node_at M t1_pre n )) (PreH23 : (rc_valid M )) (PreH24 : (store_type M t1_pre tr1 )) (PreH25 : (store_type M t2_pre tr2 )) (PreH26 : (repr_rel_node s tr1 tr1 )) (PreH27 : (repr_rel_node s tr2 tr2 )) (PreH28 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH29 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_37_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH9 : (rc_valid M_post )) (PreH10 : (rc_preserves M M_post )) (PreH11 : (rc_reservations_same M M_post )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TApply (a) (b)))) (PreH15 : ((node_tag (n)) = 2)) (PreH16 : ((node_tag (n)) <> 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_38_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TApply (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TApply (a) (b)))) (PreH22 : ((node_tag (n)) = 2)) (PreH23 : ((node_tag (n)) <> 1)) (PreH24 : ((node_tag (n)) = (node_tag (n_2)))) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t2_pre n_2 )) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_39_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TApply (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TApply (a) (b)))) (PreH21 : ((node_tag (n)) = 2)) (PreH22 : ((node_tag (n)) <> 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_40_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_41_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) = (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_42_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) <> (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition atype_unify2_entail_wit_1_1_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)) (PreH19 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)) (PreH19 : (retval = 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n))) (0)) = n) ”
  &&  emp
).

Definition atype_unify2_entail_wit_1_1_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)) (PreH19 : (retval = 0)),
  ((Node (3) ((node_a (n))) (0)) = n)
.

Definition atype_unify2_entail_wit_1_2_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  (“ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
  ||
  (EX (n_2: TypeNode),
  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n_2)) tr2 ) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
.

Definition atype_unify2_entail_wit_1_3_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr2 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t1_pre n_2 )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)) (PreH19 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n_2)) tr2 ) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr2 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t1_pre n_2 )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)) (PreH19 : (retval = 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n_2))) (0)) = n_2) ”
  &&  emp
).

Definition atype_unify2_entail_wit_1_3_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr2 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t1_pre n_2 )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)) (PreH19 : (retval = 0)),
  ((Node (3) ((node_a (n_2))) (0)) = n_2)
.

Definition atype_unify2_entail_wit_1_4_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t1_pre n_2 )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  (EX (n: TypeNode),
  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
  ||
  (“ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n_2)) tr2 ) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
.

Definition atype_unify2_entail_wit_2_1_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)) (PreH19 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  (“ (retval <> 0) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
  ||
  (EX (n_2: TypeNode),
  “ (retval <> 0) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
.

Definition atype_unify2_entail_wit_2_2_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval <> 0) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n))) (0)) = n) ”
  &&  emp
).

Definition atype_unify2_entail_wit_2_2_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  ((Node (3) ((node_a (n))) (0)) = n)
.

Definition atype_unify2_entail_wit_2_3_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr2 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t1_pre n_2 )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)) (PreH19 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  (EX (n: TypeNode),
  “ (retval <> 0) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
  ||
  (“ (retval <> 0) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s ))
.

Definition atype_unify2_entail_wit_2_4_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t1_pre n_2 )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval <> 0) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t1_pre n_2 )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n_2))) (0)) = n_2) ”
  &&  emp
).

Definition atype_unify2_entail_wit_2_4_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t1_pre n_2 )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  ((Node (3) ((node_a (n_2))) (0)) = n_2)
.

Definition atype_unify2_entail_wit_3_1_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t2_pre n_2 )) (PreH12 : ((node_tag (n)) <> 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n_2)) tr1 ) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t2_pre n_2 )) (PreH12 : ((node_tag (n)) <> 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n_2))) (0)) = n_2) ”
  &&  emp
).

Definition atype_unify2_entail_wit_3_1_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t2_pre n_2 )) (PreH12 : ((node_tag (n)) <> 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  ((Node (3) ((node_a (n_2))) (0)) = n_2)
.

Definition atype_unify2_entail_wit_3_2_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n_2)) tr1 ) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_entail_wit_4_1_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH3 : ((node_a (n_2)) < 100)) (PreH4 : (0 <= (node_a (n_2)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH6 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n_2)))))) (PreH8 : ((node_tag (n_2)) = 3)) (PreH9 : ((node_tag (n_2)) <= 3)) (PreH10 : (0 <= (node_tag (n_2)))) (PreH11 : (node_at M t2_pre n_2 )) (PreH12 : ((node_tag (n)) <> 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval <> 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval <> 0) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_entail_wit_4_2_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (retval <> 0) ”
  &&  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval <> 0) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  TT && emp 
|--
  “ ((Node (3) ((node_a (n_2))) (0)) = n_2) ”
  &&  emp
).

Definition atype_unify2_entail_wit_4_2_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  ((Node (3) ((node_a (n_2))) (0)) = n_2)
.

Definition atype_unify2_return_wit_1_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) <> (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (2 <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 2 M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) <> (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M ) ”
  &&  “ (rc_preserves M M ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 2 M s ) ”
  &&  emp
).

Definition atype_unify2_return_wit_1_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) <> (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  (rc_reservations_same M M )
.

Definition atype_unify2_return_wit_1_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) <> (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  (rc_preserves M M )
.

Definition atype_unify2_return_wit_1_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) <> (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre 2 M s )
.

Definition atype_unify2_return_wit_2_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (0 = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M ) ”
  &&  “ (rc_preserves M M ) ”
  &&  “ (infer_result 2 M s t1_pre t1_pre 0 M s ) ”
  &&  “ (unify_rel tr1 tr2 s s ) ”
  &&  emp
).

Definition atype_unify2_return_wit_2_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  (rc_reservations_same M M )
.

Definition atype_unify2_return_wit_2_same_node_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  (rc_preserves M M )
.

Definition atype_unify2_return_wit_2_same_node_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  (infer_result 2 M s t1_pre t1_pre 0 M s )
.

Definition atype_unify2_return_wit_2_same_node_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  (unify_rel tr1 tr2 s s )
.

Definition atype_unify2_return_wit_3_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) = (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (0 = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) = (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M ) ”
  &&  “ (rc_preserves M M ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M s ) ”
  &&  “ (unify_rel tr1 tr2 s s ) ”
  &&  emp
).

Definition atype_unify2_return_wit_3_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) = (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  (rc_reservations_same M M )
.

Definition atype_unify2_return_wit_3_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) = (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  (rc_preserves M M )
.

Definition atype_unify2_return_wit_3_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) = (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre 0 M s )
.

Definition atype_unify2_return_wit_3_distinct_nodes_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_a (n)) = (node_a (n_2)))) (PreH2 : ((node_tag (n)) = 0)) (PreH3 : ((node_tag (n)) <> 2)) (PreH4 : ((node_tag (n)) <> 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  (unify_rel tr1 tr2 s s )
.

Definition atype_unify2_return_wit_4_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TApply (a) (b)))) (PreH27 : ((node_tag (n)) = 2)) (PreH28 : ((node_tag (n)) <> 1)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre = t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TApply (a) (b)))) (PreH27 : ((node_tag (n)) = 2)) (PreH28 : ((node_tag (n)) <> 1)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre = t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t1_pre 0 M_post_4 s_post_4 ) ”
  &&  “ (unify_rel tr1 tr2 s s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_4_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TApply (a) (b)))) (PreH27 : ((node_tag (n)) = 2)) (PreH28 : ((node_tag (n)) <> 1)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre = t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_4_same_node_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TApply (a) (b)))) (PreH27 : ((node_tag (n)) = 2)) (PreH28 : ((node_tag (n)) <> 1)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre = t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_4_same_node_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TApply (a) (b)))) (PreH27 : ((node_tag (n)) = 2)) (PreH28 : ((node_tag (n)) <> 1)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre = t2_pre)),
  (infer_result 2 M s t1_pre t1_pre 0 M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_4_same_node_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TApply (a) (b)))) (PreH27 : ((node_tag (n)) = 2)) (PreH28 : ((node_tag (n)) <> 1)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre = t2_pre)),
  (unify_rel tr1 tr2 s s_post_4 )
.

Definition atype_unify2_return_wit_5_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TApply (a) (b)))) (PreH26 : ((node_tag (n)) = 2)) (PreH27 : ((node_tag (n)) <> 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TApply (a) (b)))) (PreH26 : ((node_tag (n)) = 2)) (PreH27 : ((node_tag (n)) <> 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t1_pre retval M_post_4 s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_5_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TApply (a) (b)))) (PreH26 : ((node_tag (n)) = 2)) (PreH27 : ((node_tag (n)) <> 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_5_same_node_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TApply (a) (b)))) (PreH26 : ((node_tag (n)) = 2)) (PreH27 : ((node_tag (n)) <> 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_5_same_node_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TApply (a) (b)))) (PreH26 : ((node_tag (n)) = 2)) (PreH27 : ((node_tag (n)) <> 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (infer_result 2 M s t1_pre t1_pre retval M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_6_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TApply (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TApply (a) (b)))) (PreH36 : ((node_tag (n)) = 2)) (PreH37 : ((node_tag (n)) <> 1)) (PreH38 : ((node_tag (n)) = (node_tag (n_2)))) (PreH39 : ((node_tag (n_2)) <> 3)) (PreH40 : ((node_tag (n_2)) <= 3)) (PreH41 : (0 <= (node_tag (n_2)))) (PreH42 : (node_at M t2_pre n_2 )) (PreH43 : ((node_tag (n)) <> 3)) (PreH44 : ((node_tag (n)) <= 3)) (PreH45 : (0 <= (node_tag (n)))) (PreH46 : (node_at M t1_pre n )) (PreH47 : (rc_valid M )) (PreH48 : (store_type M t1_pre tr1 )) (PreH49 : (store_type M t2_pre tr2 )) (PreH50 : (repr_rel_node s tr1 tr1 )) (PreH51 : (repr_rel_node s tr2 tr2 )) (PreH52 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH53 : (t1_pre <> t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TApply (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TApply (a) (b)))) (PreH36 : ((node_tag (n)) = 2)) (PreH37 : ((node_tag (n)) <> 1)) (PreH38 : ((node_tag (n)) = (node_tag (n_2)))) (PreH39 : ((node_tag (n_2)) <> 3)) (PreH40 : ((node_tag (n_2)) <= 3)) (PreH41 : (0 <= (node_tag (n_2)))) (PreH42 : (node_at M t2_pre n_2 )) (PreH43 : ((node_tag (n)) <> 3)) (PreH44 : ((node_tag (n)) <= 3)) (PreH45 : (0 <= (node_tag (n)))) (PreH46 : (node_at M t1_pre n )) (PreH47 : (rc_valid M )) (PreH48 : (store_type M t1_pre tr1 )) (PreH49 : (store_type M t2_pre tr2 )) (PreH50 : (repr_rel_node s tr1 tr1 )) (PreH51 : (repr_rel_node s tr2 tr2 )) (PreH52 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH53 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M_post_4 s_post_4 ) ”
  &&  “ (unify_rel tr1 tr2 s s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_6_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TApply (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TApply (a) (b)))) (PreH36 : ((node_tag (n)) = 2)) (PreH37 : ((node_tag (n)) <> 1)) (PreH38 : ((node_tag (n)) = (node_tag (n_2)))) (PreH39 : ((node_tag (n_2)) <> 3)) (PreH40 : ((node_tag (n_2)) <= 3)) (PreH41 : (0 <= (node_tag (n_2)))) (PreH42 : (node_at M t2_pre n_2 )) (PreH43 : ((node_tag (n)) <> 3)) (PreH44 : ((node_tag (n)) <= 3)) (PreH45 : (0 <= (node_tag (n)))) (PreH46 : (node_at M t1_pre n )) (PreH47 : (rc_valid M )) (PreH48 : (store_type M t1_pre tr1 )) (PreH49 : (store_type M t2_pre tr2 )) (PreH50 : (repr_rel_node s tr1 tr1 )) (PreH51 : (repr_rel_node s tr2 tr2 )) (PreH52 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH53 : (t1_pre <> t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_6_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TApply (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TApply (a) (b)))) (PreH36 : ((node_tag (n)) = 2)) (PreH37 : ((node_tag (n)) <> 1)) (PreH38 : ((node_tag (n)) = (node_tag (n_2)))) (PreH39 : ((node_tag (n_2)) <> 3)) (PreH40 : ((node_tag (n_2)) <= 3)) (PreH41 : (0 <= (node_tag (n_2)))) (PreH42 : (node_at M t2_pre n_2 )) (PreH43 : ((node_tag (n)) <> 3)) (PreH44 : ((node_tag (n)) <= 3)) (PreH45 : (0 <= (node_tag (n)))) (PreH46 : (node_at M t1_pre n )) (PreH47 : (rc_valid M )) (PreH48 : (store_type M t1_pre tr1 )) (PreH49 : (store_type M t2_pre tr2 )) (PreH50 : (repr_rel_node s tr1 tr1 )) (PreH51 : (repr_rel_node s tr2 tr2 )) (PreH52 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH53 : (t1_pre <> t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_6_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TApply (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TApply (a) (b)))) (PreH36 : ((node_tag (n)) = 2)) (PreH37 : ((node_tag (n)) <> 1)) (PreH38 : ((node_tag (n)) = (node_tag (n_2)))) (PreH39 : ((node_tag (n_2)) <> 3)) (PreH40 : ((node_tag (n_2)) <= 3)) (PreH41 : (0 <= (node_tag (n_2)))) (PreH42 : (node_at M t2_pre n_2 )) (PreH43 : ((node_tag (n)) <> 3)) (PreH44 : ((node_tag (n)) <= 3)) (PreH45 : (0 <= (node_tag (n)))) (PreH46 : (node_at M t1_pre n )) (PreH47 : (rc_valid M )) (PreH48 : (store_type M t1_pre tr1 )) (PreH49 : (store_type M t2_pre tr2 )) (PreH50 : (repr_rel_node s tr1 tr1 )) (PreH51 : (repr_rel_node s tr2 tr2 )) (PreH52 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH53 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre 0 M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_6_distinct_nodes_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TApply (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TApply (a) (b)))) (PreH36 : ((node_tag (n)) = 2)) (PreH37 : ((node_tag (n)) <> 1)) (PreH38 : ((node_tag (n)) = (node_tag (n_2)))) (PreH39 : ((node_tag (n_2)) <> 3)) (PreH40 : ((node_tag (n_2)) <= 3)) (PreH41 : (0 <= (node_tag (n_2)))) (PreH42 : (node_at M t2_pre n_2 )) (PreH43 : ((node_tag (n)) <> 3)) (PreH44 : ((node_tag (n)) <= 3)) (PreH45 : (0 <= (node_tag (n)))) (PreH46 : (node_at M t1_pre n )) (PreH47 : (rc_valid M )) (PreH48 : (store_type M t1_pre tr1 )) (PreH49 : (store_type M t2_pre tr2 )) (PreH50 : (repr_rel_node s tr1 tr1 )) (PreH51 : (repr_rel_node s tr2 tr2 )) (PreH52 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH53 : (t1_pre <> t2_pre)),
  (unify_rel tr1 tr2 s s_post_4 )
.

Definition atype_unify2_return_wit_7_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TApply (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TApply (a) (b)))) (PreH35 : ((node_tag (n)) = 2)) (PreH36 : ((node_tag (n)) <> 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TApply (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TApply (a) (b)))) (PreH35 : ((node_tag (n)) = 2)) (PreH36 : ((node_tag (n)) <> 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_4 s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_7_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TApply (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TApply (a) (b)))) (PreH35 : ((node_tag (n)) = 2)) (PreH36 : ((node_tag (n)) <> 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_7_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TApply (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TApply (a) (b)))) (PreH35 : ((node_tag (n)) = 2)) (PreH36 : ((node_tag (n)) <> 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_7_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TApply (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TApply (a) (b)))) (PreH35 : ((node_tag (n)) = 2)) (PreH36 : ((node_tag (n)) <> 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre retval M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_8_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (store_type M_post_3 (node_a (n)) a )) (PreH6 : (store_type M_post_3 (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post_3 s_post_3 )) (PreH9 : (rc_valid M_post_3 )) (PreH10 : (rc_preserves M M_post_3 )) (PreH11 : (rc_reservations_same M M_post_3 )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TApply (a) (b)))) (PreH15 : ((node_tag (n)) = 2)) (PreH16 : ((node_tag (n)) <> 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (store_type M_post_3 (node_a (n)) a )) (PreH6 : (store_type M_post_3 (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post_3 s_post_3 )) (PreH9 : (rc_valid M_post_3 )) (PreH10 : (rc_preserves M M_post_3 )) (PreH11 : (rc_reservations_same M M_post_3 )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TApply (a) (b)))) (PreH15 : ((node_tag (n)) = 2)) (PreH16 : ((node_tag (n)) <> 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  TT && emp 
|--
  “ (infer_result 2 M s t1_pre t1_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_8_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (store_type M_post_3 (node_a (n)) a )) (PreH6 : (store_type M_post_3 (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post_3 s_post_3 )) (PreH9 : (rc_valid M_post_3 )) (PreH10 : (rc_preserves M M_post_3 )) (PreH11 : (rc_reservations_same M M_post_3 )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TApply (a) (b)))) (PreH15 : ((node_tag (n)) = 2)) (PreH16 : ((node_tag (n)) <> 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  (infer_result 2 M s t1_pre t1_pre retval M_post_3 s_post_3 )
.

Definition atype_unify2_return_wit_9_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (node_at M_post_3 t2_pre n_2 )) (PreH4 : (store_type M_post_3 t2_pre tr2 )) (PreH5 : (store_type M_post_3 t1_pre tr1 )) (PreH6 : (store_type M_post_3 (node_a (n)) a )) (PreH7 : (store_type M_post_3 (node_b (n)) b )) (PreH8 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post_3 s_post_3 )) (PreH12 : (rc_valid M_post_3 )) (PreH13 : (rc_preserves M M_post_3 )) (PreH14 : (rc_reservations_same M M_post_3 )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TApply (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TApply (a) (b)))) (PreH21 : ((node_tag (n)) = 2)) (PreH22 : ((node_tag (n)) <> 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (node_at M_post_3 t2_pre n_2 )) (PreH4 : (store_type M_post_3 t2_pre tr2 )) (PreH5 : (store_type M_post_3 t1_pre tr1 )) (PreH6 : (store_type M_post_3 (node_a (n)) a )) (PreH7 : (store_type M_post_3 (node_b (n)) b )) (PreH8 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post_3 s_post_3 )) (PreH12 : (rc_valid M_post_3 )) (PreH13 : (rc_preserves M M_post_3 )) (PreH14 : (rc_reservations_same M M_post_3 )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TApply (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TApply (a) (b)))) (PreH21 : ((node_tag (n)) = 2)) (PreH22 : ((node_tag (n)) <> 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_9_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (node_at M_post_3 t2_pre n_2 )) (PreH4 : (store_type M_post_3 t2_pre tr2 )) (PreH5 : (store_type M_post_3 t1_pre tr1 )) (PreH6 : (store_type M_post_3 (node_a (n)) a )) (PreH7 : (store_type M_post_3 (node_b (n)) b )) (PreH8 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post_3 s_post_3 )) (PreH12 : (rc_valid M_post_3 )) (PreH13 : (rc_preserves M M_post_3 )) (PreH14 : (rc_reservations_same M M_post_3 )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TApply (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TApply (a) (b)))) (PreH21 : ((node_tag (n)) = 2)) (PreH22 : ((node_tag (n)) <> 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )
.

Definition atype_unify2_return_wit_10_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TArrow (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TArrow (a) (b)))) (PreH36 : ((node_tag (n)) = 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TArrow (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TArrow (a) (b)))) (PreH36 : ((node_tag (n)) = 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M_post_4 s_post_4 ) ”
  &&  “ (unify_rel tr1 tr2 s s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_10_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TArrow (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TArrow (a) (b)))) (PreH36 : ((node_tag (n)) = 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_10_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TArrow (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TArrow (a) (b)))) (PreH36 : ((node_tag (n)) = 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_10_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TArrow (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TArrow (a) (b)))) (PreH36 : ((node_tag (n)) = 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre 0 M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_10_distinct_nodes_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel b b_2 s_post_3 s_post_4 )) (PreH11 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH12 : (rc_valid M_post_4 )) (PreH13 : (rc_preserves M_post_3 M_post_4 )) (PreH14 : (rc_reservations_same M_post_3 M_post_4 )) (PreH15 : (retval_2 = 0)) (PreH16 : (node_at M_post_3 t1_pre n )) (PreH17 : (node_at M_post_3 t2_pre n_2 )) (PreH18 : (store_type M_post_3 t2_pre tr2 )) (PreH19 : (store_type M_post_3 t1_pre tr1 )) (PreH20 : (store_type M_post_3 (node_a (n)) a )) (PreH21 : (store_type M_post_3 (node_b (n)) b )) (PreH22 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH23 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH24 : (retval_2 = 0)) (PreH25 : (unify_rel a a_2 s s_post_3 )) (PreH26 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH27 : (rc_valid M_post_3 )) (PreH28 : (rc_preserves M M_post_3 )) (PreH29 : (rc_reservations_same M M_post_3 )) (PreH30 : (store_type M (node_b (n_2)) b_2 )) (PreH31 : (store_type M (node_a (n_2)) a_2 )) (PreH32 : (tr2 = (TArrow (a_2) (b_2)))) (PreH33 : (store_type M (node_b (n)) b )) (PreH34 : (store_type M (node_a (n)) a )) (PreH35 : (tr1 = (TArrow (a) (b)))) (PreH36 : ((node_tag (n)) = 1)) (PreH37 : ((node_tag (n)) = (node_tag (n_2)))) (PreH38 : ((node_tag (n_2)) <> 3)) (PreH39 : ((node_tag (n_2)) <= 3)) (PreH40 : (0 <= (node_tag (n_2)))) (PreH41 : (node_at M t2_pre n_2 )) (PreH42 : ((node_tag (n)) <> 3)) (PreH43 : ((node_tag (n)) <= 3)) (PreH44 : (0 <= (node_tag (n)))) (PreH45 : (node_at M t1_pre n )) (PreH46 : (rc_valid M )) (PreH47 : (store_type M t1_pre tr1 )) (PreH48 : (store_type M t2_pre tr2 )) (PreH49 : (repr_rel_node s tr1 tr1 )) (PreH50 : (repr_rel_node s tr2 tr2 )) (PreH51 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH52 : (t1_pre <> t2_pre)),
  (unify_rel tr1 tr2 s s_post_4 )
.

Definition atype_unify2_return_wit_11_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TArrow (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TArrow (a) (b)))) (PreH35 : ((node_tag (n)) = 1)) (PreH36 : ((node_tag (n)) = (node_tag (n_2)))) (PreH37 : ((node_tag (n_2)) <> 3)) (PreH38 : ((node_tag (n_2)) <= 3)) (PreH39 : (0 <= (node_tag (n_2)))) (PreH40 : (node_at M t2_pre n_2 )) (PreH41 : ((node_tag (n)) <> 3)) (PreH42 : ((node_tag (n)) <= 3)) (PreH43 : (0 <= (node_tag (n)))) (PreH44 : (node_at M t1_pre n )) (PreH45 : (rc_valid M )) (PreH46 : (store_type M t1_pre tr1 )) (PreH47 : (store_type M t2_pre tr2 )) (PreH48 : (repr_rel_node s tr1 tr1 )) (PreH49 : (repr_rel_node s tr2 tr2 )) (PreH50 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH51 : (t1_pre <> t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TArrow (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TArrow (a) (b)))) (PreH35 : ((node_tag (n)) = 1)) (PreH36 : ((node_tag (n)) = (node_tag (n_2)))) (PreH37 : ((node_tag (n_2)) <> 3)) (PreH38 : ((node_tag (n_2)) <= 3)) (PreH39 : (0 <= (node_tag (n_2)))) (PreH40 : (node_at M t2_pre n_2 )) (PreH41 : ((node_tag (n)) <> 3)) (PreH42 : ((node_tag (n)) <= 3)) (PreH43 : (0 <= (node_tag (n)))) (PreH44 : (node_at M t1_pre n )) (PreH45 : (rc_valid M )) (PreH46 : (store_type M t1_pre tr1 )) (PreH47 : (store_type M t2_pre tr2 )) (PreH48 : (repr_rel_node s tr1 tr1 )) (PreH49 : (repr_rel_node s tr2 tr2 )) (PreH50 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH51 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_4 s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_11_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TArrow (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TArrow (a) (b)))) (PreH35 : ((node_tag (n)) = 1)) (PreH36 : ((node_tag (n)) = (node_tag (n_2)))) (PreH37 : ((node_tag (n_2)) <> 3)) (PreH38 : ((node_tag (n_2)) <= 3)) (PreH39 : (0 <= (node_tag (n_2)))) (PreH40 : (node_at M t2_pre n_2 )) (PreH41 : ((node_tag (n)) <> 3)) (PreH42 : ((node_tag (n)) <= 3)) (PreH43 : (0 <= (node_tag (n)))) (PreH44 : (node_at M t1_pre n )) (PreH45 : (rc_valid M )) (PreH46 : (store_type M t1_pre tr1 )) (PreH47 : (store_type M t2_pre tr2 )) (PreH48 : (repr_rel_node s tr1 tr1 )) (PreH49 : (repr_rel_node s tr2 tr2 )) (PreH50 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH51 : (t1_pre <> t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_11_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TArrow (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TArrow (a) (b)))) (PreH35 : ((node_tag (n)) = 1)) (PreH36 : ((node_tag (n)) = (node_tag (n_2)))) (PreH37 : ((node_tag (n_2)) <> 3)) (PreH38 : ((node_tag (n_2)) <= 3)) (PreH39 : (0 <= (node_tag (n_2)))) (PreH40 : (node_at M t2_pre n_2 )) (PreH41 : ((node_tag (n)) <> 3)) (PreH42 : ((node_tag (n)) <= 3)) (PreH43 : (0 <= (node_tag (n)))) (PreH44 : (node_at M t1_pre n )) (PreH45 : (rc_valid M )) (PreH46 : (store_type M t1_pre tr1 )) (PreH47 : (store_type M t2_pre tr2 )) (PreH48 : (repr_rel_node s tr1 tr1 )) (PreH49 : (repr_rel_node s tr2 tr2 )) (PreH50 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH51 : (t1_pre <> t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_11_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t2_pre n_2 )) (PreH2 : (node_at M_post_4 t1_pre n )) (PreH3 : (store_type M_post_4 (node_b (n_2)) b_2 )) (PreH4 : (store_type M_post_4 (node_a (n_2)) a_2 )) (PreH5 : (store_type M_post_4 (node_b (n)) b )) (PreH6 : (store_type M_post_4 (node_a (n)) a )) (PreH7 : (store_type M_post_4 t1_pre tr1 )) (PreH8 : (store_type M_post_4 t2_pre tr2 )) (PreH9 : (retval <> 0)) (PreH10 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n_2)) retval M_post_4 s_post_4 )) (PreH11 : (rc_valid M_post_4 )) (PreH12 : (rc_preserves M_post_3 M_post_4 )) (PreH13 : (rc_reservations_same M_post_3 M_post_4 )) (PreH14 : (retval_2 = 0)) (PreH15 : (node_at M_post_3 t1_pre n )) (PreH16 : (node_at M_post_3 t2_pre n_2 )) (PreH17 : (store_type M_post_3 t2_pre tr2 )) (PreH18 : (store_type M_post_3 t1_pre tr1 )) (PreH19 : (store_type M_post_3 (node_a (n)) a )) (PreH20 : (store_type M_post_3 (node_b (n)) b )) (PreH21 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH22 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH23 : (retval_2 = 0)) (PreH24 : (unify_rel a a_2 s s_post_3 )) (PreH25 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval_2 M_post_3 s_post_3 )) (PreH26 : (rc_valid M_post_3 )) (PreH27 : (rc_preserves M M_post_3 )) (PreH28 : (rc_reservations_same M M_post_3 )) (PreH29 : (store_type M (node_b (n_2)) b_2 )) (PreH30 : (store_type M (node_a (n_2)) a_2 )) (PreH31 : (tr2 = (TArrow (a_2) (b_2)))) (PreH32 : (store_type M (node_b (n)) b )) (PreH33 : (store_type M (node_a (n)) a )) (PreH34 : (tr1 = (TArrow (a) (b)))) (PreH35 : ((node_tag (n)) = 1)) (PreH36 : ((node_tag (n)) = (node_tag (n_2)))) (PreH37 : ((node_tag (n_2)) <> 3)) (PreH38 : ((node_tag (n_2)) <= 3)) (PreH39 : (0 <= (node_tag (n_2)))) (PreH40 : (node_at M t2_pre n_2 )) (PreH41 : ((node_tag (n)) <> 3)) (PreH42 : ((node_tag (n)) <= 3)) (PreH43 : (0 <= (node_tag (n)))) (PreH44 : (node_at M t1_pre n )) (PreH45 : (rc_valid M )) (PreH46 : (store_type M t1_pre tr1 )) (PreH47 : (store_type M t2_pre tr2 )) (PreH48 : (repr_rel_node s tr1 tr1 )) (PreH49 : (repr_rel_node s tr2 tr2 )) (PreH50 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH51 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre retval M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_12_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TArrow (a) (b)))) (PreH27 : ((node_tag (n)) = 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TArrow (a) (b)))) (PreH27 : ((node_tag (n)) = 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t1_pre 0 M_post_4 s_post_4 ) ”
  &&  “ (unify_rel tr1 tr2 s s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_12_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TArrow (a) (b)))) (PreH27 : ((node_tag (n)) = 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_12_same_node_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TArrow (a) (b)))) (PreH27 : ((node_tag (n)) = 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_12_same_node_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TArrow (a) (b)))) (PreH27 : ((node_tag (n)) = 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (infer_result 2 M s t1_pre t1_pre 0 M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_12_same_node_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval = 0)) (PreH7 : (unify_rel b b s_post_3 s_post_4 )) (PreH8 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH9 : (rc_valid M_post_4 )) (PreH10 : (rc_preserves M_post_3 M_post_4 )) (PreH11 : (rc_reservations_same M_post_3 M_post_4 )) (PreH12 : (retval_2 = 0)) (PreH13 : (node_at M_post_3 t1_pre n )) (PreH14 : (store_type M_post_3 t2_pre tr2 )) (PreH15 : (store_type M_post_3 t1_pre tr1 )) (PreH16 : (store_type M_post_3 (node_a (n)) a )) (PreH17 : (store_type M_post_3 (node_b (n)) b )) (PreH18 : (retval_2 = 0)) (PreH19 : (unify_rel a a s s_post_3 )) (PreH20 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH21 : (rc_valid M_post_3 )) (PreH22 : (rc_preserves M M_post_3 )) (PreH23 : (rc_reservations_same M M_post_3 )) (PreH24 : (store_type M (node_b (n)) b )) (PreH25 : (store_type M (node_a (n)) a )) (PreH26 : (tr1 = (TArrow (a) (b)))) (PreH27 : ((node_tag (n)) = 1)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre = t2_pre)),
  (unify_rel tr1 tr2 s s_post_4 )
.

Definition atype_unify2_return_wit_13_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TArrow (a) (b)))) (PreH26 : ((node_tag (n)) = 1)) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre = t2_pre)),
  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TArrow (a) (b)))) (PreH26 : ((node_tag (n)) = 1)) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre = t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M_post_4 ) ”
  &&  “ (rc_preserves M M_post_4 ) ”
  &&  “ (infer_result 2 M s t1_pre t1_pre retval M_post_4 s_post_4 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_13_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TArrow (a) (b)))) (PreH26 : ((node_tag (n)) = 1)) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre = t2_pre)),
  (rc_reservations_same M M_post_4 )
.

Definition atype_unify2_return_wit_13_same_node_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TArrow (a) (b)))) (PreH26 : ((node_tag (n)) = 1)) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre = t2_pre)),
  (rc_preserves M M_post_4 )
.

Definition atype_unify2_return_wit_13_same_node_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval_2: Z) (M_post_4: RcState) (s_post_4: sol) (retval: Z) (PreH1 : (node_at M_post_4 t1_pre n )) (PreH2 : (store_type M_post_4 (node_b (n)) b )) (PreH3 : (store_type M_post_4 (node_a (n)) a )) (PreH4 : (store_type M_post_4 t1_pre tr1 )) (PreH5 : (store_type M_post_4 t2_pre tr2 )) (PreH6 : (retval <> 0)) (PreH7 : (infer_result 0 M_post_3 s_post_3 (node_b (n)) (node_b (n)) retval M_post_4 s_post_4 )) (PreH8 : (rc_valid M_post_4 )) (PreH9 : (rc_preserves M_post_3 M_post_4 )) (PreH10 : (rc_reservations_same M_post_3 M_post_4 )) (PreH11 : (retval_2 = 0)) (PreH12 : (node_at M_post_3 t1_pre n )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (store_type M_post_3 (node_a (n)) a )) (PreH16 : (store_type M_post_3 (node_b (n)) b )) (PreH17 : (retval_2 = 0)) (PreH18 : (unify_rel a a s s_post_3 )) (PreH19 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval_2 M_post_3 s_post_3 )) (PreH20 : (rc_valid M_post_3 )) (PreH21 : (rc_preserves M M_post_3 )) (PreH22 : (rc_reservations_same M M_post_3 )) (PreH23 : (store_type M (node_b (n)) b )) (PreH24 : (store_type M (node_a (n)) a )) (PreH25 : (tr1 = (TArrow (a) (b)))) (PreH26 : ((node_tag (n)) = 1)) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre = t2_pre)),
  (infer_result 2 M s t1_pre t1_pre retval M_post_4 s_post_4 )
.

Definition atype_unify2_return_wit_14_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (node_at M_post_3 t2_pre n_2 )) (PreH4 : (store_type M_post_3 t2_pre tr2 )) (PreH5 : (store_type M_post_3 t1_pre tr1 )) (PreH6 : (store_type M_post_3 (node_a (n)) a )) (PreH7 : (store_type M_post_3 (node_b (n)) b )) (PreH8 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post_3 s_post_3 )) (PreH12 : (rc_valid M_post_3 )) (PreH13 : (rc_preserves M M_post_3 )) (PreH14 : (rc_reservations_same M M_post_3 )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TArrow (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TArrow (a) (b)))) (PreH21 : ((node_tag (n)) = 1)) (PreH22 : ((node_tag (n)) = (node_tag (n_2)))) (PreH23 : ((node_tag (n_2)) <> 3)) (PreH24 : ((node_tag (n_2)) <= 3)) (PreH25 : (0 <= (node_tag (n_2)))) (PreH26 : (node_at M t2_pre n_2 )) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <= 3)) (PreH29 : (0 <= (node_tag (n)))) (PreH30 : (node_at M t1_pre n )) (PreH31 : (rc_valid M )) (PreH32 : (store_type M t1_pre tr1 )) (PreH33 : (store_type M t2_pre tr2 )) (PreH34 : (repr_rel_node s tr1 tr1 )) (PreH35 : (repr_rel_node s tr2 tr2 )) (PreH36 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH37 : (t1_pre <> t2_pre)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (node_at M_post_3 t2_pre n_2 )) (PreH4 : (store_type M_post_3 t2_pre tr2 )) (PreH5 : (store_type M_post_3 t1_pre tr1 )) (PreH6 : (store_type M_post_3 (node_a (n)) a )) (PreH7 : (store_type M_post_3 (node_b (n)) b )) (PreH8 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post_3 s_post_3 )) (PreH12 : (rc_valid M_post_3 )) (PreH13 : (rc_preserves M M_post_3 )) (PreH14 : (rc_reservations_same M M_post_3 )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TArrow (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TArrow (a) (b)))) (PreH21 : ((node_tag (n)) = 1)) (PreH22 : ((node_tag (n)) = (node_tag (n_2)))) (PreH23 : ((node_tag (n_2)) <> 3)) (PreH24 : ((node_tag (n_2)) <= 3)) (PreH25 : (0 <= (node_tag (n_2)))) (PreH26 : (node_at M t2_pre n_2 )) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <= 3)) (PreH29 : (0 <= (node_tag (n)))) (PreH30 : (node_at M t1_pre n )) (PreH31 : (rc_valid M )) (PreH32 : (store_type M t1_pre tr1 )) (PreH33 : (store_type M t2_pre tr2 )) (PreH34 : (repr_rel_node s tr1 tr1 )) (PreH35 : (repr_rel_node s tr2 tr2 )) (PreH36 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH37 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_14_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (node_at M_post_3 t2_pre n_2 )) (PreH4 : (store_type M_post_3 t2_pre tr2 )) (PreH5 : (store_type M_post_3 t1_pre tr1 )) (PreH6 : (store_type M_post_3 (node_a (n)) a )) (PreH7 : (store_type M_post_3 (node_b (n)) b )) (PreH8 : (store_type M_post_3 (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post_3 (node_b (n_2)) b_2 )) (PreH10 : (retval <> 0)) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post_3 s_post_3 )) (PreH12 : (rc_valid M_post_3 )) (PreH13 : (rc_preserves M M_post_3 )) (PreH14 : (rc_reservations_same M M_post_3 )) (PreH15 : (store_type M (node_b (n_2)) b_2 )) (PreH16 : (store_type M (node_a (n_2)) a_2 )) (PreH17 : (tr2 = (TArrow (a_2) (b_2)))) (PreH18 : (store_type M (node_b (n)) b )) (PreH19 : (store_type M (node_a (n)) a )) (PreH20 : (tr1 = (TArrow (a) (b)))) (PreH21 : ((node_tag (n)) = 1)) (PreH22 : ((node_tag (n)) = (node_tag (n_2)))) (PreH23 : ((node_tag (n_2)) <> 3)) (PreH24 : ((node_tag (n_2)) <= 3)) (PreH25 : (0 <= (node_tag (n_2)))) (PreH26 : (node_at M t2_pre n_2 )) (PreH27 : ((node_tag (n)) <> 3)) (PreH28 : ((node_tag (n)) <= 3)) (PreH29 : (0 <= (node_tag (n)))) (PreH30 : (node_at M t1_pre n )) (PreH31 : (rc_valid M )) (PreH32 : (store_type M t1_pre tr1 )) (PreH33 : (store_type M t2_pre tr2 )) (PreH34 : (repr_rel_node s tr1 tr1 )) (PreH35 : (repr_rel_node s tr2 tr2 )) (PreH36 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH37 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre retval M_post_3 s_post_3 )
.

Definition atype_unify2_return_wit_15_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (store_type M_post_3 (node_a (n)) a )) (PreH6 : (store_type M_post_3 (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post_3 s_post_3 )) (PreH9 : (rc_valid M_post_3 )) (PreH10 : (rc_preserves M M_post_3 )) (PreH11 : (rc_reservations_same M M_post_3 )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TArrow (a) (b)))) (PreH15 : ((node_tag (n)) = 1)) (PreH16 : ((node_tag (n)) <> 3)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre = t2_pre)),
  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (store_type M_post_3 (node_a (n)) a )) (PreH6 : (store_type M_post_3 (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post_3 s_post_3 )) (PreH9 : (rc_valid M_post_3 )) (PreH10 : (rc_preserves M M_post_3 )) (PreH11 : (rc_reservations_same M M_post_3 )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TArrow (a) (b)))) (PreH15 : ((node_tag (n)) = 1)) (PreH16 : ((node_tag (n)) <> 3)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre = t2_pre)),
  TT && emp 
|--
  “ (infer_result 2 M s t1_pre t1_pre retval M_post_3 s_post_3 ) ”
  &&  emp
).

Definition atype_unify2_return_wit_15_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post_3: RcState) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (node_at M_post_3 t1_pre n )) (PreH3 : (store_type M_post_3 t2_pre tr2 )) (PreH4 : (store_type M_post_3 t1_pre tr1 )) (PreH5 : (store_type M_post_3 (node_a (n)) a )) (PreH6 : (store_type M_post_3 (node_b (n)) b )) (PreH7 : (retval <> 0)) (PreH8 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post_3 s_post_3 )) (PreH9 : (rc_valid M_post_3 )) (PreH10 : (rc_preserves M M_post_3 )) (PreH11 : (rc_reservations_same M M_post_3 )) (PreH12 : (store_type M (node_b (n)) b )) (PreH13 : (store_type M (node_a (n)) a )) (PreH14 : (tr1 = (TArrow (a) (b)))) (PreH15 : ((node_tag (n)) = 1)) (PreH16 : ((node_tag (n)) <> 3)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre = t2_pre)),
  (infer_result 2 M s t1_pre t1_pre retval M_post_3 s_post_3 )
.

Definition atype_unify2_return_wit_16_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> (node_tag (n_2)))) (PreH2 : ((node_tag (n_2)) <> 3)) (PreH3 : ((node_tag (n_2)) <= 3)) (PreH4 : (0 <= (node_tag (n_2)))) (PreH5 : (node_at M t2_pre n_2 )) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (2 <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 2 M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> (node_tag (n_2)))) (PreH2 : ((node_tag (n_2)) <> 3)) (PreH3 : ((node_tag (n_2)) <= 3)) (PreH4 : (0 <= (node_tag (n_2)))) (PreH5 : (node_at M t2_pre n_2 )) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  TT && emp 
|--
  “ (rc_reservations_same M M ) ”
  &&  “ (rc_preserves M M ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 2 M s ) ”
  &&  emp
).

Definition atype_unify2_return_wit_16_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> (node_tag (n_2)))) (PreH2 : ((node_tag (n_2)) <> 3)) (PreH3 : ((node_tag (n_2)) <= 3)) (PreH4 : (0 <= (node_tag (n_2)))) (PreH5 : (node_at M t2_pre n_2 )) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  (rc_reservations_same M M )
.

Definition atype_unify2_return_wit_16_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> (node_tag (n_2)))) (PreH2 : ((node_tag (n_2)) <> 3)) (PreH3 : ((node_tag (n_2)) <= 3)) (PreH4 : (0 <= (node_tag (n_2)))) (PreH5 : (node_at M t2_pre n_2 )) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  (rc_preserves M M )
.

Definition atype_unify2_return_wit_16_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> (node_tag (n_2)))) (PreH2 : ((node_tag (n_2)) <> 3)) (PreH3 : ((node_tag (n_2)) <= 3)) (PreH4 : (0 <= (node_tag (n_2)))) (PreH5 : (node_at M t2_pre n_2 )) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  (infer_result 2 M s t1_pre t2_pre 2 M s )
.

Definition atype_unify2_return_wit_17_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre n_2 )) (PreH3 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH5 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH6 : (store_type M_post_3 retval_2 tr1 )) (PreH7 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH10 : (node_at M_post_3 t1_pre n )) (PreH11 : (node_at M_post_3 t2_pre n_2 )) (PreH12 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (retval_2 = t1_pre)) (PreH16 : (retain_rel M t1_pre M_post_3 )) (PreH17 : (rc_valid M_post_3 )) (PreH18 : (rc_preserves M M_post_3 )) (PreH19 : (retval = 0)) (PreH20 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH21 : ((node_a (n_2)) < 100)) (PreH22 : (0 <= (node_a (n_2)))) (PreH23 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH24 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH25 : (tr2 = (TVar ((node_a (n_2)))))) (PreH26 : ((node_tag (n_2)) = 3)) (PreH27 : ((node_tag (n_2)) <= 3)) (PreH28 : (0 <= (node_tag (n_2)))) (PreH29 : (node_at M t2_pre n_2 )) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre <> t2_pre)) (PreH41 : (retval = 0)),
  (store_world (rc_publish (M_post_3) (retval_2)) )
  **  (store_solution (rc_publish (M_post_3) (retval_2)) ( &( "res" ) ) (sol_update (s) ((node_a (n_2))) (tr1)) )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (0 = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre n_2 )) (PreH3 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH5 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH6 : (store_type M_post_3 retval_2 tr1 )) (PreH7 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH10 : (node_at M_post_3 t1_pre n )) (PreH11 : (node_at M_post_3 t2_pre n_2 )) (PreH12 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (retval_2 = t1_pre)) (PreH16 : (retain_rel M t1_pre M_post_3 )) (PreH17 : (rc_valid M_post_3 )) (PreH18 : (rc_preserves M M_post_3 )) (PreH19 : (retval = 0)) (PreH20 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH21 : ((node_a (n_2)) < 100)) (PreH22 : (0 <= (node_a (n_2)))) (PreH23 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH24 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH25 : (tr2 = (TVar ((node_a (n_2)))))) (PreH26 : ((node_tag (n_2)) = 3)) (PreH27 : ((node_tag (n_2)) <= 3)) (PreH28 : (0 <= (node_tag (n_2)))) (PreH29 : (node_at M t2_pre n_2 )) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre <> t2_pre)) (PreH41 : (retval = 0)),
  TT && emp 
|--
  “ (infer_result 2 M s t1_pre t2_pre 0 (rc_publish (M_post_3) (t1_pre)) (sol_update (s) ((node_a (n_2))) (tr1)) ) ”
  &&  “ (unify_rel tr1 tr2 s (sol_update (s) ((node_a (n_2))) (tr1)) ) ”
  &&  emp
).

Definition atype_unify2_return_wit_17_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre n_2 )) (PreH3 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH5 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH6 : (store_type M_post_3 retval_2 tr1 )) (PreH7 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH10 : (node_at M_post_3 t1_pre n )) (PreH11 : (node_at M_post_3 t2_pre n_2 )) (PreH12 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (retval_2 = t1_pre)) (PreH16 : (retain_rel M t1_pre M_post_3 )) (PreH17 : (rc_valid M_post_3 )) (PreH18 : (rc_preserves M M_post_3 )) (PreH19 : (retval = 0)) (PreH20 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH21 : ((node_a (n_2)) < 100)) (PreH22 : (0 <= (node_a (n_2)))) (PreH23 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH24 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH25 : (tr2 = (TVar ((node_a (n_2)))))) (PreH26 : ((node_tag (n_2)) = 3)) (PreH27 : ((node_tag (n_2)) <= 3)) (PreH28 : (0 <= (node_tag (n_2)))) (PreH29 : (node_at M t2_pre n_2 )) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre <> t2_pre)) (PreH41 : (retval = 0)),
  (infer_result 2 M s t1_pre t2_pre 0 (rc_publish (M_post_3) (t1_pre)) (sol_update (s) ((node_a (n_2))) (tr1)) )
.

Definition atype_unify2_return_wit_17_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre n_2 )) (PreH3 : (node_at (rc_publish (M_post_3) (retval_2)) t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH5 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH6 : (store_type M_post_3 retval_2 tr1 )) (PreH7 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH10 : (node_at M_post_3 t1_pre n )) (PreH11 : (node_at M_post_3 t2_pre n_2 )) (PreH12 : (node_at M_post_3 t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH13 : (store_type M_post_3 t2_pre tr2 )) (PreH14 : (store_type M_post_3 t1_pre tr1 )) (PreH15 : (retval_2 = t1_pre)) (PreH16 : (retain_rel M t1_pre M_post_3 )) (PreH17 : (rc_valid M_post_3 )) (PreH18 : (rc_preserves M M_post_3 )) (PreH19 : (retval = 0)) (PreH20 : (not_occur_final s (node_a (n_2)) tr1 )) (PreH21 : ((node_a (n_2)) < 100)) (PreH22 : (0 <= (node_a (n_2)))) (PreH23 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH24 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH25 : (tr2 = (TVar ((node_a (n_2)))))) (PreH26 : ((node_tag (n_2)) = 3)) (PreH27 : ((node_tag (n_2)) <= 3)) (PreH28 : (0 <= (node_tag (n_2)))) (PreH29 : (node_at M t2_pre n_2 )) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre <> t2_pre)) (PreH41 : (retval = 0)),
  (unify_rel tr1 tr2 s (sol_update (s) ((node_a (n_2))) (tr1)) )
.

Definition atype_unify2_return_wit_18_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (1 <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 1 M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  TT && emp 
|--
  “ (rc_reservations_same M M ) ”
  &&  “ (rc_preserves M M ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 1 M s ) ”
  &&  emp
).

Definition atype_unify2_return_wit_18_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  (rc_reservations_same M M )
.

Definition atype_unify2_return_wit_18_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  (rc_preserves M M )
.

Definition atype_unify2_return_wit_18_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n_2)) < 100)) (PreH3 : (0 <= (node_a (n_2)))) (PreH4 : (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) )) (PreH5 : (n_2 = (Node (3) ((node_a (n_2))) (0)))) (PreH6 : (tr2 = (TVar ((node_a (n_2)))))) (PreH7 : ((node_tag (n_2)) = 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)) (PreH22 : (retval <> 0)),
  (infer_result 2 M s t1_pre t2_pre 1 M s )
.

Definition atype_unify2_return_wit_19_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre = t2_pre)) (PreH35 : (retval = 0)),
  (store_world (rc_publish (M_post_3) (retval_2)) )
  **  (store_solution (rc_publish (M_post_3) (retval_2)) ( &( "res" ) ) (sol_update (s) ((node_a (n))) (tr2)) )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (0 = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre = t2_pre)) (PreH35 : (retval = 0)),
  TT && emp 
|--
  “ (infer_result 2 M s t1_pre t1_pre 0 (rc_publish (M_post_3) (t1_pre)) (sol_update (s) ((node_a (n))) (tr2)) ) ”
  &&  “ (unify_rel tr1 tr2 s (sol_update (s) ((node_a (n))) (tr2)) ) ”
  &&  emp
).

Definition atype_unify2_return_wit_19_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre = t2_pre)) (PreH35 : (retval = 0)),
  (infer_result 2 M s t1_pre t1_pre 0 (rc_publish (M_post_3) (t1_pre)) (sol_update (s) ((node_a (n))) (tr2)) )
.

Definition atype_unify2_return_wit_19_same_node_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre = t2_pre)) (PreH35 : (retval = 0)),
  (unify_rel tr1 tr2 s (sol_update (s) ((node_a (n))) (tr2)) )
.

Definition atype_unify2_return_wit_20_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre <> t2_pre)) (PreH35 : (retval = 0)),
  (store_world (rc_publish (M_post_3) (retval_2)) )
  **  (store_solution (rc_publish (M_post_3) (retval_2)) ( &( "res" ) ) (sol_update (s) ((node_a (n))) (tr2)) )
|--
  EX (M_post: RcState) (s_post: sol),
  “ (0 = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 0 M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre <> t2_pre)) (PreH35 : (retval = 0)),
  TT && emp 
|--
  “ (infer_result 2 M s t1_pre t2_pre 0 (rc_publish (M_post_3) (t2_pre)) (sol_update (s) ((node_a (n))) (tr2)) ) ”
  &&  “ (unify_rel tr1 tr2 s (sol_update (s) ((node_a (n))) (tr2)) ) ”
  &&  emp
).

Definition atype_unify2_return_wit_20_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre <> t2_pre)) (PreH35 : (retval = 0)),
  (infer_result 2 M s t1_pre t2_pre 0 (rc_publish (M_post_3) (t2_pre)) (sol_update (s) ((node_a (n))) (tr2)) )
.

Definition atype_unify2_return_wit_20_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (M_post_3: RcState) (retval_2: Z) (PreH1 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre n )) (PreH2 : (node_at (rc_publish (M_post_3) (retval_2)) t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type (rc_publish (M_post_3) (retval_2)) t2_pre tr2 )) (PreH4 : (store_type (rc_publish (M_post_3) (retval_2)) t1_pre tr1 )) (PreH5 : (store_type M_post_3 retval_2 tr2 )) (PreH6 : (rc_valid (rc_publish (M_post_3) (retval_2)) )) (PreH7 : (rc_preserves M (rc_publish (M_post_3) (retval_2)) )) (PreH8 : (rc_reservations_same M (rc_publish (M_post_3) (retval_2)) )) (PreH9 : (node_at M_post_3 t1_pre n )) (PreH10 : (node_at M_post_3 t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH11 : (store_type M_post_3 t2_pre tr2 )) (PreH12 : (store_type M_post_3 t1_pre tr1 )) (PreH13 : (retval_2 = t2_pre)) (PreH14 : (retain_rel M t2_pre M_post_3 )) (PreH15 : (rc_valid M_post_3 )) (PreH16 : (rc_preserves M M_post_3 )) (PreH17 : (retval = 0)) (PreH18 : (not_occur_final s (node_a (n)) tr2 )) (PreH19 : ((node_a (n)) < 100)) (PreH20 : (0 <= (node_a (n)))) (PreH21 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH22 : (n = (Node (3) ((node_a (n))) (0)))) (PreH23 : (tr1 = (TVar ((node_a (n)))))) (PreH24 : ((node_tag (n)) = 3)) (PreH25 : ((node_tag (n)) <= 3)) (PreH26 : (0 <= (node_tag (n)))) (PreH27 : (node_at M t1_pre n )) (PreH28 : (rc_valid M )) (PreH29 : (store_type M t1_pre tr1 )) (PreH30 : (store_type M t2_pre tr2 )) (PreH31 : (repr_rel_node s tr1 tr1 )) (PreH32 : (repr_rel_node s tr2 tr2 )) (PreH33 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH34 : (t1_pre <> t2_pre)) (PreH35 : (retval = 0)),
  (unify_rel tr1 tr2 s (sol_update (s) ((node_a (n))) (tr2)) )
.

Definition atype_unify2_return_wit_21_same_node :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (1 <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 1 M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  TT && emp 
|--
  “ (rc_reservations_same M M ) ”
  &&  “ (rc_preserves M M ) ”
  &&  “ (infer_result 2 M s t1_pre t1_pre 1 M s ) ”
  &&  emp
).

Definition atype_unify2_return_wit_21_same_node_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  (rc_reservations_same M M )
.

Definition atype_unify2_return_wit_21_same_node_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  (rc_preserves M M )
.

Definition atype_unify2_return_wit_21_same_node_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)) (PreH18 : (retval <> 0)),
  (infer_result 2 M s t1_pre t1_pre 1 M s )
.

Definition atype_unify2_return_wit_22_distinct_nodes :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (M_post_2: RcState) (s_post_2: sol),
  “ (1 <> 0) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 1 M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 )
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  TT && emp 
|--
  “ (rc_reservations_same M M ) ”
  &&  “ (rc_preserves M M ) ”
  &&  “ (infer_result 2 M s t1_pre t2_pre 1 M s ) ”
  &&  emp
).

Definition atype_unify2_return_wit_22_distinct_nodes_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  (rc_reservations_same M M )
.

Definition atype_unify2_return_wit_22_distinct_nodes_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  (rc_preserves M M )
.

Definition atype_unify2_return_wit_22_distinct_nodes_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((node_a (n)) < 100)) (PreH3 : (0 <= (node_a (n)))) (PreH4 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH5 : (n = (Node (3) ((node_a (n))) (0)))) (PreH6 : (tr1 = (TVar ((node_a (n)))))) (PreH7 : ((node_tag (n)) = 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)) (PreH18 : (retval <> 0)),
  (infer_result 2 M s t1_pre t2_pre 1 M s )
.

Definition atype_unify2_partial_solve_wit_1_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (PreH1 : (rc_valid M )) (PreH2 : (store_type M t1_pre tr1 )) (PreH3 : (store_type M t2_pre tr2 )) (PreH4 : (repr_rel_node s tr1 tr1 )) (PreH5 : (repr_rel_node s tr2 tr2 )) (PreH6 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH7 : (t1_pre = t2_pre)),
  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (n: TypeNode),
  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_2_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (PreH1 : (rc_valid M )) (PreH2 : (store_type M t1_pre tr1 )) (PreH3 : (store_type M t2_pre tr2 )) (PreH4 : (repr_rel_node s tr1 tr1 )) (PreH5 : (repr_rel_node s tr2 tr2 )) (PreH6 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH7 : (t1_pre <> t2_pre)),
  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (n: TypeNode),
  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_3_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t1_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (repr_rel_node s tr2 tr2 )) (PreH10 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH11 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_4_same_node_pure :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr1 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "occur" ) )) # Int  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
.

Definition atype_unify2_partial_solve_wit_4_same_node_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr1 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_4_same_node := atype_unify2_partial_solve_wit_4_same_node_pure -> atype_unify2_partial_solve_wit_4_same_node_aux.

Definition atype_unify2_partial_solve_wit_5_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t1_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (repr_rel_node s tr2 tr2 )) (PreH10 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH11 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_6_distinct_nodes_pure :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr1 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "occur" ) )) # Int  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
.

Definition atype_unify2_partial_solve_wit_6_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr1 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_6_distinct_nodes := atype_unify2_partial_solve_wit_6_distinct_nodes_pure -> atype_unify2_partial_solve_wit_6_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_7_same_node_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)) (PreH19 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M ) ”
  &&  “ (0 < (rc_count (M) (t2_pre))) ”
  &&  “ ((rc_count (M) (t2_pre)) < INT_MAX) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
  &&  “ (0 < (rc_count (M) (t1_pre))) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre = t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 < (rc_count (M) (t1_pre))) ”
  &&  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
  &&  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
  &&  “ (0 < (rc_count (M) (t1_pre))) ”
).

Definition atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre = t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 < (rc_count (M) (t1_pre))) ”
.

Definition atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre = t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
.

Definition atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre = t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
.

Definition atype_unify2_partial_solve_wit_7_same_node_pure_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre = t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 < (rc_count (M) (t1_pre))) ”
.

Definition atype_unify2_partial_solve_wit_7_same_node_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)) (PreH19 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (0 < (rc_count (M) (t2_pre))) ”
  &&  “ ((rc_count (M) (t2_pre)) < INT_MAX) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
  &&  “ (0 < (rc_count (M) (t1_pre))) ”
  &&  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_7_same_node := atype_unify2_partial_solve_wit_7_same_node_pure -> atype_unify2_partial_solve_wit_7_same_node_aux.

Definition atype_unify2_partial_solve_wit_8_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)) (PreH19 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M ) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((rc_count (M) (t2_pre)) < INT_MAX) ”
  &&  “ (0 < (rc_count (M) (t2_pre))) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 < (rc_count (M) (t2_pre))) ”
  &&  “ ((rc_count (M) (t2_pre)) < INT_MAX) ”
).

Definition atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 < (rc_count (M) (t2_pre))) ”
.

Definition atype_unify2_partial_solve_wit_8_distinct_nodes_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr2 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr1 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t1_pre n )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_count (M) (t2_pre)) < INT_MAX) ”
.

Definition atype_unify2_partial_solve_wit_8_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr2 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr1 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)) (PreH19 : (retval = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((rc_count (M) (t2_pre)) < INT_MAX) ”
  &&  “ (0 < (rc_count (M) (t2_pre))) ”
  &&  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_8_distinct_nodes := atype_unify2_partial_solve_wit_8_distinct_nodes_pure -> atype_unify2_partial_solve_wit_8_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_9_same_node_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (retval = t2_pre)) (PreH6 : (retain_rel M t2_pre M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (retval_2 = 0)) (PreH10 : (not_occur_final s (node_a (n)) tr2 )) (PreH11 : ((node_a (n)) < 100)) (PreH12 : (0 <= (node_a (n)))) (PreH13 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (n = (Node (3) ((node_a (n))) (0)))) (PreH15 : (tr1 = (TVar ((node_a (n)))))) (PreH16 : ((node_tag (n)) = 3)) (PreH17 : ((node_tag (n)) <= 3)) (PreH18 : (0 <= (node_tag (n)))) (PreH19 : (node_at M t1_pre n )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre = t2_pre)) (PreH27 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ (store_type M_post retval tr2 ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (retain_rel M retval M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre = t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
).

Definition atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre = t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
.

Definition atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre = t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
.

Definition atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre = t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
.

Definition atype_unify2_partial_solve_wit_9_same_node_pure_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre = t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
.

Definition atype_unify2_partial_solve_wit_9_same_node_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (retval = t2_pre)) (PreH6 : (retain_rel M t2_pre M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (retval_2 = 0)) (PreH10 : (not_occur_final s (node_a (n)) tr2 )) (PreH11 : ((node_a (n)) < 100)) (PreH12 : (0 <= (node_a (n)))) (PreH13 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (n = (Node (3) ((node_a (n))) (0)))) (PreH15 : (tr1 = (TVar ((node_a (n)))))) (PreH16 : ((node_tag (n)) = 3)) (PreH17 : ((node_tag (n)) <= 3)) (PreH18 : (0 <= (node_tag (n)))) (PreH19 : (node_at M t1_pre n )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre = t2_pre)) (PreH27 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ (store_type M_post retval tr2 ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (retain_rel M retval M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (retval = t2_pre) ”
  &&  “ (retain_rel M t2_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  “ (retval_2 = 0) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify2_partial_solve_wit_9_same_node := atype_unify2_partial_solve_wit_9_same_node_pure -> atype_unify2_partial_solve_wit_9_same_node_aux.

Definition atype_unify2_partial_solve_wit_10_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (retval = t2_pre)) (PreH6 : (retain_rel M t2_pre M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (retval_2 = 0)) (PreH10 : (not_occur_final s (node_a (n)) tr2 )) (PreH11 : ((node_a (n)) < 100)) (PreH12 : (0 <= (node_a (n)))) (PreH13 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (n = (Node (3) ((node_a (n))) (0)))) (PreH15 : (tr1 = (TVar ((node_a (n)))))) (PreH16 : ((node_tag (n)) = 3)) (PreH17 : ((node_tag (n)) <= 3)) (PreH18 : (0 <= (node_tag (n)))) (PreH19 : (node_at M t1_pre n )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre <> t2_pre)) (PreH27 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ (store_type M_post retval tr2 ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (retain_rel M retval M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t2_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre <> t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
  &&  “ ((rc_reserved (M_post) (t2_pre)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t2_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
).

Definition atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre <> t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
.

Definition atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre <> t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (t2_pre)) > 0) ”
.

Definition atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre <> t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (t2_pre)) > 0) ”
.

Definition atype_unify2_partial_solve_wit_10_distinct_nodes_pure_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n )) (PreH6 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH7 : (store_type M_post t2_pre tr2 )) (PreH8 : (store_type M_post t1_pre tr1 )) (PreH9 : (retval = t2_pre)) (PreH10 : (retain_rel M t2_pre M_post )) (PreH11 : (rc_valid M_post )) (PreH12 : (rc_preserves M M_post )) (PreH13 : (retval_2 = 0)) (PreH14 : (not_occur_final s (node_a (n)) tr2 )) (PreH15 : ((node_a (n)) < 100)) (PreH16 : (0 <= (node_a (n)))) (PreH17 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH18 : (n = (Node (3) ((node_a (n))) (0)))) (PreH19 : (tr1 = (TVar ((node_a (n)))))) (PreH20 : ((node_tag (n)) = 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre <> t2_pre)) (PreH31 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
.

Definition atype_unify2_partial_solve_wit_10_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n )) (PreH2 : (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (retval = t2_pre)) (PreH6 : (retain_rel M t2_pre M_post )) (PreH7 : (rc_valid M_post )) (PreH8 : (rc_preserves M M_post )) (PreH9 : (retval_2 = 0)) (PreH10 : (not_occur_final s (node_a (n)) tr2 )) (PreH11 : ((node_a (n)) < 100)) (PreH12 : (0 <= (node_a (n)))) (PreH13 : (node_at M t1_pre (Node (3) ((node_a (n))) (0)) )) (PreH14 : (n = (Node (3) ((node_a (n))) (0)))) (PreH15 : (tr1 = (TVar ((node_a (n)))))) (PreH16 : ((node_tag (n)) = 3)) (PreH17 : ((node_tag (n)) <= 3)) (PreH18 : (0 <= (node_tag (n)))) (PreH19 : (node_at M t1_pre n )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre <> t2_pre)) (PreH27 : (retval_2 = 0)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ (store_type M_post retval tr2 ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (retain_rel M retval M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t2_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (retval = t2_pre) ”
  &&  “ (retain_rel M t2_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr2 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t1_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr1 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval_2 = 0) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t1_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify2_partial_solve_wit_10_distinct_nodes := atype_unify2_partial_solve_wit_10_distinct_nodes_pure -> atype_unify2_partial_solve_wit_10_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_11_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t1_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (repr_rel_node s tr2 tr2 )) (PreH10 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH11 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_12_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <= 3)) (PreH3 : (0 <= (node_tag (n)))) (PreH4 : (node_at M t1_pre n )) (PreH5 : (rc_valid M )) (PreH6 : (store_type M t1_pre tr1 )) (PreH7 : (store_type M t2_pre tr2 )) (PreH8 : (repr_rel_node s tr1 tr1 )) (PreH9 : (repr_rel_node s tr2 tr2 )) (PreH10 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH11 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (n_2: TypeNode),
  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_13_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n_2)) = 3)) (PreH2 : ((node_tag (n_2)) <= 3)) (PreH3 : (0 <= (node_tag (n_2)))) (PreH4 : (node_at M t2_pre n_2 )) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_a (n_2)) < 100) ”
  &&  “ (0 <= (node_a (n_2))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n_2))) (0)) ) ”
  &&  “ (n_2 = (Node (3) ((node_a (n_2))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n_2))))) ”
  &&  “ ((node_tag (n_2)) = 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n_2))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_14_distinct_nodes_pure :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr2 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t2_pre n )) (PreH10 : ((node_tag (n_2)) <> 3)) (PreH11 : ((node_tag (n_2)) <= 3)) (PreH12 : (0 <= (node_tag (n_2)))) (PreH13 : (node_at M t1_pre n_2 )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  ((( &( "occur" ) )) # Int  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
.

Definition atype_unify2_partial_solve_wit_14_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (PreH1 : ((node_a (n)) < 100)) (PreH2 : (0 <= (node_a (n)))) (PreH3 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (n = (Node (3) ((node_a (n))) (0)))) (PreH5 : (tr2 = (TVar ((node_a (n)))))) (PreH6 : ((node_tag (n)) = 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t2_pre n )) (PreH10 : ((node_tag (n_2)) <> 3)) (PreH11 : ((node_tag (n_2)) <= 3)) (PreH12 : (0 <= (node_tag (n_2)))) (PreH13 : (node_at M t1_pre n_2 )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_14_distinct_nodes := atype_unify2_partial_solve_wit_14_distinct_nodes_pure -> atype_unify2_partial_solve_wit_14_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_15_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr1 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : ((node_tag (n_2)) <> 3)) (PreH13 : ((node_tag (n_2)) <= 3)) (PreH14 : (0 <= (node_tag (n_2)))) (PreH15 : (node_at M t1_pre n_2 )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M ) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
  &&  “ (0 < (rc_count (M) (t1_pre))) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr1 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr2 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t2_pre n )) (PreH16 : ((node_tag (n_2)) <> 3)) (PreH17 : ((node_tag (n_2)) <= 3)) (PreH18 : (0 <= (node_tag (n_2)))) (PreH19 : (node_at M t1_pre n_2 )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre <> t2_pre)) (PreH27 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 < (rc_count (M) (t1_pre))) ”
  &&  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
).

Definition atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr1 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr2 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t2_pre n )) (PreH16 : ((node_tag (n_2)) <> 3)) (PreH17 : ((node_tag (n_2)) <= 3)) (PreH18 : (0 <= (node_tag (n_2)))) (PreH19 : (node_at M t1_pre n_2 )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre <> t2_pre)) (PreH27 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 < (rc_count (M) (t1_pre))) ”
.

Definition atype_unify2_partial_solve_wit_15_distinct_nodes_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (not_occur_final s (node_a (n)) tr1 )) (PreH7 : ((node_a (n)) < 100)) (PreH8 : (0 <= (node_a (n)))) (PreH9 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH10 : (n = (Node (3) ((node_a (n))) (0)))) (PreH11 : (tr2 = (TVar ((node_a (n)))))) (PreH12 : ((node_tag (n)) = 3)) (PreH13 : ((node_tag (n)) <= 3)) (PreH14 : (0 <= (node_tag (n)))) (PreH15 : (node_at M t2_pre n )) (PreH16 : ((node_tag (n_2)) <> 3)) (PreH17 : ((node_tag (n_2)) <= 3)) (PreH18 : (0 <= (node_tag (n_2)))) (PreH19 : (node_at M t1_pre n_2 )) (PreH20 : (rc_valid M )) (PreH21 : (store_type M t1_pre tr1 )) (PreH22 : (store_type M t2_pre tr2 )) (PreH23 : (repr_rel_node s tr1 tr1 )) (PreH24 : (repr_rel_node s tr2 tr2 )) (PreH25 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH26 : (t1_pre <> t2_pre)) (PreH27 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
.

Definition atype_unify2_partial_solve_wit_15_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s (node_a (n)) tr1 )) (PreH3 : ((node_a (n)) < 100)) (PreH4 : (0 <= (node_a (n)))) (PreH5 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH6 : (n = (Node (3) ((node_a (n))) (0)))) (PreH7 : (tr2 = (TVar ((node_a (n)))))) (PreH8 : ((node_tag (n)) = 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t2_pre n )) (PreH12 : ((node_tag (n_2)) <> 3)) (PreH13 : ((node_tag (n_2)) <= 3)) (PreH14 : (0 <= (node_tag (n_2)))) (PreH15 : (node_at M t1_pre n_2 )) (PreH16 : (rc_valid M )) (PreH17 : (store_type M t1_pre tr1 )) (PreH18 : (store_type M t2_pre tr2 )) (PreH19 : (repr_rel_node s tr1 tr1 )) (PreH20 : (repr_rel_node s tr2 tr2 )) (PreH21 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH22 : (t1_pre <> t2_pre)) (PreH23 : (retval = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ ((rc_count (M) (t1_pre)) < INT_MAX) ”
  &&  “ (0 < (rc_count (M) (t1_pre))) ”
  &&  “ (retval = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr1 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval = 0) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_15_distinct_nodes := atype_unify2_partial_solve_wit_15_distinct_nodes_pure -> atype_unify2_partial_solve_wit_15_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_16_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n_2 )) (PreH2 : (node_at M_post t2_pre n )) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (retval = t1_pre)) (PreH7 : (retain_rel M t1_pre M_post )) (PreH8 : (rc_valid M_post )) (PreH9 : (rc_preserves M M_post )) (PreH10 : (retval_2 = 0)) (PreH11 : (not_occur_final s (node_a (n)) tr1 )) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr2 = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t2_pre n )) (PreH21 : ((node_tag (n_2)) <> 3)) (PreH22 : ((node_tag (n_2)) <= 3)) (PreH23 : (0 <= (node_tag (n_2)))) (PreH24 : (node_at M t1_pre n_2 )) (PreH25 : (rc_valid M )) (PreH26 : (store_type M t1_pre tr1 )) (PreH27 : (store_type M t2_pre tr2 )) (PreH28 : (repr_rel_node s tr1 tr1 )) (PreH29 : (repr_rel_node s tr2 tr2 )) (PreH30 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH31 : (t1_pre <> t2_pre)) (PreH32 : (retval_2 = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
  &&  “ (not_occur_final s (node_a (n)) tr1 ) ”
  &&  “ (store_type M_post retval tr1 ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (retain_rel M retval M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n_2 )) (PreH6 : (node_at M_post t2_pre n )) (PreH7 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (store_type M_post t1_pre tr1 )) (PreH10 : (retval = t1_pre)) (PreH11 : (retain_rel M t1_pre M_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (retval_2 = 0)) (PreH15 : (not_occur_final s (node_a (n)) tr1 )) (PreH16 : ((node_a (n)) < 100)) (PreH17 : (0 <= (node_a (n)))) (PreH18 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH19 : (n = (Node (3) ((node_a (n))) (0)))) (PreH20 : (tr2 = (TVar ((node_a (n)))))) (PreH21 : ((node_tag (n)) = 3)) (PreH22 : ((node_tag (n)) <= 3)) (PreH23 : (0 <= (node_tag (n)))) (PreH24 : (node_at M t2_pre n )) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t1_pre n_2 )) (PreH29 : (rc_valid M )) (PreH30 : (store_type M t1_pre tr1 )) (PreH31 : (store_type M t2_pre tr2 )) (PreH32 : (repr_rel_node s tr1 tr1 )) (PreH33 : (repr_rel_node s tr2 tr2 )) (PreH34 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH35 : (t1_pre <> t2_pre)) (PreH36 : (retval_2 = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
).

Definition atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n_2 )) (PreH6 : (node_at M_post t2_pre n )) (PreH7 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (store_type M_post t1_pre tr1 )) (PreH10 : (retval = t1_pre)) (PreH11 : (retain_rel M t1_pre M_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (retval_2 = 0)) (PreH15 : (not_occur_final s (node_a (n)) tr1 )) (PreH16 : ((node_a (n)) < 100)) (PreH17 : (0 <= (node_a (n)))) (PreH18 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH19 : (n = (Node (3) ((node_a (n))) (0)))) (PreH20 : (tr2 = (TVar ((node_a (n)))))) (PreH21 : ((node_tag (n)) = 3)) (PreH22 : ((node_tag (n)) <= 3)) (PreH23 : (0 <= (node_tag (n)))) (PreH24 : (node_at M t2_pre n )) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t1_pre n_2 )) (PreH29 : (rc_valid M )) (PreH30 : (store_type M t1_pre tr1 )) (PreH31 : (store_type M t2_pre tr2 )) (PreH32 : (repr_rel_node s tr1 tr1 )) (PreH33 : (repr_rel_node s tr2 tr2 )) (PreH34 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH35 : (t1_pre <> t2_pre)) (PreH36 : (retval_2 = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
.

Definition atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_2 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n_2 )) (PreH6 : (node_at M_post t2_pre n )) (PreH7 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (store_type M_post t1_pre tr1 )) (PreH10 : (retval = t1_pre)) (PreH11 : (retain_rel M t1_pre M_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (retval_2 = 0)) (PreH15 : (not_occur_final s (node_a (n)) tr1 )) (PreH16 : ((node_a (n)) < 100)) (PreH17 : (0 <= (node_a (n)))) (PreH18 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH19 : (n = (Node (3) ((node_a (n))) (0)))) (PreH20 : (tr2 = (TVar ((node_a (n)))))) (PreH21 : ((node_tag (n)) = 3)) (PreH22 : ((node_tag (n)) <= 3)) (PreH23 : (0 <= (node_tag (n)))) (PreH24 : (node_at M t2_pre n )) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t1_pre n_2 )) (PreH29 : (rc_valid M )) (PreH30 : (store_type M t1_pre tr1 )) (PreH31 : (store_type M t2_pre tr2 )) (PreH32 : (repr_rel_node s tr1 tr1 )) (PreH33 : (repr_rel_node s tr2 tr2 )) (PreH34 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH35 : (t1_pre <> t2_pre)) (PreH36 : (retval_2 = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
.

Definition atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_3 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n_2 )) (PreH6 : (node_at M_post t2_pre n )) (PreH7 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (store_type M_post t1_pre tr1 )) (PreH10 : (retval = t1_pre)) (PreH11 : (retain_rel M t1_pre M_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (retval_2 = 0)) (PreH15 : (not_occur_final s (node_a (n)) tr1 )) (PreH16 : ((node_a (n)) < 100)) (PreH17 : (0 <= (node_a (n)))) (PreH18 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH19 : (n = (Node (3) ((node_a (n))) (0)))) (PreH20 : (tr2 = (TVar ((node_a (n)))))) (PreH21 : ((node_tag (n)) = 3)) (PreH22 : ((node_tag (n)) <= 3)) (PreH23 : (0 <= (node_tag (n)))) (PreH24 : (node_at M t2_pre n )) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t1_pre n_2 )) (PreH29 : (rc_valid M )) (PreH30 : (store_type M t1_pre tr1 )) (PreH31 : (store_type M t2_pre tr2 )) (PreH32 : (repr_rel_node s tr1 tr1 )) (PreH33 : (repr_rel_node s tr2 tr2 )) (PreH34 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH35 : (t1_pre <> t2_pre)) (PreH36 : (retval_2 = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
.

Definition atype_unify2_partial_solve_wit_16_distinct_nodes_pure_split_goal_4 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (retval_2 <= INT_MAX)) (PreH2 : ((node_a (n)) <= INT_MAX)) (PreH3 : (retval_2 >= INT_MIN)) (PreH4 : ((node_a (n)) >= INT_MIN)) (PreH5 : (node_at M_post t1_pre n_2 )) (PreH6 : (node_at M_post t2_pre n )) (PreH7 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH8 : (store_type M_post t2_pre tr2 )) (PreH9 : (store_type M_post t1_pre tr1 )) (PreH10 : (retval = t1_pre)) (PreH11 : (retain_rel M t1_pre M_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (retval_2 = 0)) (PreH15 : (not_occur_final s (node_a (n)) tr1 )) (PreH16 : ((node_a (n)) < 100)) (PreH17 : (0 <= (node_a (n)))) (PreH18 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH19 : (n = (Node (3) ((node_a (n))) (0)))) (PreH20 : (tr2 = (TVar ((node_a (n)))))) (PreH21 : ((node_tag (n)) = 3)) (PreH22 : ((node_tag (n)) <= 3)) (PreH23 : (0 <= (node_tag (n)))) (PreH24 : (node_at M t2_pre n )) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t1_pre n_2 )) (PreH29 : (rc_valid M )) (PreH30 : (store_type M t1_pre tr1 )) (PreH31 : (store_type M t2_pre tr2 )) (PreH32 : (repr_rel_node s tr1 tr1 )) (PreH33 : (repr_rel_node s tr2 tr2 )) (PreH34 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH35 : (t1_pre <> t2_pre)) (PreH36 : (retval_2 = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
  **  ((( &( "occur" ) )) # Int  |-> retval_2)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
.

Definition atype_unify2_partial_solve_wit_16_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n_2: TypeNode) (n: TypeNode) (retval_2: Z) (M_post: RcState) (retval: Z) (PreH1 : (node_at M_post t1_pre n_2 )) (PreH2 : (node_at M_post t2_pre n )) (PreH3 : (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (retval = t1_pre)) (PreH7 : (retain_rel M t1_pre M_post )) (PreH8 : (rc_valid M_post )) (PreH9 : (rc_preserves M M_post )) (PreH10 : (retval_2 = 0)) (PreH11 : (not_occur_final s (node_a (n)) tr1 )) (PreH12 : ((node_a (n)) < 100)) (PreH13 : (0 <= (node_a (n)))) (PreH14 : (node_at M t2_pre (Node (3) ((node_a (n))) (0)) )) (PreH15 : (n = (Node (3) ((node_a (n))) (0)))) (PreH16 : (tr2 = (TVar ((node_a (n)))))) (PreH17 : ((node_tag (n)) = 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t2_pre n )) (PreH21 : ((node_tag (n_2)) <> 3)) (PreH22 : ((node_tag (n_2)) <= 3)) (PreH23 : (0 <= (node_tag (n_2)))) (PreH24 : (node_at M t1_pre n_2 )) (PreH25 : (rc_valid M )) (PreH26 : (store_type M t1_pre tr1 )) (PreH27 : (store_type M t2_pre tr2 )) (PreH28 : (repr_rel_node s tr1 tr1 )) (PreH29 : (repr_rel_node s tr2 tr2 )) (PreH30 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH31 : (t1_pre <> t2_pre)) (PreH32 : (retval_2 = 0)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (0 <= (node_a (n))) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a (n)) old )) ”
  &&  “ (not_occur_final s (node_a (n)) tr1 ) ”
  &&  “ (store_type M_post retval tr1 ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (retain_rel M retval M_post ) ”
  &&  “ ((rc_reserved (M_post) (retval)) > 0) ”
  &&  “ ((rc_reserved (M_post) (t1_pre)) > 0) ”
  &&  “ forall (old: TypeTree), ~((solution_at s (node_a ((Node (3) ((node_a (n))) (0)))) old )) ”
  &&  “ (node_at M_post t1_pre n_2 ) ”
  &&  “ (node_at M_post t2_pre n ) ”
  &&  “ (node_at M_post t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (retval = t1_pre) ”
  &&  “ (retain_rel M t1_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (retval_2 = 0) ”
  &&  “ (not_occur_final s (node_a (n)) tr1 ) ”
  &&  “ ((node_a (n)) < 100) ”
  &&  “ (0 <= (node_a (n))) ”
  &&  “ (node_at M t2_pre (Node (3) ((node_a (n))) (0)) ) ”
  &&  “ (n = (Node (3) ((node_a (n))) (0))) ”
  &&  “ (tr2 = (TVar ((node_a (n))))) ”
  &&  “ ((node_tag (n)) = 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t2_pre n ) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t1_pre n_2 ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  “ (retval_2 = 0) ”
  &&  (store_solution M ( &( "res" ) ) s )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M_post (payload_keys (t2_pre) ((Node (3) ((node_a (n))) (0)))) )
.

Definition atype_unify2_partial_solve_wit_16_distinct_nodes := atype_unify2_partial_solve_wit_16_distinct_nodes_pure -> atype_unify2_partial_solve_wit_16_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_17_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <> 3)) (PreH3 : ((node_tag (n)) <= 3)) (PreH4 : (0 <= (node_tag (n)))) (PreH5 : (node_at M t1_pre n )) (PreH6 : (rc_valid M )) (PreH7 : (store_type M t1_pre tr1 )) (PreH8 : (store_type M t2_pre tr2 )) (PreH9 : (repr_rel_node s tr1 tr1 )) (PreH10 : (repr_rel_node s tr2 tr2 )) (PreH11 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH12 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_18_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <> 3)) (PreH3 : ((node_tag (n)) <= 3)) (PreH4 : (0 <= (node_tag (n)))) (PreH5 : (node_at M t1_pre n )) (PreH6 : (rc_valid M )) (PreH7 : (store_type M t1_pre tr1 )) (PreH8 : (store_type M t2_pre tr2 )) (PreH9 : (repr_rel_node s tr1 tr1 )) (PreH10 : (repr_rel_node s tr2 tr2 )) (PreH11 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH12 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_19_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 3)) (PreH2 : ((node_tag (n)) <> 3)) (PreH3 : ((node_tag (n)) <= 3)) (PreH4 : (0 <= (node_tag (n)))) (PreH5 : (node_at M t1_pre n )) (PreH6 : (rc_valid M )) (PreH7 : (store_type M t1_pre tr1 )) (PreH8 : (store_type M t2_pre tr2 )) (PreH9 : (repr_rel_node s tr1 tr1 )) (PreH10 : (repr_rel_node s tr2 tr2 )) (PreH11 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH12 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_20_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) = 1)) (PreH2 : ((node_tag (n)) = (node_tag (n_2)))) (PreH3 : ((node_tag (n_2)) <> 3)) (PreH4 : ((node_tag (n_2)) <= 3)) (PreH5 : (0 <= (node_tag (n_2)))) (PreH6 : (node_at M t2_pre n_2 )) (PreH7 : ((node_tag (n)) <> 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (a: TypeTree) (b: TypeTree),
  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))) )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_21_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 1)) (PreH2 : ((node_tag (n)) <> 3)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <= 3)) (PreH5 : (0 <= (node_tag (n)))) (PreH6 : (node_at M t1_pre n )) (PreH7 : (rc_valid M )) (PreH8 : (store_type M t1_pre tr1 )) (PreH9 : (store_type M t2_pre tr2 )) (PreH10 : (repr_rel_node s tr1 tr1 )) (PreH11 : (repr_rel_node s tr2 tr2 )) (PreH12 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH13 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (a: TypeTree) (b: TypeTree),
  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_22_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TArrow (a) (b)))) (PreH4 : ((node_tag (n)) = 1)) (PreH5 : ((node_tag (n)) = (node_tag (n_2)))) (PreH6 : ((node_tag (n_2)) <> 3)) (PreH7 : ((node_tag (n_2)) <= 3)) (PreH8 : (0 <= (node_tag (n_2)))) (PreH9 : (node_at M t2_pre n_2 )) (PreH10 : ((node_tag (n)) <> 3)) (PreH11 : ((node_tag (n)) <= 3)) (PreH12 : (0 <= (node_tag (n)))) (PreH13 : (node_at M t1_pre n )) (PreH14 : (rc_valid M )) (PreH15 : (store_type M t1_pre tr1 )) (PreH16 : (store_type M t2_pre tr2 )) (PreH17 : (repr_rel_node s tr1 tr1 )) (PreH18 : (repr_rel_node s tr2 tr2 )) (PreH19 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH20 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))) )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (a_2: TypeTree) (b_2: TypeTree),
  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TArrow (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_23_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TArrow (a) (b)))) (PreH4 : ((node_tag (n)) = 1)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_24_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : (store_type M (node_b (n_2)) b_2 )) (PreH2 : (store_type M (node_a (n_2)) a_2 )) (PreH3 : (tr2 = (TArrow (a_2) (b_2)))) (PreH4 : (store_type M (node_b (n)) b )) (PreH5 : (store_type M (node_a (n)) a )) (PreH6 : (tr1 = (TArrow (a) (b)))) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : ((node_tag (n)) = (node_tag (n_2)))) (PreH9 : ((node_tag (n_2)) <> 3)) (PreH10 : ((node_tag (n_2)) <= 3)) (PreH11 : (0 <= (node_tag (n_2)))) (PreH12 : (node_at M t2_pre n_2 )) (PreH13 : ((node_tag (n)) <> 3)) (PreH14 : ((node_tag (n)) <= 3)) (PreH15 : (0 <= (node_tag (n)))) (PreH16 : (node_at M t1_pre n )) (PreH17 : (rc_valid M )) (PreH18 : (store_type M t1_pre tr1 )) (PreH19 : (store_type M t2_pre tr2 )) (PreH20 : (repr_rel_node s tr1 tr1 )) (PreH21 : (repr_rel_node s tr2 tr2 )) (PreH22 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH23 : (t1_pre <> t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n_2)) <= INT_MAX)) (PreH3 : ((node_tag (n)) >= INT_MIN)) (PreH4 : ((node_tag (n_2)) >= INT_MIN)) (PreH5 : (store_type M (node_b (n_2)) b_2 )) (PreH6 : (store_type M (node_a (n_2)) a_2 )) (PreH7 : (tr2 = (TArrow (a_2) (b_2)))) (PreH8 : (store_type M (node_b (n)) b )) (PreH9 : (store_type M (node_a (n)) a )) (PreH10 : (tr1 = (TArrow (a) (b)))) (PreH11 : ((node_tag (n)) = 1)) (PreH12 : ((node_tag (n)) = (node_tag (n_2)))) (PreH13 : ((node_tag (n_2)) <> 3)) (PreH14 : ((node_tag (n_2)) <= 3)) (PreH15 : (0 <= (node_tag (n_2)))) (PreH16 : (node_at M t2_pre n_2 )) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre <> t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
).

Definition atype_unify2_partial_solve_wit_24_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n_2)) <= INT_MAX)) (PreH3 : ((node_tag (n)) >= INT_MIN)) (PreH4 : ((node_tag (n_2)) >= INT_MIN)) (PreH5 : (store_type M (node_b (n_2)) b_2 )) (PreH6 : (store_type M (node_a (n_2)) a_2 )) (PreH7 : (tr2 = (TArrow (a_2) (b_2)))) (PreH8 : (store_type M (node_b (n)) b )) (PreH9 : (store_type M (node_a (n)) a )) (PreH10 : (tr1 = (TArrow (a) (b)))) (PreH11 : ((node_tag (n)) = 1)) (PreH12 : ((node_tag (n)) = (node_tag (n_2)))) (PreH13 : ((node_tag (n_2)) <> 3)) (PreH14 : ((node_tag (n_2)) <= 3)) (PreH15 : (0 <= (node_tag (n_2)))) (PreH16 : (node_at M t2_pre n_2 )) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <= 3)) (PreH19 : (0 <= (node_tag (n)))) (PreH20 : (node_at M t1_pre n )) (PreH21 : (rc_valid M )) (PreH22 : (store_type M t1_pre tr1 )) (PreH23 : (store_type M t2_pre tr2 )) (PreH24 : (repr_rel_node s tr1 tr1 )) (PreH25 : (repr_rel_node s tr2 tr2 )) (PreH26 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH27 : (t1_pre <> t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
.

Definition atype_unify2_partial_solve_wit_24_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : (store_type M (node_b (n_2)) b_2 )) (PreH2 : (store_type M (node_a (n_2)) a_2 )) (PreH3 : (tr2 = (TArrow (a_2) (b_2)))) (PreH4 : (store_type M (node_b (n)) b )) (PreH5 : (store_type M (node_a (n)) a )) (PreH6 : (tr1 = (TArrow (a) (b)))) (PreH7 : ((node_tag (n)) = 1)) (PreH8 : ((node_tag (n)) = (node_tag (n_2)))) (PreH9 : ((node_tag (n_2)) <> 3)) (PreH10 : ((node_tag (n_2)) <= 3)) (PreH11 : (0 <= (node_tag (n_2)))) (PreH12 : (node_at M t2_pre n_2 )) (PreH13 : ((node_tag (n)) <> 3)) (PreH14 : ((node_tag (n)) <= 3)) (PreH15 : (0 <= (node_tag (n)))) (PreH16 : (node_at M t1_pre n )) (PreH17 : (rc_valid M )) (PreH18 : (store_type M t1_pre tr1 )) (PreH19 : (store_type M t2_pre tr2 )) (PreH20 : (repr_rel_node s tr1 tr1 )) (PreH21 : (repr_rel_node s tr2 tr2 )) (PreH22 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH23 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TArrow (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_24_distinct_nodes := atype_unify2_partial_solve_wit_24_distinct_nodes_pure -> atype_unify2_partial_solve_wit_24_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_25_same_node_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TArrow (a) (b)))) (PreH4 : ((node_tag (n)) = 1)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre = t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : (store_type M (node_b (n)) b )) (PreH4 : (store_type M (node_a (n)) a )) (PreH5 : (tr1 = (TArrow (a) (b)))) (PreH6 : ((node_tag (n)) = 1)) (PreH7 : ((node_tag (n)) <> 3)) (PreH8 : ((node_tag (n)) <> 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
).

Definition atype_unify2_partial_solve_wit_25_same_node_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : (store_type M (node_b (n)) b )) (PreH4 : (store_type M (node_a (n)) a )) (PreH5 : (tr1 = (TArrow (a) (b)))) (PreH6 : ((node_tag (n)) = 1)) (PreH7 : ((node_tag (n)) <> 3)) (PreH8 : ((node_tag (n)) <> 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre = t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
.

Definition atype_unify2_partial_solve_wit_25_same_node_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TArrow (a) (b)))) (PreH4 : ((node_tag (n)) = 1)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <= 3)) (PreH8 : (0 <= (node_tag (n)))) (PreH9 : (node_at M t1_pre n )) (PreH10 : (rc_valid M )) (PreH11 : (store_type M t1_pre tr1 )) (PreH12 : (store_type M t2_pre tr2 )) (PreH13 : (repr_rel_node s tr1 tr1 )) (PreH14 : (repr_rel_node s tr2 tr2 )) (PreH15 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH16 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_25_same_node := atype_unify2_partial_solve_wit_25_same_node_pure -> atype_unify2_partial_solve_wit_25_same_node_aux.

Definition atype_unify2_partial_solve_wit_26_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TArrow (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TArrow (a) (b)))) (PreH22 : ((node_tag (n)) = 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t2_pre n_2 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_a (n_2)) a_2 ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a_2 s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TArrow (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_27_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TArrow (a) (b)))) (PreH16 : ((node_tag (n)) = 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_28_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TArrow (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TArrow (a) (b)))) (PreH22 : ((node_tag (n)) = 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t2_pre n_2 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_a (n_2)) a_2 ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a_2 s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TArrow (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_29_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TArrow (a) (b)))) (PreH16 : ((node_tag (n)) = 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_30_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TArrow (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TArrow (a) (b)))) (PreH22 : ((node_tag (n)) = 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((( &( "arrow_to2" ) )) # Ptr  |-> (node_b (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((( &( "arrow_to1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (node_at M_post t2_pre n_2 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post (node_a (n)) a )) (PreH9 : (store_type M_post (node_b (n)) b )) (PreH10 : (store_type M_post (node_a (n_2)) a_2 )) (PreH11 : (store_type M_post (node_b (n_2)) b_2 )) (PreH12 : (retval = 0)) (PreH13 : (unify_rel a a_2 s s_post )) (PreH14 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH15 : (rc_valid M_post )) (PreH16 : (rc_preserves M M_post )) (PreH17 : (rc_reservations_same M M_post )) (PreH18 : (store_type M (node_b (n_2)) b_2 )) (PreH19 : (store_type M (node_a (n_2)) a_2 )) (PreH20 : (tr2 = (TArrow (a_2) (b_2)))) (PreH21 : (store_type M (node_b (n)) b )) (PreH22 : (store_type M (node_a (n)) a )) (PreH23 : (tr1 = (TArrow (a) (b)))) (PreH24 : ((node_tag (n)) = 1)) (PreH25 : ((node_tag (n)) = (node_tag (n_2)))) (PreH26 : ((node_tag (n_2)) <> 3)) (PreH27 : ((node_tag (n_2)) <= 3)) (PreH28 : (0 <= (node_tag (n_2)))) (PreH29 : (node_at M t2_pre n_2 )) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((( &( "arrow_to2" ) )) # Ptr  |-> (node_b (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((( &( "arrow_to1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
).

Definition atype_unify2_partial_solve_wit_30_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (node_at M_post t2_pre n_2 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post (node_a (n)) a )) (PreH9 : (store_type M_post (node_b (n)) b )) (PreH10 : (store_type M_post (node_a (n_2)) a_2 )) (PreH11 : (store_type M_post (node_b (n_2)) b_2 )) (PreH12 : (retval = 0)) (PreH13 : (unify_rel a a_2 s s_post )) (PreH14 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH15 : (rc_valid M_post )) (PreH16 : (rc_preserves M M_post )) (PreH17 : (rc_reservations_same M M_post )) (PreH18 : (store_type M (node_b (n_2)) b_2 )) (PreH19 : (store_type M (node_a (n_2)) a_2 )) (PreH20 : (tr2 = (TArrow (a_2) (b_2)))) (PreH21 : (store_type M (node_b (n)) b )) (PreH22 : (store_type M (node_a (n)) a )) (PreH23 : (tr1 = (TArrow (a) (b)))) (PreH24 : ((node_tag (n)) = 1)) (PreH25 : ((node_tag (n)) = (node_tag (n_2)))) (PreH26 : ((node_tag (n_2)) <> 3)) (PreH27 : ((node_tag (n_2)) <= 3)) (PreH28 : (0 <= (node_tag (n_2)))) (PreH29 : (node_at M t2_pre n_2 )) (PreH30 : ((node_tag (n)) <> 3)) (PreH31 : ((node_tag (n)) <= 3)) (PreH32 : (0 <= (node_tag (n)))) (PreH33 : (node_at M t1_pre n )) (PreH34 : (rc_valid M )) (PreH35 : (store_type M t1_pre tr1 )) (PreH36 : (store_type M t2_pre tr2 )) (PreH37 : (repr_rel_node s tr1 tr1 )) (PreH38 : (repr_rel_node s tr2 tr2 )) (PreH39 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH40 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((( &( "arrow_to2" ) )) # Ptr  |-> (node_b (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((( &( "arrow_to1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
.

Definition atype_unify2_partial_solve_wit_30_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TArrow (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TArrow (a) (b)))) (PreH22 : ((node_tag (n)) = 1)) (PreH23 : ((node_tag (n)) = (node_tag (n_2)))) (PreH24 : ((node_tag (n_2)) <> 3)) (PreH25 : ((node_tag (n_2)) <= 3)) (PreH26 : (0 <= (node_tag (n_2)))) (PreH27 : (node_at M t2_pre n_2 )) (PreH28 : ((node_tag (n)) <> 3)) (PreH29 : ((node_tag (n)) <= 3)) (PreH30 : (0 <= (node_tag (n)))) (PreH31 : (node_at M t1_pre n )) (PreH32 : (rc_valid M )) (PreH33 : (store_type M t1_pre tr1 )) (PreH34 : (store_type M t2_pre tr2 )) (PreH35 : (repr_rel_node s tr1 tr1 )) (PreH36 : (repr_rel_node s tr2 tr2 )) (PreH37 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH38 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
  &&  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t2_pre n_2 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_a (n_2)) a_2 ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a_2 s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TArrow (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_30_distinct_nodes := atype_unify2_partial_solve_wit_30_distinct_nodes_pure -> atype_unify2_partial_solve_wit_30_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_31_same_node_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TArrow (a) (b)))) (PreH16 : ((node_tag (n)) = 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((( &( "arrow_to2" ) )) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  ((( &( "arrow_to1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post t2_pre tr2 )) (PreH6 : (store_type M_post t1_pre tr1 )) (PreH7 : (store_type M_post (node_a (n)) a )) (PreH8 : (store_type M_post (node_b (n)) b )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel a a s s_post )) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n)) b )) (PreH16 : (store_type M (node_a (n)) a )) (PreH17 : (tr1 = (TArrow (a) (b)))) (PreH18 : ((node_tag (n)) = 1)) (PreH19 : ((node_tag (n)) <> 3)) (PreH20 : ((node_tag (n)) <> 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((( &( "arrow_to2" ) )) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  ((( &( "arrow_to1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
).

Definition atype_unify2_partial_solve_wit_31_same_node_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post t2_pre tr2 )) (PreH6 : (store_type M_post t1_pre tr1 )) (PreH7 : (store_type M_post (node_a (n)) a )) (PreH8 : (store_type M_post (node_b (n)) b )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel a a s s_post )) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n)) b )) (PreH16 : (store_type M (node_a (n)) a )) (PreH17 : (tr1 = (TArrow (a) (b)))) (PreH18 : ((node_tag (n)) = 1)) (PreH19 : ((node_tag (n)) <> 3)) (PreH20 : ((node_tag (n)) <> 3)) (PreH21 : ((node_tag (n)) <= 3)) (PreH22 : (0 <= (node_tag (n)))) (PreH23 : (node_at M t1_pre n )) (PreH24 : (rc_valid M )) (PreH25 : (store_type M t1_pre tr1 )) (PreH26 : (store_type M t2_pre tr2 )) (PreH27 : (repr_rel_node s tr1 tr1 )) (PreH28 : (repr_rel_node s tr2 tr2 )) (PreH29 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH30 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  ((( &( "arrow_to2" ) )) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  ((( &( "arrow_to1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "arrow_from2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "arrow_from1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
.

Definition atype_unify2_partial_solve_wit_31_same_node_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TArrow (a) (b)))) (PreH16 : ((node_tag (n)) = 1)) (PreH17 : ((node_tag (n)) <> 3)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
  &&  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TArrow (a) (b))) ”
  &&  “ ((node_tag (n)) = 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_31_same_node := atype_unify2_partial_solve_wit_31_same_node_pure -> atype_unify2_partial_solve_wit_31_same_node_aux.

Definition atype_unify2_partial_solve_wit_32_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 2)) (PreH2 : ((node_tag (n)) <> 1)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <= 3)) (PreH6 : (0 <= (node_tag (n)))) (PreH7 : (node_at M t1_pre n )) (PreH8 : (rc_valid M )) (PreH9 : (store_type M t1_pre tr1 )) (PreH10 : (store_type M t2_pre tr2 )) (PreH11 : (repr_rel_node s tr1 tr1 )) (PreH12 : (repr_rel_node s tr2 tr2 )) (PreH13 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH14 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (a: TypeTree) (b: TypeTree),
  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_33_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) = 2)) (PreH2 : ((node_tag (n)) <> 1)) (PreH3 : ((node_tag (n)) = (node_tag (n_2)))) (PreH4 : ((node_tag (n_2)) <> 3)) (PreH5 : ((node_tag (n_2)) <= 3)) (PreH6 : (0 <= (node_tag (n_2)))) (PreH7 : (node_at M t2_pre n_2 )) (PreH8 : ((node_tag (n)) <> 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (a: TypeTree) (b: TypeTree),
  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))) )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_34_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TApply (a) (b)))) (PreH4 : ((node_tag (n)) = 2)) (PreH5 : ((node_tag (n)) <> 1)) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <> 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_35_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TApply (a) (b)))) (PreH4 : ((node_tag (n)) = 2)) (PreH5 : ((node_tag (n)) <> 1)) (PreH6 : ((node_tag (n)) = (node_tag (n_2)))) (PreH7 : ((node_tag (n_2)) <> 3)) (PreH8 : ((node_tag (n_2)) <= 3)) (PreH9 : (0 <= (node_tag (n_2)))) (PreH10 : (node_at M t2_pre n_2 )) (PreH11 : ((node_tag (n)) <> 3)) (PreH12 : ((node_tag (n)) <= 3)) (PreH13 : (0 <= (node_tag (n)))) (PreH14 : (node_at M t1_pre n )) (PreH15 : (rc_valid M )) (PreH16 : (store_type M t1_pre tr1 )) (PreH17 : (store_type M t2_pre tr2 )) (PreH18 : (repr_rel_node s tr1 tr1 )) (PreH19 : (repr_rel_node s tr2 tr2 )) (PreH20 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH21 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))) )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  EX (a_2: TypeTree) (b_2: TypeTree),
  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TApply (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_36_same_node_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TApply (a) (b)))) (PreH4 : ((node_tag (n)) = 2)) (PreH5 : ((node_tag (n)) <> 1)) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <> 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : (store_type M (node_b (n)) b )) (PreH4 : (store_type M (node_a (n)) a )) (PreH5 : (tr1 = (TApply (a) (b)))) (PreH6 : ((node_tag (n)) = 2)) (PreH7 : ((node_tag (n)) <> 1)) (PreH8 : ((node_tag (n)) <> 3)) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t1_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (repr_rel_node s tr2 tr2 )) (PreH18 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH19 : (t1_pre = t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
).

Definition atype_unify2_partial_solve_wit_36_same_node_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n)) >= INT_MIN)) (PreH3 : (store_type M (node_b (n)) b )) (PreH4 : (store_type M (node_a (n)) a )) (PreH5 : (tr1 = (TApply (a) (b)))) (PreH6 : ((node_tag (n)) = 2)) (PreH7 : ((node_tag (n)) <> 1)) (PreH8 : ((node_tag (n)) <> 3)) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t1_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (repr_rel_node s tr2 tr2 )) (PreH18 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH19 : (t1_pre = t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
.

Definition atype_unify2_partial_solve_wit_36_same_node_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (PreH1 : (store_type M (node_b (n)) b )) (PreH2 : (store_type M (node_a (n)) a )) (PreH3 : (tr1 = (TApply (a) (b)))) (PreH4 : ((node_tag (n)) = 2)) (PreH5 : ((node_tag (n)) <> 1)) (PreH6 : ((node_tag (n)) <> 3)) (PreH7 : ((node_tag (n)) <> 3)) (PreH8 : ((node_tag (n)) <= 3)) (PreH9 : (0 <= (node_tag (n)))) (PreH10 : (node_at M t1_pre n )) (PreH11 : (rc_valid M )) (PreH12 : (store_type M t1_pre tr1 )) (PreH13 : (store_type M t2_pre tr2 )) (PreH14 : (repr_rel_node s tr1 tr1 )) (PreH15 : (repr_rel_node s tr2 tr2 )) (PreH16 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH17 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n)) ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_36_same_node := atype_unify2_partial_solve_wit_36_same_node_pure -> atype_unify2_partial_solve_wit_36_same_node_aux.

Definition atype_unify2_partial_solve_wit_37_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : (store_type M (node_b (n_2)) b_2 )) (PreH2 : (store_type M (node_a (n_2)) a_2 )) (PreH3 : (tr2 = (TApply (a_2) (b_2)))) (PreH4 : (store_type M (node_b (n)) b )) (PreH5 : (store_type M (node_a (n)) a )) (PreH6 : (tr1 = (TApply (a) (b)))) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : ((node_tag (n)) <> 1)) (PreH9 : ((node_tag (n)) = (node_tag (n_2)))) (PreH10 : ((node_tag (n_2)) <> 3)) (PreH11 : ((node_tag (n_2)) <= 3)) (PreH12 : (0 <= (node_tag (n_2)))) (PreH13 : (node_at M t2_pre n_2 )) (PreH14 : ((node_tag (n)) <> 3)) (PreH15 : ((node_tag (n)) <= 3)) (PreH16 : (0 <= (node_tag (n)))) (PreH17 : (node_at M t1_pre n )) (PreH18 : (rc_valid M )) (PreH19 : (store_type M t1_pre tr1 )) (PreH20 : (store_type M t2_pre tr2 )) (PreH21 : (repr_rel_node s tr1 tr1 )) (PreH22 : (repr_rel_node s tr2 tr2 )) (PreH23 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH24 : (t1_pre <> t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n_2)) <= INT_MAX)) (PreH3 : ((node_tag (n)) >= INT_MIN)) (PreH4 : ((node_tag (n_2)) >= INT_MIN)) (PreH5 : (store_type M (node_b (n_2)) b_2 )) (PreH6 : (store_type M (node_a (n_2)) a_2 )) (PreH7 : (tr2 = (TApply (a_2) (b_2)))) (PreH8 : (store_type M (node_b (n)) b )) (PreH9 : (store_type M (node_a (n)) a )) (PreH10 : (tr1 = (TApply (a) (b)))) (PreH11 : ((node_tag (n)) = 2)) (PreH12 : ((node_tag (n)) <> 1)) (PreH13 : ((node_tag (n)) = (node_tag (n_2)))) (PreH14 : ((node_tag (n_2)) <> 3)) (PreH15 : ((node_tag (n_2)) <= 3)) (PreH16 : (0 <= (node_tag (n_2)))) (PreH17 : (node_at M t2_pre n_2 )) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre <> t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
).

Definition atype_unify2_partial_solve_wit_37_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : ((node_tag (n)) <= INT_MAX)) (PreH2 : ((node_tag (n_2)) <= INT_MAX)) (PreH3 : ((node_tag (n)) >= INT_MIN)) (PreH4 : ((node_tag (n_2)) >= INT_MIN)) (PreH5 : (store_type M (node_b (n_2)) b_2 )) (PreH6 : (store_type M (node_a (n_2)) a_2 )) (PreH7 : (tr2 = (TApply (a_2) (b_2)))) (PreH8 : (store_type M (node_b (n)) b )) (PreH9 : (store_type M (node_a (n)) a )) (PreH10 : (tr1 = (TApply (a) (b)))) (PreH11 : ((node_tag (n)) = 2)) (PreH12 : ((node_tag (n)) <> 1)) (PreH13 : ((node_tag (n)) = (node_tag (n_2)))) (PreH14 : ((node_tag (n_2)) <> 3)) (PreH15 : ((node_tag (n_2)) <= 3)) (PreH16 : (0 <= (node_tag (n_2)))) (PreH17 : (node_at M t2_pre n_2 )) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <= 3)) (PreH20 : (0 <= (node_tag (n)))) (PreH21 : (node_at M t1_pre n )) (PreH22 : (rc_valid M )) (PreH23 : (store_type M t1_pre tr1 )) (PreH24 : (store_type M t2_pre tr2 )) (PreH25 : (repr_rel_node s tr1 tr1 )) (PreH26 : (repr_rel_node s tr2 tr2 )) (PreH27 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH28 : (t1_pre <> t2_pre)),
  ((( &( "r" ) )) # Int  |->_)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
.

Definition atype_unify2_partial_solve_wit_37_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (PreH1 : (store_type M (node_b (n_2)) b_2 )) (PreH2 : (store_type M (node_a (n_2)) a_2 )) (PreH3 : (tr2 = (TApply (a_2) (b_2)))) (PreH4 : (store_type M (node_b (n)) b )) (PreH5 : (store_type M (node_a (n)) a )) (PreH6 : (tr1 = (TApply (a) (b)))) (PreH7 : ((node_tag (n)) = 2)) (PreH8 : ((node_tag (n)) <> 1)) (PreH9 : ((node_tag (n)) = (node_tag (n_2)))) (PreH10 : ((node_tag (n_2)) <> 3)) (PreH11 : ((node_tag (n_2)) <= 3)) (PreH12 : (0 <= (node_tag (n_2)))) (PreH13 : (node_at M t2_pre n_2 )) (PreH14 : ((node_tag (n)) <> 3)) (PreH15 : ((node_tag (n)) <= 3)) (PreH16 : (0 <= (node_tag (n)))) (PreH17 : (node_at M t1_pre n )) (PreH18 : (rc_valid M )) (PreH19 : (store_type M t1_pre tr1 )) (PreH20 : (store_type M t2_pre tr2 )) (PreH21 : (repr_rel_node s tr1 tr1 )) (PreH22 : (repr_rel_node s tr2 tr2 )) (PreH23 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH24 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ (rc_valid M ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (rc_capacity 0 M s (node_a (n)) (node_a (n_2)) ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TApply (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_37_distinct_nodes := atype_unify2_partial_solve_wit_37_distinct_nodes_pure -> atype_unify2_partial_solve_wit_37_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_38_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TApply (a) (b)))) (PreH16 : ((node_tag (n)) = 2)) (PreH17 : ((node_tag (n)) <> 1)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <> 3)) (PreH20 : ((node_tag (n)) <= 3)) (PreH21 : (0 <= (node_tag (n)))) (PreH22 : (node_at M t1_pre n )) (PreH23 : (rc_valid M )) (PreH24 : (store_type M t1_pre tr1 )) (PreH25 : (store_type M t2_pre tr2 )) (PreH26 : (repr_rel_node s tr1 tr1 )) (PreH27 : (repr_rel_node s tr2 tr2 )) (PreH28 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH29 : (t1_pre = t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_39_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TApply (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TApply (a) (b)))) (PreH22 : ((node_tag (n)) = 2)) (PreH23 : ((node_tag (n)) <> 1)) (PreH24 : ((node_tag (n)) = (node_tag (n_2)))) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t2_pre n_2 )) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre <> t2_pre)),
  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t2_pre n_2 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_a (n_2)) a_2 ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a_2 s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TApply (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_40_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TApply (a) (b)))) (PreH16 : ((node_tag (n)) = 2)) (PreH17 : ((node_tag (n)) <> 1)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <> 3)) (PreH20 : ((node_tag (n)) <= 3)) (PreH21 : (0 <= (node_tag (n)))) (PreH22 : (node_at M t1_pre n )) (PreH23 : (rc_valid M )) (PreH24 : (store_type M t1_pre tr1 )) (PreH25 : (store_type M t2_pre tr2 )) (PreH26 : (repr_rel_node s tr1 tr1 )) (PreH27 : (repr_rel_node s tr2 tr2 )) (PreH28 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH29 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_41_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TApply (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TApply (a) (b)))) (PreH22 : ((node_tag (n)) = 2)) (PreH23 : ((node_tag (n)) <> 1)) (PreH24 : ((node_tag (n)) = (node_tag (n_2)))) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t2_pre n_2 )) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t2_pre n_2 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_a (n_2)) a_2 ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a_2 s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TApply (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_42_same_node_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TApply (a) (b)))) (PreH16 : ((node_tag (n)) = 2)) (PreH17 : ((node_tag (n)) <> 1)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <> 3)) (PreH20 : ((node_tag (n)) <= 3)) (PreH21 : (0 <= (node_tag (n)))) (PreH22 : (node_at M t1_pre n )) (PreH23 : (rc_valid M )) (PreH24 : (store_type M t1_pre tr1 )) (PreH25 : (store_type M t2_pre tr2 )) (PreH26 : (repr_rel_node s tr1 tr1 )) (PreH27 : (repr_rel_node s tr2 tr2 )) (PreH28 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH29 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((( &( "app_rand2" ) )) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  ((( &( "app_rand1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post t2_pre tr2 )) (PreH6 : (store_type M_post t1_pre tr1 )) (PreH7 : (store_type M_post (node_a (n)) a )) (PreH8 : (store_type M_post (node_b (n)) b )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel a a s s_post )) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n)) b )) (PreH16 : (store_type M (node_a (n)) a )) (PreH17 : (tr1 = (TApply (a) (b)))) (PreH18 : ((node_tag (n)) = 2)) (PreH19 : ((node_tag (n)) <> 1)) (PreH20 : ((node_tag (n)) <> 3)) (PreH21 : ((node_tag (n)) <> 3)) (PreH22 : ((node_tag (n)) <= 3)) (PreH23 : (0 <= (node_tag (n)))) (PreH24 : (node_at M t1_pre n )) (PreH25 : (rc_valid M )) (PreH26 : (store_type M t1_pre tr1 )) (PreH27 : (store_type M t2_pre tr2 )) (PreH28 : (repr_rel_node s tr1 tr1 )) (PreH29 : (repr_rel_node s tr2 tr2 )) (PreH30 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH31 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((( &( "app_rand2" ) )) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  ((( &( "app_rand1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
).

Definition atype_unify2_partial_solve_wit_42_same_node_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (store_type M_post t2_pre tr2 )) (PreH6 : (store_type M_post t1_pre tr1 )) (PreH7 : (store_type M_post (node_a (n)) a )) (PreH8 : (store_type M_post (node_b (n)) b )) (PreH9 : (retval = 0)) (PreH10 : (unify_rel a a s s_post )) (PreH11 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH12 : (rc_valid M_post )) (PreH13 : (rc_preserves M M_post )) (PreH14 : (rc_reservations_same M M_post )) (PreH15 : (store_type M (node_b (n)) b )) (PreH16 : (store_type M (node_a (n)) a )) (PreH17 : (tr1 = (TApply (a) (b)))) (PreH18 : ((node_tag (n)) = 2)) (PreH19 : ((node_tag (n)) <> 1)) (PreH20 : ((node_tag (n)) <> 3)) (PreH21 : ((node_tag (n)) <> 3)) (PreH22 : ((node_tag (n)) <= 3)) (PreH23 : (0 <= (node_tag (n)))) (PreH24 : (node_at M t1_pre n )) (PreH25 : (rc_valid M )) (PreH26 : (store_type M t1_pre tr1 )) (PreH27 : (store_type M t2_pre tr2 )) (PreH28 : (repr_rel_node s tr1 tr1 )) (PreH29 : (repr_rel_node s tr2 tr2 )) (PreH30 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH31 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((( &( "app_rand2" ) )) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  ((( &( "app_rand1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
.

Definition atype_unify2_partial_solve_wit_42_same_node_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (a: TypeTree) (b: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (store_type M_post t2_pre tr2 )) (PreH4 : (store_type M_post t1_pre tr1 )) (PreH5 : (store_type M_post (node_a (n)) a )) (PreH6 : (store_type M_post (node_b (n)) b )) (PreH7 : (retval = 0)) (PreH8 : (unify_rel a a s s_post )) (PreH9 : (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post )) (PreH10 : (rc_valid M_post )) (PreH11 : (rc_preserves M M_post )) (PreH12 : (rc_reservations_same M M_post )) (PreH13 : (store_type M (node_b (n)) b )) (PreH14 : (store_type M (node_a (n)) a )) (PreH15 : (tr1 = (TApply (a) (b)))) (PreH16 : ((node_tag (n)) = 2)) (PreH17 : ((node_tag (n)) <> 1)) (PreH18 : ((node_tag (n)) <> 3)) (PreH19 : ((node_tag (n)) <> 3)) (PreH20 : ((node_tag (n)) <= 3)) (PreH21 : (0 <= (node_tag (n)))) (PreH22 : (node_at M t1_pre n )) (PreH23 : (rc_valid M )) (PreH24 : (store_type M t1_pre tr1 )) (PreH25 : (store_type M t2_pre tr2 )) (PreH26 : (repr_rel_node s tr1 tr1 )) (PreH27 : (repr_rel_node s tr2 tr2 )) (PreH28 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH29 : (t1_pre = t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_world_missing M_post (cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))) )
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n)) ) ”
  &&  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_42_same_node := atype_unify2_partial_solve_wit_42_same_node_pure -> atype_unify2_partial_solve_wit_42_same_node_aux.

Definition atype_unify2_partial_solve_wit_43_distinct_nodes_pure :=
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TApply (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TApply (a) (b)))) (PreH22 : ((node_tag (n)) = 2)) (PreH23 : ((node_tag (n)) <> 1)) (PreH24 : ((node_tag (n)) = (node_tag (n_2)))) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t2_pre n_2 )) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((( &( "app_rand2" ) )) # Ptr  |-> (node_b (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((( &( "app_rand1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (node_at M_post t2_pre n_2 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post (node_a (n)) a )) (PreH9 : (store_type M_post (node_b (n)) b )) (PreH10 : (store_type M_post (node_a (n_2)) a_2 )) (PreH11 : (store_type M_post (node_b (n_2)) b_2 )) (PreH12 : (retval = 0)) (PreH13 : (unify_rel a a_2 s s_post )) (PreH14 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH15 : (rc_valid M_post )) (PreH16 : (rc_preserves M M_post )) (PreH17 : (rc_reservations_same M M_post )) (PreH18 : (store_type M (node_b (n_2)) b_2 )) (PreH19 : (store_type M (node_a (n_2)) a_2 )) (PreH20 : (tr2 = (TApply (a_2) (b_2)))) (PreH21 : (store_type M (node_b (n)) b )) (PreH22 : (store_type M (node_a (n)) a )) (PreH23 : (tr1 = (TApply (a) (b)))) (PreH24 : ((node_tag (n)) = 2)) (PreH25 : ((node_tag (n)) <> 1)) (PreH26 : ((node_tag (n)) = (node_tag (n_2)))) (PreH27 : ((node_tag (n_2)) <> 3)) (PreH28 : ((node_tag (n_2)) <= 3)) (PreH29 : (0 <= (node_tag (n_2)))) (PreH30 : (node_at M t2_pre n_2 )) (PreH31 : ((node_tag (n)) <> 3)) (PreH32 : ((node_tag (n)) <= 3)) (PreH33 : (0 <= (node_tag (n)))) (PreH34 : (node_at M t1_pre n )) (PreH35 : (rc_valid M )) (PreH36 : (store_type M t1_pre tr1 )) (PreH37 : (store_type M t2_pre tr2 )) (PreH38 : (repr_rel_node s tr1 tr1 )) (PreH39 : (repr_rel_node s tr2 tr2 )) (PreH40 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH41 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((( &( "app_rand2" ) )) # Ptr  |-> (node_b (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((( &( "app_rand1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
).

Definition atype_unify2_partial_solve_wit_43_distinct_nodes_pure_split_goal_1 :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (node_at M_post t1_pre n )) (PreH5 : (node_at M_post t2_pre n_2 )) (PreH6 : (store_type M_post t2_pre tr2 )) (PreH7 : (store_type M_post t1_pre tr1 )) (PreH8 : (store_type M_post (node_a (n)) a )) (PreH9 : (store_type M_post (node_b (n)) b )) (PreH10 : (store_type M_post (node_a (n_2)) a_2 )) (PreH11 : (store_type M_post (node_b (n_2)) b_2 )) (PreH12 : (retval = 0)) (PreH13 : (unify_rel a a_2 s s_post )) (PreH14 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH15 : (rc_valid M_post )) (PreH16 : (rc_preserves M M_post )) (PreH17 : (rc_reservations_same M M_post )) (PreH18 : (store_type M (node_b (n_2)) b_2 )) (PreH19 : (store_type M (node_a (n_2)) a_2 )) (PreH20 : (tr2 = (TApply (a_2) (b_2)))) (PreH21 : (store_type M (node_b (n)) b )) (PreH22 : (store_type M (node_a (n)) a )) (PreH23 : (tr1 = (TApply (a) (b)))) (PreH24 : ((node_tag (n)) = 2)) (PreH25 : ((node_tag (n)) <> 1)) (PreH26 : ((node_tag (n)) = (node_tag (n_2)))) (PreH27 : ((node_tag (n_2)) <> 3)) (PreH28 : ((node_tag (n_2)) <= 3)) (PreH29 : (0 <= (node_tag (n_2)))) (PreH30 : (node_at M t2_pre n_2 )) (PreH31 : ((node_tag (n)) <> 3)) (PreH32 : ((node_tag (n)) <= 3)) (PreH33 : (0 <= (node_tag (n)))) (PreH34 : (node_at M t1_pre n )) (PreH35 : (rc_valid M )) (PreH36 : (store_type M t1_pre tr1 )) (PreH37 : (store_type M t2_pre tr2 )) (PreH38 : (repr_rel_node s tr1 tr1 )) (PreH39 : (repr_rel_node s tr2 tr2 )) (PreH40 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH41 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((( &( "app_rand2" ) )) # Ptr  |-> (node_b (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  ((( &( "app_rand1" ) )) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "app_tfn2" ) )) # Ptr  |-> (node_a (n_2)))
  **  ((( &( "app_tfn1" ) )) # Ptr  |-> (node_a (n)))
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
.

Definition atype_unify2_partial_solve_wit_43_distinct_nodes_aux :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (a: TypeTree) (b: TypeTree) (a_2: TypeTree) (b_2: TypeTree) (M_post: RcState) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (node_at M_post t1_pre n )) (PreH3 : (node_at M_post t2_pre n_2 )) (PreH4 : (store_type M_post t2_pre tr2 )) (PreH5 : (store_type M_post t1_pre tr1 )) (PreH6 : (store_type M_post (node_a (n)) a )) (PreH7 : (store_type M_post (node_b (n)) b )) (PreH8 : (store_type M_post (node_a (n_2)) a_2 )) (PreH9 : (store_type M_post (node_b (n_2)) b_2 )) (PreH10 : (retval = 0)) (PreH11 : (unify_rel a a_2 s s_post )) (PreH12 : (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post )) (PreH13 : (rc_valid M_post )) (PreH14 : (rc_preserves M M_post )) (PreH15 : (rc_reservations_same M M_post )) (PreH16 : (store_type M (node_b (n_2)) b_2 )) (PreH17 : (store_type M (node_a (n_2)) a_2 )) (PreH18 : (tr2 = (TApply (a_2) (b_2)))) (PreH19 : (store_type M (node_b (n)) b )) (PreH20 : (store_type M (node_a (n)) a )) (PreH21 : (tr1 = (TApply (a) (b)))) (PreH22 : ((node_tag (n)) = 2)) (PreH23 : ((node_tag (n)) <> 1)) (PreH24 : ((node_tag (n)) = (node_tag (n_2)))) (PreH25 : ((node_tag (n_2)) <> 3)) (PreH26 : ((node_tag (n_2)) <= 3)) (PreH27 : (0 <= (node_tag (n_2)))) (PreH28 : (node_at M t2_pre n_2 )) (PreH29 : ((node_tag (n)) <> 3)) (PreH30 : ((node_tag (n)) <= 3)) (PreH31 : (0 <= (node_tag (n)))) (PreH32 : (node_at M t1_pre n )) (PreH33 : (rc_valid M )) (PreH34 : (store_type M t1_pre tr1 )) (PreH35 : (store_type M t2_pre tr2 )) (PreH36 : (repr_rel_node s tr1 tr1 )) (PreH37 : (repr_rel_node s tr2 tr2 )) (PreH38 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH39 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n_2)))
  **  (store_world_missing M_post (cons ((field_key (t2_pre) (Payload1))) ((cons ((field_key (t1_pre) (Payload1))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> (node_b (n)))
  **  (store_solution M_post ( &( "res" ) ) s_post )
|--
  “ (rc_valid M_post ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (rc_capacity 0 M_post s_post (node_b (n)) (node_b (n_2)) ) ”
  &&  “ (retval = 0) ”
  &&  “ (node_at M_post t1_pre n ) ”
  &&  “ (node_at M_post t2_pre n_2 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post (node_a (n)) a ) ”
  &&  “ (store_type M_post (node_b (n)) b ) ”
  &&  “ (store_type M_post (node_a (n_2)) a_2 ) ”
  &&  “ (store_type M_post (node_b (n_2)) b_2 ) ”
  &&  “ (retval = 0) ”
  &&  “ (unify_rel a a_2 s s_post ) ”
  &&  “ (infer_result 0 M s (node_a (n)) (node_a (n_2)) retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  “ (store_type M (node_b (n_2)) b_2 ) ”
  &&  “ (store_type M (node_a (n_2)) a_2 ) ”
  &&  “ (tr2 = (TApply (a_2) (b_2))) ”
  &&  “ (store_type M (node_b (n)) b ) ”
  &&  “ (store_type M (node_a (n)) a ) ”
  &&  “ (tr1 = (TApply (a) (b))) ”
  &&  “ ((node_tag (n)) = 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post )
.

Definition atype_unify2_partial_solve_wit_43_distinct_nodes := atype_unify2_partial_solve_wit_43_distinct_nodes_pure -> atype_unify2_partial_solve_wit_43_distinct_nodes_aux.

Definition atype_unify2_partial_solve_wit_44_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) <> 2)) (PreH2 : ((node_tag (n)) <> 1)) (PreH3 : ((node_tag (n)) <> 3)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <= 3)) (PreH6 : (0 <= (node_tag (n)))) (PreH7 : (node_at M t1_pre n )) (PreH8 : (rc_valid M )) (PreH9 : (store_type M t1_pre tr1 )) (PreH10 : (store_type M t2_pre tr2 )) (PreH11 : (repr_rel_node s tr1 tr1 )) (PreH12 : (repr_rel_node s tr2 tr2 )) (PreH13 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH14 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))) )
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) = 0) ”
  &&  “ ((node_tag (n)) <> 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_45_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) <> 2)) (PreH2 : ((node_tag (n)) <> 1)) (PreH3 : ((node_tag (n)) = (node_tag (n_2)))) (PreH4 : ((node_tag (n_2)) <> 3)) (PreH5 : ((node_tag (n_2)) <= 3)) (PreH6 : (0 <= (node_tag (n_2)))) (PreH7 : (node_at M t2_pre n_2 )) (PreH8 : ((node_tag (n)) <> 3)) (PreH9 : ((node_tag (n)) <= 3)) (PreH10 : (0 <= (node_tag (n)))) (PreH11 : (node_at M t1_pre n )) (PreH12 : (rc_valid M )) (PreH13 : (store_type M t1_pre tr1 )) (PreH14 : (store_type M t2_pre tr2 )) (PreH15 : (repr_rel_node s tr1 tr1 )) (PreH16 : (repr_rel_node s tr2 tr2 )) (PreH17 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH18 : (t1_pre <> t2_pre)),
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) = 0) ”
  &&  “ ((node_tag (n)) <> 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))) )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_46_same_node :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) <> 3)) (PreH5 : ((node_tag (n)) <> 3)) (PreH6 : ((node_tag (n)) <= 3)) (PreH7 : (0 <= (node_tag (n)))) (PreH8 : (node_at M t1_pre n )) (PreH9 : (rc_valid M )) (PreH10 : (store_type M t1_pre tr1 )) (PreH11 : (store_type M t2_pre tr2 )) (PreH12 : (repr_rel_node s tr1 tr1 )) (PreH13 : (repr_rel_node s tr2 tr2 )) (PreH14 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH15 : (t1_pre = t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) = 0) ”
  &&  “ ((node_tag (n)) <> 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre = t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

Definition atype_unify2_partial_solve_wit_47_distinct_nodes :=
forall (tr2: TypeTree) (tr1: TypeTree) (s: sol) (M: RcState) (t1_pre: Z) (t2_pre: Z) (n: TypeNode) (n_2: TypeNode) (PreH1 : ((node_tag (n)) = 0)) (PreH2 : ((node_tag (n)) <> 2)) (PreH3 : ((node_tag (n)) <> 1)) (PreH4 : ((node_tag (n)) = (node_tag (n_2)))) (PreH5 : ((node_tag (n_2)) <> 3)) (PreH6 : ((node_tag (n_2)) <= 3)) (PreH7 : (0 <= (node_tag (n_2)))) (PreH8 : (node_at M t2_pre n_2 )) (PreH9 : ((node_tag (n)) <> 3)) (PreH10 : ((node_tag (n)) <= 3)) (PreH11 : (0 <= (node_tag (n)))) (PreH12 : (node_at M t1_pre n )) (PreH13 : (rc_valid M )) (PreH14 : (store_type M t1_pre tr1 )) (PreH15 : (store_type M t2_pre tr2 )) (PreH16 : (repr_rel_node s tr1 tr1 )) (PreH17 : (repr_rel_node s tr2 tr2 )) (PreH18 : (rc_capacity 2 M s t1_pre t2_pre )) (PreH19 : (t1_pre <> t2_pre)),
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  (store_world_missing M (cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))) )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
|--
  “ ((node_tag (n)) = 0) ”
  &&  “ ((node_tag (n)) <> 2) ”
  &&  “ ((node_tag (n)) <> 1) ”
  &&  “ ((node_tag (n)) = (node_tag (n_2))) ”
  &&  “ ((node_tag (n_2)) <> 3) ”
  &&  “ ((node_tag (n_2)) <= 3) ”
  &&  “ (0 <= (node_tag (n_2))) ”
  &&  “ (node_at M t2_pre n_2 ) ”
  &&  “ ((node_tag (n)) <> 3) ”
  &&  “ ((node_tag (n)) <= 3) ”
  &&  “ (0 <= (node_tag (n))) ”
  &&  “ (node_at M t1_pre n ) ”
  &&  “ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (repr_rel_node s tr1 tr1 ) ”
  &&  “ (repr_rel_node s tr2 tr2 ) ”
  &&  “ (rc_capacity 2 M s t1_pre t2_pre ) ”
  &&  “ (t1_pre <> t2_pre) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n_2)))
  **  (store_world_missing M (cons ((field_key (t2_pre) (Payload0))) ((cons ((field_key (t1_pre) (Payload0))) ((cons ((field_key (t2_pre) (Tag))) ((cons ((field_key (t1_pre) (Tag))) ((@nil TypeFieldKey))))))))) )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> (node_a (n)))
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n_2)))
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> (node_tag (n)))
  **  (store_solution M ( &( "res" ) ) s )
.

(* Shallow FunAssertion specs for atype_unify. *)
Definition atype_unify_sig : FuncSig := ([ * struct "atype";  * struct "atype"], i32)%ctype.

Definition atype_unify_verify : Spec atype_unify_sig :=
  fun F =>
ALL (M: RcState),
ALL (s: sol),
ALL (tr1: TypeTree),
ALL (tr2: TypeTree),
HoareFun ([ * struct "atype";  * struct "atype"], i32)%ctype
  (fun '(t1_pre, t2_pre) =>
  (“ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (rc_capacity 0 M s t1_pre t2_pre ) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) s )))
  (fun '(t1_pre, t2_pre) retval =>
(orp
  (EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1 tr2 s s_post ) ”
  &&  “ (infer_result 0 M s t1_pre t2_pre retval M_post s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (rc_reservations_same M M_post ) ”
  &&  (store_world M_post )
  **  (store_solution M_post ( &( "res" ) ) s_post ))
  (EX (M_post_2: RcState) (s_post_2: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 0 M s t1_pre t2_pre retval M_post_2 s_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (rc_reservations_same M M_post_2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 ))))
  F.

Definition atype_unify_final : Spec atype_unify_sig :=
  fun F =>
ALL (M: RcState),
ALL (s_pre: sol),
ALL (raw: sol),
ALL (tr1: TypeTree),
ALL (tr2: TypeTree),
HoareFun ([ * struct "atype";  * struct "atype"], i32)%ctype
  (fun '(t1_pre, t2_pre) =>
  (“ (rc_valid M ) ”
  &&  “ (store_type M t1_pre tr1 ) ”
  &&  “ (store_type M t2_pre tr2 ) ”
  &&  “ (sol_compress_to raw s_pre ) ”
  &&  “ (sol_finite s_pre ) ”
  &&  “ (sol_no_loop raw ) ”
  &&  “ (rc_capacity 0 M raw t1_pre t2_pre ) ”
  &&  (store_world M )
  **  (store_solution M ( &( "res" ) ) raw )))
  (fun '(t1_pre, t2_pre) retval =>
(orp
  (EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (sol_correct_iter tr1 tr2 s_pre s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  “ (store_type M_post t1_pre tr1 ) ”
  &&  “ (store_type M_post t2_pre tr2 ) ”
  &&  (store_world M_post )
  **  (store_compressed_solution M_post ( &( "res" ) ) s_post ))
  (EX (s_post_2: sol) (M_post_2: RcState),
  “ (retval <> 0) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M M_post_2 ) ”
  &&  “ (store_type M_post_2 t1_pre tr1 ) ”
  &&  “ (store_type M_post_2 t2_pre tr2 ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 ))))
  F.

Definition atype_unify_verify_entail_final :=
forall (t1_pre: Z) (t2_pre: Z) (M_final: RcState) (s_pre_final: sol) (raw_final: sol) (tr1_final: TypeTree) (tr2_final: TypeTree),
  (“ (rc_valid M_final ) ”
  &&  “ (store_type M_final t1_pre tr1_final ) ”
  &&  “ (store_type M_final t2_pre tr2_final ) ”
  &&  “ (sol_compress_to raw_final s_pre_final ) ”
  &&  “ (sol_finite s_pre_final ) ”
  &&  “ (sol_no_loop raw_final ) ”
  &&  “ (rc_capacity 0 M_final raw_final t1_pre t2_pre ) ”
  &&  (store_world M_final )
  **  (store_solution M_final ( &( "res" ) ) raw_final ))
|--
EX (M_verify: RcState)(s_verify: sol)(tr1_verify: TypeTree)(tr2_verify: TypeTree),
  (“ (rc_valid M_verify ) ”
  &&  “ (store_type M_verify t1_pre tr1_verify ) ”
  &&  “ (store_type M_verify t2_pre tr2_verify ) ”
  &&  “ (rc_capacity 0 M_verify s_verify t1_pre t2_pre ) ”
  &&  (store_world M_verify )
  **  (store_solution M_verify ( &( "res" ) ) s_verify ))
  **
  (ALL (retval: Z),
(orp
  (EX (M_post_3: RcState) (s_post_3: sol),
  “ (retval = 0) ”
  &&  “ (unify_rel tr1_verify tr2_verify s_verify s_post_3 ) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_3 s_post_3 ) ”
  &&  “ (rc_valid M_post_3 ) ”
  &&  “ (rc_preserves M_verify M_post_3 ) ”
  &&  “ (rc_reservations_same M_verify M_post_3 ) ”
  &&  (store_world M_post_3 )
  **  (store_solution M_post_3 ( &( "res" ) ) s_post_3 ))
  (EX (M_post_4: RcState) (s_post_4: sol),
  “ (retval <> 0) ”
  &&  “ (infer_result 0 M_verify s_verify t1_pre t2_pre retval M_post_4 s_post_4 ) ”
  &&  “ (rc_valid M_post_4 ) ”
  &&  “ (rc_preserves M_verify M_post_4 ) ”
  &&  “ (rc_reservations_same M_verify M_post_4 ) ”
  &&  (store_world M_post_4 )
  **  (store_solution M_post_4 ( &( "res" ) ) s_post_4 )))
  -*
(orp
  (EX (M_post: RcState) (s_post: sol),
  “ (retval = 0) ”
  &&  “ (sol_correct_iter tr1_final tr2_final s_pre_final s_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_final M_post ) ”
  &&  “ (store_type M_post t1_pre tr1_final ) ”
  &&  “ (store_type M_post t2_pre tr2_final ) ”
  &&  (store_world M_post )
  **  (store_compressed_solution M_post ( &( "res" ) ) s_post ))
  (EX (s_post_2: sol) (M_post_2: RcState),
  “ (retval <> 0) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_final M_post_2 ) ”
  &&  “ (store_type M_post_2 t1_pre tr1_final ) ”
  &&  “ (store_type M_post_2 t2_pre tr2_final ) ”
  &&  (store_world M_post_2 )
  **  (store_solution M_post_2 ( &( "res" ) ) s_post_2 ))))
.

(* Shallow FunAssertion specs for copy_atype. *)
Definition copy_atype_sig : FuncSig := ([ * struct "atype"],  * struct "atype")%ctype.

Definition copy_atype_open_var : Spec copy_atype_sig :=
  fun F =>
ALL (M: RcState),
ALL (p: Z),
ALL (v: Z),
HoareFun ([ * struct "atype"],  * struct "atype")%ctype
  (fun t_pre =>
  (“ (rc_valid M ) ”
  &&  “ (0 < (rc_count (M) (t_pre))) ”
  &&  “ ((rc_count (M) (t_pre)) < INT_MAX) ”
  &&  “ (node_at M p (Node (3) (v) (0)) ) ”
  &&  ((&((p)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> v)
  **  (store_world_missing M (payload_keys (p) ((Node (3) (v) (0)))) )))
  (fun t_pre retval =>
  (EX (M_post: RcState),
  “ (retval = t_pre) ”
  &&  “ (retain_rel M t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  ((&((p)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> v)
  **  (store_world_missing M_post (payload_keys (p) ((Node (3) (v) (0)))) )))
  F.

Definition copy_atype_nonnull : Spec copy_atype_sig :=
  fun F =>
ALL (M: RcState),
HoareFun ([ * struct "atype"],  * struct "atype")%ctype
  (fun t_pre =>
  (“ (t_pre <> 0) ”
  &&  “ (rc_valid M ) ”
  &&  “ (0 < (rc_count (M) (t_pre))) ”
  &&  “ ((rc_count (M) (t_pre)) < INT_MAX) ”
  &&  (store_world M )))
  (fun t_pre retval =>
  (EX (M_post: RcState),
  “ (retval = t_pre) ”
  &&  “ (retain_rel M t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  (store_world M_post )))
  F.

Definition copy_atype_null : Spec copy_atype_sig :=
  fun F =>
ALL (M: RcState),
HoareFun ([ * struct "atype"],  * struct "atype")%ctype
  (fun t_pre =>
  (“ (t_pre = 0) ”
  &&  “ (rc_valid M ) ”
  &&  (store_world M )))
  (fun t_pre retval =>
  (EX (M_post: RcState),
  “ (retval = t_pre) ”
  &&  “ (retain_rel M t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M M_post ) ”
  &&  (store_world M_post )))
  F.

Definition copy_atype_nonnull_entail_open_var :=
forall (t_pre: Z) (M_open_var: RcState) (p_open_var: Z) (v_open_var: Z),
  (“ (rc_valid M_open_var ) ”
  &&  “ (0 < (rc_count (M_open_var) (t_pre))) ”
  &&  “ ((rc_count (M_open_var) (t_pre)) < INT_MAX) ”
  &&  “ (node_at M_open_var p_open_var (Node (3) (v_open_var) (0)) ) ”
  &&  ((&((p_open_var)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> v_open_var)
  **  (store_world_missing M_open_var (payload_keys (p_open_var) ((Node (3) (v_open_var) (0)))) ))
|--
EX (M_nonnull: RcState),
  (“ (t_pre <> 0) ”
  &&  “ (rc_valid M_nonnull ) ”
  &&  “ (0 < (rc_count (M_nonnull) (t_pre))) ”
  &&  “ ((rc_count (M_nonnull) (t_pre)) < INT_MAX) ”
  &&  (store_world M_nonnull ))
  **
  (ALL (retval: Z),
  (EX (M_post_2: RcState),
  “ (retval = t_pre) ”
  &&  “ (retain_rel M_nonnull t_pre M_post_2 ) ”
  &&  “ (rc_valid M_post_2 ) ”
  &&  “ (rc_preserves M_nonnull M_post_2 ) ”
  &&  (store_world M_post_2 ))
  -*
  (EX (M_post: RcState),
  “ (retval = t_pre) ”
  &&  “ (retain_rel M_open_var t_pre M_post ) ”
  &&  “ (rc_valid M_post ) ”
  &&  “ (rc_preserves M_open_var M_post ) ”
  &&  ((&((p_open_var)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> v_open_var)
  **  (store_world_missing M_post (payload_keys (p_open_var) ((Node (3) (v_open_var) (0)))) )))
.

Module Type VC_Correct.

Include typeinfer_rc_Strategy_Correct.

Axiom proof_of_copy_atype_safety_wit_1_nonnull : copy_atype_safety_wit_1_nonnull.
Axiom proof_of_copy_atype_safety_wit_2_null : copy_atype_safety_wit_2_null.
Axiom proof_of_copy_atype_safety_wit_3_nonnull : copy_atype_safety_wit_3_nonnull.
Axiom proof_of_copy_atype_safety_wit_4_null : copy_atype_safety_wit_4_null.
Axiom proof_of_copy_atype_safety_wit_5_nonnull : copy_atype_safety_wit_5_nonnull.
Axiom proof_of_copy_atype_safety_wit_6_nonnull : copy_atype_safety_wit_6_nonnull.
Axiom proof_of_copy_atype_return_wit_1_nonnull : copy_atype_return_wit_1_nonnull.
Axiom proof_of_copy_atype_return_wit_2_null : copy_atype_return_wit_2_null.
Axiom proof_of_copy_atype_partial_solve_wit_1_nonnull : copy_atype_partial_solve_wit_1_nonnull.
Axiom proof_of_free_atype_safety_wit_1_nonnull : free_atype_safety_wit_1_nonnull.
Axiom proof_of_free_atype_safety_wit_2_null : free_atype_safety_wit_2_null.
Axiom proof_of_free_atype_safety_wit_3_nonnull : free_atype_safety_wit_3_nonnull.
Axiom proof_of_free_atype_safety_wit_4_null : free_atype_safety_wit_4_null.
Axiom proof_of_free_atype_safety_wit_5_nonnull : free_atype_safety_wit_5_nonnull.
Axiom proof_of_free_atype_safety_wit_6_nonnull : free_atype_safety_wit_6_nonnull.
Axiom proof_of_free_atype_safety_wit_7_nonnull : free_atype_safety_wit_7_nonnull.
Axiom proof_of_free_atype_safety_wit_8_nonnull : free_atype_safety_wit_8_nonnull.
Axiom proof_of_free_atype_safety_wit_9_nonnull : free_atype_safety_wit_9_nonnull.
Axiom proof_of_free_atype_entail_wit_1_1_nonnull : free_atype_entail_wit_1_1_nonnull.
Axiom proof_of_free_atype_entail_wit_1_2_nonnull : free_atype_entail_wit_1_2_nonnull.
Axiom proof_of_free_atype_entail_wit_1_3_nonnull : free_atype_entail_wit_1_3_nonnull.
Axiom proof_of_free_atype_return_wit_1_null : free_atype_return_wit_1_null.
Axiom proof_of_free_atype_return_wit_2_nonnull : free_atype_return_wit_2_nonnull.
Axiom proof_of_free_atype_return_wit_3_nonnull : free_atype_return_wit_3_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_1_nonnull : free_atype_partial_solve_wit_1_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_2_nonnull : free_atype_partial_solve_wit_2_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_3_nonnull_pure : free_atype_partial_solve_wit_3_nonnull_pure.
Axiom proof_of_free_atype_partial_solve_wit_3_nonnull : free_atype_partial_solve_wit_3_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_4_nonnull_pure : free_atype_partial_solve_wit_4_nonnull_pure.
Axiom proof_of_free_atype_partial_solve_wit_4_nonnull : free_atype_partial_solve_wit_4_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_5_nonnull_pure : free_atype_partial_solve_wit_5_nonnull_pure.
Axiom proof_of_free_atype_partial_solve_wit_5_nonnull : free_atype_partial_solve_wit_5_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_6_nonnull_pure : free_atype_partial_solve_wit_6_nonnull_pure.
Axiom proof_of_free_atype_partial_solve_wit_6_nonnull : free_atype_partial_solve_wit_6_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_7_nonnull_pure : free_atype_partial_solve_wit_7_nonnull_pure.
Axiom proof_of_free_atype_partial_solve_wit_7_nonnull : free_atype_partial_solve_wit_7_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_8_nonnull_pure : free_atype_partial_solve_wit_8_nonnull_pure.
Axiom proof_of_free_atype_partial_solve_wit_8_nonnull : free_atype_partial_solve_wit_8_nonnull.
Axiom proof_of_free_atype_partial_solve_wit_9_nonnull : free_atype_partial_solve_wit_9_nonnull.
Axiom proof_of_free_atype_which_implies_wit_1 : free_atype_which_implies_wit_1.
Axiom proof_of_free_atype_which_implies_wit_2 : free_atype_which_implies_wit_2.
Axiom proof_of_atype_unify_safety_wit_1 : atype_unify_safety_wit_1.
Axiom proof_of_atype_unify_safety_wit_2 : atype_unify_safety_wit_2.
Axiom proof_of_atype_unify_safety_wit_3 : atype_unify_safety_wit_3.
Axiom proof_of_atype_unify_entail_wit_1_1 : atype_unify_entail_wit_1_1.
Axiom proof_of_atype_unify_entail_wit_1_2 : atype_unify_entail_wit_1_2.
Axiom proof_of_atype_unify_entail_wit_2_1 : atype_unify_entail_wit_2_1.
Axiom proof_of_atype_unify_entail_wit_2_2 : atype_unify_entail_wit_2_2.
Axiom proof_of_atype_unify_return_wit_1 : atype_unify_return_wit_1.
Axiom proof_of_atype_unify_return_wit_2 : atype_unify_return_wit_2.
Axiom proof_of_atype_unify_return_wit_3 : atype_unify_return_wit_3.
Axiom proof_of_atype_unify_return_wit_4 : atype_unify_return_wit_4.
Axiom proof_of_atype_unify_return_wit_5 : atype_unify_return_wit_5.
Axiom proof_of_atype_unify_return_wit_6 : atype_unify_return_wit_6.
Axiom proof_of_atype_unify_partial_solve_wit_1 : atype_unify_partial_solve_wit_1.
Axiom proof_of_atype_unify_partial_solve_wit_2 : atype_unify_partial_solve_wit_2.
Axiom proof_of_atype_unify_partial_solve_wit_3_pure : atype_unify_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify_partial_solve_wit_3 : atype_unify_partial_solve_wit_3.
Axiom proof_of_atype_unify_partial_solve_wit_4_pure : atype_unify_partial_solve_wit_4_pure.
Axiom proof_of_atype_unify_partial_solve_wit_4 : atype_unify_partial_solve_wit_4.
Axiom proof_of_atype_unify_partial_solve_wit_5_pure : atype_unify_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify_partial_solve_wit_5 : atype_unify_partial_solve_wit_5.
Axiom proof_of_atype_unify_partial_solve_wit_6_pure : atype_unify_partial_solve_wit_6_pure.
Axiom proof_of_atype_unify_partial_solve_wit_6 : atype_unify_partial_solve_wit_6.
Axiom proof_of_atype_unify_partial_solve_wit_7_pure : atype_unify_partial_solve_wit_7_pure.
Axiom proof_of_atype_unify_partial_solve_wit_7 : atype_unify_partial_solve_wit_7.
Axiom proof_of_atype_unify_partial_solve_wit_8_pure : atype_unify_partial_solve_wit_8_pure.
Axiom proof_of_atype_unify_partial_solve_wit_8 : atype_unify_partial_solve_wit_8.
Axiom proof_of_atype_unify_partial_solve_wit_9_pure : atype_unify_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify_partial_solve_wit_9 : atype_unify_partial_solve_wit_9.
Axiom proof_of_atype_unify1_safety_wit_1 : atype_unify1_safety_wit_1.
Axiom proof_of_atype_unify1_safety_wit_2 : atype_unify1_safety_wit_2.
Axiom proof_of_atype_unify1_safety_wit_3 : atype_unify1_safety_wit_3.
Axiom proof_of_atype_unify1_entail_wit_1_1 : atype_unify1_entail_wit_1_1.
Axiom proof_of_atype_unify1_entail_wit_1_2 : atype_unify1_entail_wit_1_2.
Axiom proof_of_atype_unify1_entail_wit_2_1 : atype_unify1_entail_wit_2_1.
Axiom proof_of_atype_unify1_entail_wit_2_2 : atype_unify1_entail_wit_2_2.
Axiom proof_of_atype_unify1_return_wit_1 : atype_unify1_return_wit_1.
Axiom proof_of_atype_unify1_return_wit_2 : atype_unify1_return_wit_2.
Axiom proof_of_atype_unify1_return_wit_3 : atype_unify1_return_wit_3.
Axiom proof_of_atype_unify1_return_wit_4 : atype_unify1_return_wit_4.
Axiom proof_of_atype_unify1_return_wit_5 : atype_unify1_return_wit_5.
Axiom proof_of_atype_unify1_return_wit_6 : atype_unify1_return_wit_6.
Axiom proof_of_atype_unify1_partial_solve_wit_1 : atype_unify1_partial_solve_wit_1.
Axiom proof_of_atype_unify1_partial_solve_wit_2 : atype_unify1_partial_solve_wit_2.
Axiom proof_of_atype_unify1_partial_solve_wit_3_pure : atype_unify1_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_3 : atype_unify1_partial_solve_wit_3.
Axiom proof_of_atype_unify1_partial_solve_wit_4_pure : atype_unify1_partial_solve_wit_4_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_4 : atype_unify1_partial_solve_wit_4.
Axiom proof_of_atype_unify1_partial_solve_wit_5_pure : atype_unify1_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_5 : atype_unify1_partial_solve_wit_5.
Axiom proof_of_atype_unify1_partial_solve_wit_6_pure : atype_unify1_partial_solve_wit_6_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_6 : atype_unify1_partial_solve_wit_6.
Axiom proof_of_atype_unify1_partial_solve_wit_7_pure : atype_unify1_partial_solve_wit_7_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_7 : atype_unify1_partial_solve_wit_7.
Axiom proof_of_atype_unify1_partial_solve_wit_8_pure : atype_unify1_partial_solve_wit_8_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_8 : atype_unify1_partial_solve_wit_8.
Axiom proof_of_atype_unify1_partial_solve_wit_9_pure : atype_unify1_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_9 : atype_unify1_partial_solve_wit_9.
Axiom proof_of_atype_unify2_safety_wit_1 : atype_unify2_safety_wit_1.
Axiom proof_of_atype_unify2_safety_wit_2_same_node : atype_unify2_safety_wit_2_same_node.
Axiom proof_of_atype_unify2_safety_wit_3_distinct_nodes : atype_unify2_safety_wit_3_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_4_same_node : atype_unify2_safety_wit_4_same_node.
Axiom proof_of_atype_unify2_safety_wit_5_distinct_nodes : atype_unify2_safety_wit_5_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_6_same_node : atype_unify2_safety_wit_6_same_node.
Axiom proof_of_atype_unify2_safety_wit_7_distinct_nodes : atype_unify2_safety_wit_7_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_8_same_node : atype_unify2_safety_wit_8_same_node.
Axiom proof_of_atype_unify2_safety_wit_9_distinct_nodes : atype_unify2_safety_wit_9_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_10_same_node : atype_unify2_safety_wit_10_same_node.
Axiom proof_of_atype_unify2_safety_wit_11_distinct_nodes : atype_unify2_safety_wit_11_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_12_same_node : atype_unify2_safety_wit_12_same_node.
Axiom proof_of_atype_unify2_safety_wit_13_distinct_nodes : atype_unify2_safety_wit_13_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_14_same_node : atype_unify2_safety_wit_14_same_node.
Axiom proof_of_atype_unify2_safety_wit_15_distinct_nodes : atype_unify2_safety_wit_15_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_16_distinct_nodes : atype_unify2_safety_wit_16_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_17_distinct_nodes : atype_unify2_safety_wit_17_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_18_distinct_nodes : atype_unify2_safety_wit_18_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_19_distinct_nodes : atype_unify2_safety_wit_19_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_20_distinct_nodes : atype_unify2_safety_wit_20_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_21_same_node : atype_unify2_safety_wit_21_same_node.
Axiom proof_of_atype_unify2_safety_wit_22_distinct_nodes : atype_unify2_safety_wit_22_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_23_distinct_nodes : atype_unify2_safety_wit_23_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_24_same_node : atype_unify2_safety_wit_24_same_node.
Axiom proof_of_atype_unify2_safety_wit_25_same_node : atype_unify2_safety_wit_25_same_node.
Axiom proof_of_atype_unify2_safety_wit_26_distinct_nodes : atype_unify2_safety_wit_26_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_27_distinct_nodes : atype_unify2_safety_wit_27_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_28_same_node : atype_unify2_safety_wit_28_same_node.
Axiom proof_of_atype_unify2_safety_wit_29_same_node : atype_unify2_safety_wit_29_same_node.
Axiom proof_of_atype_unify2_safety_wit_30_same_node : atype_unify2_safety_wit_30_same_node.
Axiom proof_of_atype_unify2_safety_wit_31_distinct_nodes : atype_unify2_safety_wit_31_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_32_same_node : atype_unify2_safety_wit_32_same_node.
Axiom proof_of_atype_unify2_safety_wit_33_same_node : atype_unify2_safety_wit_33_same_node.
Axiom proof_of_atype_unify2_safety_wit_34_distinct_nodes : atype_unify2_safety_wit_34_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_35_distinct_nodes : atype_unify2_safety_wit_35_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_36_same_node : atype_unify2_safety_wit_36_same_node.
Axiom proof_of_atype_unify2_safety_wit_37_same_node : atype_unify2_safety_wit_37_same_node.
Axiom proof_of_atype_unify2_safety_wit_38_distinct_nodes : atype_unify2_safety_wit_38_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_39_distinct_nodes : atype_unify2_safety_wit_39_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_40_same_node : atype_unify2_safety_wit_40_same_node.
Axiom proof_of_atype_unify2_safety_wit_41_distinct_nodes : atype_unify2_safety_wit_41_distinct_nodes.
Axiom proof_of_atype_unify2_safety_wit_42_distinct_nodes : atype_unify2_safety_wit_42_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_1_1_same_node : atype_unify2_entail_wit_1_1_same_node.
Axiom proof_of_atype_unify2_entail_wit_1_2_same_node : atype_unify2_entail_wit_1_2_same_node.
Axiom proof_of_atype_unify2_entail_wit_1_3_distinct_nodes : atype_unify2_entail_wit_1_3_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_1_4_distinct_nodes : atype_unify2_entail_wit_1_4_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_2_1_same_node : atype_unify2_entail_wit_2_1_same_node.
Axiom proof_of_atype_unify2_entail_wit_2_2_same_node : atype_unify2_entail_wit_2_2_same_node.
Axiom proof_of_atype_unify2_entail_wit_2_3_distinct_nodes : atype_unify2_entail_wit_2_3_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_2_4_distinct_nodes : atype_unify2_entail_wit_2_4_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_3_1_distinct_nodes : atype_unify2_entail_wit_3_1_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_3_2_distinct_nodes : atype_unify2_entail_wit_3_2_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_4_1_distinct_nodes : atype_unify2_entail_wit_4_1_distinct_nodes.
Axiom proof_of_atype_unify2_entail_wit_4_2_distinct_nodes : atype_unify2_entail_wit_4_2_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_1_distinct_nodes : atype_unify2_return_wit_1_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_2_same_node : atype_unify2_return_wit_2_same_node.
Axiom proof_of_atype_unify2_return_wit_3_distinct_nodes : atype_unify2_return_wit_3_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_4_same_node : atype_unify2_return_wit_4_same_node.
Axiom proof_of_atype_unify2_return_wit_5_same_node : atype_unify2_return_wit_5_same_node.
Axiom proof_of_atype_unify2_return_wit_6_distinct_nodes : atype_unify2_return_wit_6_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_7_distinct_nodes : atype_unify2_return_wit_7_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_8_same_node : atype_unify2_return_wit_8_same_node.
Axiom proof_of_atype_unify2_return_wit_9_distinct_nodes : atype_unify2_return_wit_9_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_10_distinct_nodes : atype_unify2_return_wit_10_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_11_distinct_nodes : atype_unify2_return_wit_11_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_12_same_node : atype_unify2_return_wit_12_same_node.
Axiom proof_of_atype_unify2_return_wit_13_same_node : atype_unify2_return_wit_13_same_node.
Axiom proof_of_atype_unify2_return_wit_14_distinct_nodes : atype_unify2_return_wit_14_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_15_same_node : atype_unify2_return_wit_15_same_node.
Axiom proof_of_atype_unify2_return_wit_16_distinct_nodes : atype_unify2_return_wit_16_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_17_distinct_nodes : atype_unify2_return_wit_17_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_18_distinct_nodes : atype_unify2_return_wit_18_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_19_same_node : atype_unify2_return_wit_19_same_node.
Axiom proof_of_atype_unify2_return_wit_20_distinct_nodes : atype_unify2_return_wit_20_distinct_nodes.
Axiom proof_of_atype_unify2_return_wit_21_same_node : atype_unify2_return_wit_21_same_node.
Axiom proof_of_atype_unify2_return_wit_22_distinct_nodes : atype_unify2_return_wit_22_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_1_same_node : atype_unify2_partial_solve_wit_1_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_2_distinct_nodes : atype_unify2_partial_solve_wit_2_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_3_same_node : atype_unify2_partial_solve_wit_3_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_4_same_node_pure : atype_unify2_partial_solve_wit_4_same_node_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_4_same_node : atype_unify2_partial_solve_wit_4_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_5_distinct_nodes : atype_unify2_partial_solve_wit_5_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_6_distinct_nodes_pure : atype_unify2_partial_solve_wit_6_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_6_distinct_nodes : atype_unify2_partial_solve_wit_6_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_7_same_node_pure : atype_unify2_partial_solve_wit_7_same_node_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_7_same_node : atype_unify2_partial_solve_wit_7_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_8_distinct_nodes_pure : atype_unify2_partial_solve_wit_8_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_8_distinct_nodes : atype_unify2_partial_solve_wit_8_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_9_same_node_pure : atype_unify2_partial_solve_wit_9_same_node_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_9_same_node : atype_unify2_partial_solve_wit_9_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes_pure : atype_unify2_partial_solve_wit_10_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_10_distinct_nodes : atype_unify2_partial_solve_wit_10_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_11_same_node : atype_unify2_partial_solve_wit_11_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_12_distinct_nodes : atype_unify2_partial_solve_wit_12_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_13_distinct_nodes : atype_unify2_partial_solve_wit_13_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_14_distinct_nodes_pure : atype_unify2_partial_solve_wit_14_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_14_distinct_nodes : atype_unify2_partial_solve_wit_14_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_15_distinct_nodes_pure : atype_unify2_partial_solve_wit_15_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_15_distinct_nodes : atype_unify2_partial_solve_wit_15_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes_pure : atype_unify2_partial_solve_wit_16_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_16_distinct_nodes : atype_unify2_partial_solve_wit_16_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_17_same_node : atype_unify2_partial_solve_wit_17_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_18_same_node : atype_unify2_partial_solve_wit_18_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_19_same_node : atype_unify2_partial_solve_wit_19_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_20_distinct_nodes : atype_unify2_partial_solve_wit_20_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_21_same_node : atype_unify2_partial_solve_wit_21_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_22_distinct_nodes : atype_unify2_partial_solve_wit_22_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_23_same_node : atype_unify2_partial_solve_wit_23_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_24_distinct_nodes_pure : atype_unify2_partial_solve_wit_24_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_24_distinct_nodes : atype_unify2_partial_solve_wit_24_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_25_same_node_pure : atype_unify2_partial_solve_wit_25_same_node_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_25_same_node : atype_unify2_partial_solve_wit_25_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_26_distinct_nodes : atype_unify2_partial_solve_wit_26_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_27_same_node : atype_unify2_partial_solve_wit_27_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_28_distinct_nodes : atype_unify2_partial_solve_wit_28_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_29_same_node : atype_unify2_partial_solve_wit_29_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_30_distinct_nodes_pure : atype_unify2_partial_solve_wit_30_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_30_distinct_nodes : atype_unify2_partial_solve_wit_30_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_31_same_node_pure : atype_unify2_partial_solve_wit_31_same_node_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_31_same_node : atype_unify2_partial_solve_wit_31_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_32_same_node : atype_unify2_partial_solve_wit_32_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_33_distinct_nodes : atype_unify2_partial_solve_wit_33_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_34_same_node : atype_unify2_partial_solve_wit_34_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_35_distinct_nodes : atype_unify2_partial_solve_wit_35_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_36_same_node_pure : atype_unify2_partial_solve_wit_36_same_node_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_36_same_node : atype_unify2_partial_solve_wit_36_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_37_distinct_nodes_pure : atype_unify2_partial_solve_wit_37_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_37_distinct_nodes : atype_unify2_partial_solve_wit_37_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_38_same_node : atype_unify2_partial_solve_wit_38_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_39_distinct_nodes : atype_unify2_partial_solve_wit_39_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_40_same_node : atype_unify2_partial_solve_wit_40_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_41_distinct_nodes : atype_unify2_partial_solve_wit_41_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_42_same_node_pure : atype_unify2_partial_solve_wit_42_same_node_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_42_same_node : atype_unify2_partial_solve_wit_42_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_43_distinct_nodes_pure : atype_unify2_partial_solve_wit_43_distinct_nodes_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_43_distinct_nodes : atype_unify2_partial_solve_wit_43_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_44_same_node : atype_unify2_partial_solve_wit_44_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_45_distinct_nodes : atype_unify2_partial_solve_wit_45_distinct_nodes.
Axiom proof_of_atype_unify2_partial_solve_wit_46_same_node : atype_unify2_partial_solve_wit_46_same_node.
Axiom proof_of_atype_unify2_partial_solve_wit_47_distinct_nodes : atype_unify2_partial_solve_wit_47_distinct_nodes.
Axiom proof_of_atype_unify_verify_entail_final : atype_unify_verify_entail_final.
Axiom proof_of_copy_atype_nonnull_entail_open_var : copy_atype_nonnull_entail_open_var.

End VC_Correct.
