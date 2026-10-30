#ifndef TYPEINFER_RC_H
#define TYPEINFER_RC_H

enum TypeOp
{
    AT_ATOM,
    AT_ARROW,
    AT_APP,
    AT_VAR
};

struct atype
{
    int refcnt;
    enum TypeOp t;
    union
    {
        struct
        {
            struct atype *from;
            struct atype *to;
        } ARROW;
        struct
        {
            struct atype *tfn;
            struct atype *rand;
        } APP;
        struct
        {
            int name;
        } VAR;
        struct
        {
            int name;
        } ATOM;
    } d;
};

/*@ Import Coq Require Import SimpleC.EE.Applications_human.typeinfer_rc.typeinfer_rc */
/* Contract reading guide:
 * With binds the input mathematical values; Require states facts about them.
 * A successful unify returns 0 and establishes unify_rel for those same inputs.
 * rc_capacity(stage, M, s, p, q) excludes retain-counter overflow throughout
 * the abstract execution (stage 0/1/2 = unify/unify1/unify2). It is NOT just
 * a bound on the current input counters, nor a termination/correctness premise.
 */
/*@ Extern Coq (TypeFieldSlot :: *) (TypeFieldKey :: *) (TypeTree :: *) (sol :: *) (RcState :: *) (TypeNode :: *) */
/*@ Extern Coq
    (TVar : Z -> TypeTree) (TAtom : Z -> TypeTree)
    (TArrow : TypeTree -> TypeTree -> TypeTree)
    (TApply : TypeTree -> TypeTree -> TypeTree)
    (Node : Z -> Z -> Z -> TypeNode)
    (node_tag : TypeNode -> Z) (node_a : TypeNode -> Z) (node_b : TypeNode -> Z)
    (node_at : RcState -> Z -> TypeNode -> Prop)
    (rc_valid : RcState -> Prop)
    (rc_count : RcState -> Z -> Z) (rc_roots : RcState -> Z -> Z)
    (rc_reserved : RcState -> Z -> Z)
    (rc_publish : RcState -> Z -> RcState)
    (rc_reservations_same : RcState -> RcState -> Prop)
    (rc_delete : RcState -> Z -> TypeNode -> RcState)
    (rc_decrement : RcState -> Z -> RcState)
    (rc_preserves : RcState -> RcState -> Prop)
    (store_type : RcState -> Z -> TypeTree -> Prop)
    (store_solution : RcState -> Z -> sol -> Assertion)
    (store_compressed_solution : RcState -> Z -> sol -> Assertion)
    (RefCount : TypeFieldSlot) (Tag : TypeFieldSlot)
    (Payload0 : TypeFieldSlot) (Payload1 : TypeFieldSlot)
    (field_key : Z -> TypeFieldSlot -> TypeFieldKey)
    (store_world_missing : RcState -> list TypeFieldKey -> Assertion)
    (store_type_field : RcState -> Z -> TypeNode -> TypeFieldSlot -> Assertion)
    (field_fresh : TypeFieldKey -> list TypeFieldKey -> Prop)
    (field_lookup : Z -> TypeFieldSlot -> list TypeFieldKey -> Prop)
    (payload_keys : Z -> TypeNode -> list TypeFieldKey)
    (store_world : RcState -> Assertion)
    (store_world_except : RcState -> Z -> Assertion)
    (store_node_payload : Z -> TypeNode -> Assertion)
    (store_payload_aux : Z -> TypeNode -> Assertion)
    (retain_rel : RcState -> Z -> RcState -> Prop)
    (release_rel : RcState -> Z -> RcState -> Prop)
    (rc_capacity : Z -> RcState -> sol -> Z -> Z -> Prop)
    (infer_result : Z -> RcState -> sol -> Z -> Z -> Z -> RcState -> sol -> Prop)
    (repr_result : RcState -> sol -> Z -> Z -> RcState -> Prop)
    (repr_rel_node : sol -> TypeTree -> TypeTree -> Prop)
    (solution_at : sol -> Z -> TypeTree -> Prop)
    (not_occur_final : sol -> Z -> TypeTree -> Prop)
    (not_var : TypeTree -> Prop)
    (sol_update : sol -> Z -> TypeTree -> sol)
    (sol_compress_to : sol -> sol -> Prop)
    (sol_finite : sol -> Prop) (sol_no_loop : sol -> Prop)
    (sol_correct_iter : TypeTree -> TypeTree -> sol -> sol -> Prop)
    (unify_rel : TypeTree -> TypeTree -> sol -> sol -> Prop)
*/


#endif
