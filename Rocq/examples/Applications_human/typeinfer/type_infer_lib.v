Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list.
Local Open Scope Z_scope.

Definition TypeVarID: Type := Z.

Inductive TypeTree: Type :=
| TVar (n: TypeVarID)
| TAtom (n: Z)
| TApply (tfn rand: TypeTree)
| TArrow (from to: TypeTree).

Definition sol: Type :=
  TypeVarID -> option TypeTree.

Fixpoint type_subst (t: TypeTree) (s: sol): TypeTree :=
  match t with
  | TVar n =>
      match s n with
      | Some t0 => t0
      | None => TVar n
      end
  | TAtom n => TAtom n
  | TApply t1 t2 => TApply (type_subst t1 s) (type_subst t2 s)
  | TArrow t1 t2 => TArrow (type_subst t1 s) (type_subst t2 s)
  end.

Fixpoint type_subst_var (t: TypeTree) (n: TypeVarID) (tn: TypeTree): TypeTree :=
  match t with
  | TVar n0 => if Z.eq_dec n n0 then tn else t
  | TAtom _ => t
  | TApply t1 t2 => TApply (type_subst_var t1 n tn) (type_subst_var t2 n tn)
  | TArrow t1 t2 => TArrow (type_subst_var t1 n tn) (type_subst_var t2 n tn)
  end.

(* let s[n] = t *)
Definition sol_update (s: sol) (n: TypeVarID) (t: TypeTree): sol :=
  fun n' => if Z.eq_dec n n' then Some t else s n'.

Definition sol_c_update (s: sol) (n: TypeVarID) (t: TypeTree): sol :=
  fun n' => if Z.eq_dec n n' then Some t else
    match (s n') with
    | Some(tn') => Some(type_subst_var tn' n t)
    | None => None
    end.

Fixpoint occur (n: TypeVarID) (t: TypeTree): Prop :=
  match t with
  | TVar n0 => n = n0
  | TAtom _ => False
  | TApply t1 t2 => occur n t1 \/ occur n t2
  | TArrow t1 t2 => occur n t1 \/ occur n t2
  end.

Definition sol_compressed (s: sol): Prop :=
  forall n m: TypeVarID,
    match s n, s m with
    | Some t, Some _ => ~ occur m t
    | _, _ => True
    end.

Definition sol_compress_to (s sc: sol): Prop :=
  sol_compressed sc /\
  forall n: TypeVarID,
    match s n with
    | Some t => sc n = Some (type_subst t sc)
    | None => sc n = None
    end.

Definition sol_no_loop (s: sol): Prop :=
  forall n t,
    s n = Some t -> ~ occur n t.

Definition sol_valid_eq (t1 t2: TypeTree) (s: sol): Prop :=
  type_subst t1 s = type_subst t2 s.

Definition sol_valid_eqs (eqns: list (TypeTree * TypeTree)) (s: sol): Prop :=
  forall t1 t2,
    In (t1, t2) eqns -> sol_valid_eq t1 t2 s.

Definition sol_refine (general specific: sol): Prop :=
  forall t: TypeTree,
  type_subst t specific = type_subst (type_subst t general) specific.

Fixpoint no_var (t: TypeTree): Prop :=
  match t with
  | TVar _ => False
  | TAtom _ => True
  | TApply t1 t2 => no_var t1 /\ no_var t2
  | TArrow t1 t2 => no_var t1 /\ no_var t2
  end.

Definition sol_no_var (s: sol): Prop :=
  forall n: TypeVarID,
    match s n with
    | Some t => no_var t
    | None => True
    end.


Definition sol_finite (s: sol): Prop :=
  exists ids: list TypeVarID,
    forall n: TypeVarID,
      In n ids <-> s n <> None.

Definition not_var (t: TypeTree): Prop :=
  match t with
  | TVar _ => False
  | _ => True
  end.

Inductive repr_rel_id (s: sol): TypeVarID -> TypeTree -> Prop :=
| repr_rel_var:
    forall n, s n = None -> repr_rel_id s n (TVar n)
| repr_rel_not_var:
    forall n t, s n = Some t -> not_var t -> repr_rel_id s n t
| repr_rel_rec:
    forall n m t,
      s n = Some (TVar m) -> repr_rel_id s m t -> repr_rel_id s n t.

Inductive repr_rel_node (s: sol): TypeTree -> TypeTree -> Prop :=
| repr_rel_node_var:
    forall n t, repr_rel_id s n t -> repr_rel_node s (TVar n) t
| repr_rel_node_not_var:
    forall t, not_var t -> repr_rel_node s t t.

Definition not_occur_final (s: sol) (n: TypeVarID) (t: TypeTree): Prop :=
  forall sc,
  sol_compress_to s sc ->
  ~occur n (type_subst t sc).

Inductive unify_rel: TypeTree -> TypeTree -> sol -> sol -> Prop :=
| unify_rel_left_var:
    forall s t1 n1 t2 t2'
      (R1: repr_rel_node s t1 (TVar n1))
      (R2: repr_rel_node s t2 t2')
      (Occ: not_occur_final s n1 t2'),
      unify_rel t1 t2 s (sol_update s n1 t2')
| unify_rel_right_var:
    forall s t1 t1' t2 n2
      (R1: repr_rel_node s t1 t1')
      (R2: repr_rel_node s t2 (TVar n2))
      (Occ: not_occur_final s n2 t1'),
      unify_rel t1 t2 s (sol_update s n2 t1')
| unify_rel_apply:
    forall s0 s1 s2 t1 t11 t12 t2 t21 t22
      (R1: repr_rel_node s0 t1 (TApply t11 t12))
      (R2: repr_rel_node s0 t2 (TApply t21 t22))
      (U1: unify_rel t11 t21 s0 s1)
      (U2: unify_rel t12 t22 s1 s2),
      unify_rel t1 t2 s0 s2
| unify_rel_arrow:
    forall s0 s1 s2 t1 t11 t12 t2 t21 t22
      (R1: repr_rel_node s0 t1 (TArrow t11 t12))
      (R2: repr_rel_node s0 t2 (TArrow t21 t22))
      (U1: unify_rel t11 t21 s0 s1)
      (U2: unify_rel t12 t22 s1 s2),
      unify_rel t1 t2 s0 s2
| unify_rel_atom:
    forall s t1 t2 n
      (R1: repr_rel_node s t1 (TAtom n))
      (R2: repr_rel_node s t2 (TAtom n)),
      unify_rel t1 t2 s s.

Definition sol_correct_iter (t1 t2: TypeTree) (s_pre s_post: sol): Prop :=
  forall sf: sol,
    sol_compressed sf ->
    (sol_valid_eq t1 t2 sf /\ sol_refine s_pre sf <->
      sol_refine s_post sf).

Definition unify_sound1: Prop :=
  forall t1 t2 s_pre s_post s_cpre
  (C_spre2scpre: sol_compress_to s_pre s_cpre)
  (NoLoop_spre: sol_no_loop s_pre)
  (Finite_scpre: sol_finite s_cpre)
  (U: unify_rel t1 t2 s_pre s_post),
  exists s_cpost,
    sol_compress_to s_post s_cpost /\
    sol_no_loop s_post /\
    sol_finite s_cpost /\
    sol_correct_iter t1 t2 s_cpre s_cpost.

Definition unify_sound (t1 t2 : TypeTree) (s_pre s_post : sol) : Prop :=
  forall s_cpre, 
    sol_compress_to s_pre s_cpre ->
    sol_finite s_cpre ->
  exists s_cpost,
    sol_compress_to s_post s_cpost /\
    sol_finite s_cpost /\
    sol_no_loop s_post /\
    sol_correct_iter t1 t2 s_cpre s_cpost.

