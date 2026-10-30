Require Import Coq.Structures.Equalities.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import SimpleC.Common.CTypes.
Require Import AUXLib.ListLib.
From AUXLib Require Import EqDec.

Inductive FieldName: Type :=
  | CFN_named (s: string): FieldName
  | CFN_unnamed (i: Z): FieldName.
  (** A struct/union field can be named or unnamed.
      Every unnamed field has a distinct id. *)

Inductive TypeName: Type :=
  | CTN_named (s: string): TypeName
  | CTN_unnamed (i: Z): TypeName.
  (** A struct/union/enum type can be named or unnamed.
      Every unnamed type has a distinct id. *)

Inductive SimpleCtype : Type :=
  | CT_basic (t: CBasicType): SimpleCtype 
      (** basic types *)
  | CT_pointer (t: SimpleCtype): SimpleCtype 
      (** pointer types ( * t ) *)
  | CT_array (t: SimpleCtype) (n: option Z): SimpleCtype
      (** array types
          - normal array, CT_array t (Some n) for t[n]
          - dynamic array, CT_array t None for t[] *)
  | CT_function (t0: SimpleCtype) (ts: list SimpleCtype): SimpleCtype
      (** function types *)
  | CT_struct (i: TypeName) (lvl: nat): SimpleCtype   (** struct types *)
  | CT_union (i: TypeName) (lvl: nat): SimpleCtype    (** union types *)
  | CT_enum (i: TypeName) (lvl: nat): SimpleCtype     (** enum types *)
  | CT_alias (s: string) (lvl: nat): SimpleCtype      (** typedef types *)
.

(* Zig style notations for C types *)
Module SimpleCtypeNotations.
  Declare Scope ctype_scope.
  Delimit Scope ctype_scope with ctype.
  Bind Scope ctype_scope with SimpleCtype.

  Notation "'i8'" := (CT_basic (CT_int Signed I8)) : ctype_scope.
  Notation "'i16'" := (CT_basic (CT_int Signed I16)) : ctype_scope.
  Notation "'i32'" := (CT_basic (CT_int Signed I32)) : ctype_scope.
  Notation "'i64'" := (CT_basic (CT_int Signed I64)) : ctype_scope.
  Notation "'u8'" := (CT_basic (CT_int Unsigned I8)) : ctype_scope.
  Notation "'u16'" := (CT_basic (CT_int Unsigned I16)) : ctype_scope.
  Notation "'u32'" := (CT_basic (CT_int Unsigned I32)) : ctype_scope.
  Notation "'u64'" := (CT_basic (CT_int Unsigned I64)) : ctype_scope.
  Notation "'void'" := (CT_basic CT_void) : ctype_scope.
  Notation "'cbool'" := (CT_basic CT_bool) : ctype_scope.
  Notation "* t" := (CT_pointer t)
    (at level 30, right associativity, format " '*' t") : ctype_scope.
  Notation "t .[ n ]" := (CT_array t (Some n%Z))
    (at level 1, left associativity, format "t .[ n ]") : ctype_scope.
  Notation "t .[ ]" := (CT_array t None)
    (at level 1, left associativity, format "t .[ ]") : ctype_scope.
  Notation "'fn' () t0" :=
    (CT_function t0 nil)
    (at level 30, right associativity) : ctype_scope.
  Notation "'fn' ( t1 , .. , tn ) t0" :=
    (CT_function t0 (cons t1 .. (cons tn nil) ..))
    (at level 30, right associativity, t1 at level 30, tn at level 30) : ctype_scope.
  Notation "'struct' i" := (CT_struct (CTN_named i) 0)
    (at level 0, i at level 0) : ctype_scope.
  Notation "'union' i" := (CT_union (CTN_named i) 0)
    (at level 0, i at level 0) : ctype_scope.
  Notation "'enum' i" := (CT_enum (CTN_named i) 0)
    (at level 0, i at level 0) : ctype_scope.

  Goal ( * *i32)%ctype = CT_pointer (CT_pointer (CT_basic (CT_int Signed I32))).
  Proof. reflexivity. Qed.

  Goal (i32.[2].[3])%ctype =
    CT_array (CT_array (CT_basic (CT_int Signed I32)) (Some 2%Z)) (Some 3%Z).
  Proof. reflexivity. Qed.

  Goal ( *i32.[10])%ctype =
    CT_pointer (CT_array (CT_basic (CT_int Signed I32)) (Some 10%Z)).
  Proof. reflexivity. Qed.

  Goal ( *i32.[2 * 3])%ctype =
    CT_pointer (CT_array (CT_basic (CT_int Signed I32)) (Some (2 * 3)%Z)).
  Proof. reflexivity. Qed.

  Goal (fn () void)%ctype =
    CT_function (CT_basic CT_void) nil.
  Proof. reflexivity. Qed.

  Goal (fn (i8, *u16.[4]) *fn (u32) u64)%ctype =
    CT_function
      (CT_pointer
        (CT_function
          (CT_basic (CT_int Unsigned I64))
          (CT_basic (CT_int Unsigned I32) :: nil)))
      (CT_basic (CT_int Signed I8) ::
       CT_pointer
         (CT_array (CT_basic (CT_int Unsigned I16)) (Some 4%Z)) :: nil).
  Proof. reflexivity. Qed.

  Goal (fn (struct "node".[8], *union "value") enum "tag")%ctype =
    CT_function
      (CT_enum (CTN_named "tag") 0)
      (CT_array (CT_struct (CTN_named "node") 0) (Some 8%Z) ::
       CT_pointer (CT_union (CTN_named "value") 0) :: nil).
  Proof. reflexivity. Qed.
End SimpleCtypeNotations.

Definition is_integral_type (t : SimpleCtype) : bool :=
  match t with
  | CT_basic CT_bool => true
  | CT_basic (CT_int _ _) => true
  | _ => false (* TODO: typedef handling *)
  end.

Definition is_pointer_type (t : SimpleCtype) : bool :=
  match t with
  | CT_pointer _ => true
  | _ => false (* TODO: typedef handling *)
  end.

Definition is_arith_type (t: SimpleCtype): bool :=
  match t with
  | CT_basic t =>
      match t with
      | CT_bool => true
      | CT_int _ _ => true
      | CT_void => false
      end
  | CT_pointer _ => false
  | CT_array _ _ => false
  | CT_function _ _ => false
  | CT_struct _ _ => false
  | CT_union _ _ => false
  | CT_enum _ _ => false
  | CT_alias _ _ => false (* TODO: how to handle typedef? *)
  end.

Definition is_scalar_type (t: SimpleCtype): bool :=
  match t with
  | CT_basic t =>
      match t with
      | CT_void => false
      | CT_bool => true
      | CT_int _ _ => true
      end
  | CT_pointer _ => true
  | CT_array _ _ => false
  | CT_function _ _ => false
  | CT_struct _ _ => false
  | CT_union _ _ => false
  | CT_enum _ _ => false
  | CT_alias _ _ => false (* TODO: how to handle typedef? *)
  end.

#[export] Instance FieldName_eqdec: EqDec FieldName eq.
  refine (fun x y => match
    x, y with
    | CFN_named s1, CFN_named s2 => match string_dec s1 s2 with
                                    | left pf => left (f_equal (fun pf => CFN_named pf) pf)
                                    | right pf => right _
                                    end
    | CFN_unnamed i1, CFN_unnamed i2 => match Z.eq_dec i1 i2 with
                                      | left pf => left (f_equal (fun pf => CFN_unnamed pf) pf)
                                      | right pf => right _
                                      end
    | _, _ => right _
    end
  ); congruence.
Defined.

#[export] Instance TypeName_eqdec: EqDec TypeName eq.
  refine (fun x y => match
    x, y with
    | CTN_named s1, CTN_named s2 => match string_dec s1 s2 with
                                    | left pf => left (f_equal (fun pf => CTN_named pf) pf)
                                    | right pf => right _
                                    end
    | CTN_unnamed i1, CTN_unnamed i2 => match Z.eq_dec i1 i2 with
                                      | left pf => left (f_equal (fun pf => CTN_unnamed pf) pf)
                                      | right pf => right _
                                      end
    | _, _ => right _
    end
  ); congruence.
Defined.

#[export] Instance SimpleCtype_eqdec: EqDec SimpleCtype eq.
Proof.
  refine (fix SimpleCtype_eqdec (x y: SimpleCtype): {x = y} + {x <> y} :=
    match x, y with
    | CT_basic t1, CT_basic t2 =>
        match CBasicType_eqdec t1 t2 with
        | left pf => left (f_equal (fun pf => CT_basic pf) pf)
        | right pf => right _
        end
    | CT_pointer t1, CT_pointer t2 =>
        match SimpleCtype_eqdec t1 t2 with
        | left pf => left (f_equal (fun pf => CT_pointer pf) pf)
        | right pf => right _
        end
    | CT_array t1 n1, CT_array t2 n2 =>
        match SimpleCtype_eqdec t1 t2, option_eqdec n1 n2 with
        | left pf1, left pf2 => left (f_equal2 (fun pf1 pf2 => CT_array pf1 pf2) pf1 pf2)
        | _, _ => right _
        end
    | CT_function t1 ts1, CT_function t2 ts2 =>
        match SimpleCtype_eqdec t1 t2, list_eqdec SimpleCtype_eqdec ts1 ts2 with
        | left pf1, left pf2 => left (f_equal2 (fun pf1 pf2 => CT_function pf1 pf2) pf1 pf2)
        | _, _ => right _
        end
    | CT_struct i1 lvl1, CT_struct i2 lvl2 =>
        match TypeName_eqdec i1 i2, Nat.eq_dec lvl1 lvl2 with
        | left pf1, left pf2 => left (f_equal2 (fun pf1 pf2 => CT_struct pf1 pf2) pf1 pf2)
        | _, _ => right _
        end
    | CT_union i1 lvl1, CT_union i2 lvl2 =>
        match TypeName_eqdec i1 i2, Nat.eq_dec lvl1 lvl2 with
        | left pf1, left pf2 => left (f_equal2 (fun pf1 pf2 => CT_union pf1 pf2) pf1 pf2)
        | _, _ => right _
        end
    | CT_enum i1 lvl1, CT_enum i2 lvl2 =>
        match TypeName_eqdec i1 i2, Nat.eq_dec lvl1 lvl2 with
        | left pf1, left pf2 => left (f_equal2 (fun pf1 pf2 => CT_enum pf1 pf2) pf1 pf2)
        | _, _ => right _
        end
    | CT_alias s1 lvl1, CT_alias s2 lvl2 =>
        match string_dec s1 s2, Nat.eq_dec lvl1 lvl2 with
        | left pf1, left pf2 => left (f_equal2 (fun pf1 pf2 => CT_alias pf1 pf2) pf1 pf2)
        | _, _ => right _
        end
    | _, _ => right _
    end
  ); congruence.
Defined.


Inductive TypeDecl: Type :=
  | CTDecl_struct (i: string): TypeDecl
  | CTDecl_union (i: string): TypeDecl
  | CTDecl_enum (i: string): TypeDecl.

Record FieldDecl: Type :=
  {
    field_name: FieldName;
    field_type: SimpleCtype;
  }.

Record Enumerator: Type :=
  {
    enumerator_name: string;
    enumerator_value: Z;
  }.

Inductive TypeDef: Type :=
  | CTDef_struct (i: TypeName) (m: list FieldDecl)
  | CTDef_union (i: TypeName) (m: list FieldDecl)
  | CTDef_enum (i: TypeName) (m: list Enumerator)
  | CTDef_typedef (i: string) (t: SimpleCtype).

Definition SimpleCtype_full_ind
             (P: SimpleCtype -> Prop)
             (Q: list SimpleCtype -> Prop)
             (H_basic: forall t: CBasicType, P (CT_basic t))
             (H_pointer: forall t (IHt: P t), P (CT_pointer t))
             (H_array: forall t (IHt: P t) (len: option Z), P (CT_array t len))
             (H_function: forall t0 (IHt0: P t0) ts (IHts: Q ts),
                          P (CT_function t0 ts))
             (H_struct: forall i lvl, P (CT_struct i lvl))
             (H_union: forall i lvl, P (CT_union i lvl))
             (H_enum: forall i lvl, P (CT_enum i lvl))
             (H_alias: forall s lvl, P (CT_alias s lvl))
             (H_nil: Q nil)
             (H_cons: forall t (IHt: P t) ts (IHts: Q ts), Q (cons t ts)):
  forall t, P t :=
  (fix ind (t: SimpleCtype): P t :=
     match t with
     | CT_basic t0 => H_basic t0
     | CT_pointer t0 => H_pointer t0 (ind t0)
     | CT_array t0 len => H_array t0 (ind t0) len
     | CT_function t0 ts =>
         H_function t0 (ind t0) ts
           ((fix list_ind (ts: list SimpleCtype): Q ts :=
              match ts with
              | nil => H_nil
              | cons t ts0 => H_cons t (ind t) ts0 (list_ind ts0)
              end) ts)
     | CT_struct i lvl => H_struct i lvl
     | CT_union i lvl => H_union i lvl
     | CT_enum i lvl => H_enum i lvl
     | CT_alias s lvl => H_alias s lvl
     end).

Module FieldName <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := FieldName.
  Definition eq := @Logic.eq FieldName.
  Definition eqb (t1 t2: FieldName): bool :=
    match t1, t2 with
    | CFN_named s1, CFN_named s2 => String.eqb s1 s2
    | CFN_unnamed i1, CFN_unnamed i2 => Z.eqb i1 i2
    | _, _ => false
    end.
  Lemma eqb_eq:
    forall t1 t2: FieldName, eqb t1 t2 = true <-> t1 = t2.
  Proof.
    intros.
    destruct t1, t2; simpl.
    + rewrite String.eqb_eq.
      split; intros; congruence.
    + split; intros; congruence.
    + split; intros; congruence.
    + rewrite Z.eqb_eq.
      split; intros; congruence.
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End FieldName.

Module TypeName <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := TypeName.
  Definition eq := @Logic.eq TypeName.
  Definition eqb (t1 t2: TypeName): bool :=
    match t1, t2 with
    | CTN_named s1, CTN_named s2 => String.eqb s1 s2
    | CTN_unnamed i1, CTN_unnamed i2 => Z.eqb i1 i2
    | _, _ => false
    end.
  Lemma eqb_eq:
    forall t1 t2: TypeName, eqb t1 t2 = true <-> t1 = t2.
  Proof.
    intros.
    destruct t1, t2; simpl.
    + rewrite String.eqb_eq.
      split; intros; congruence.
    + split; intros; congruence.
    + split; intros; congruence.
    + rewrite Z.eqb_eq.
      split; intros; congruence.
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End TypeName.

Module SimpleCtype <: UsualBoolEq.

  Set Inline Level 30.
  Definition t := SimpleCtype.
  Definition eq := @Logic.eq SimpleCtype.
  Fixpoint eqb (t1 t2: SimpleCtype): bool :=
    match t1, t2 with
    | CT_basic t1, CT_basic t2 =>
        CBasicType.eqb t1 t2
    | CT_pointer ty1, CT_pointer ty2 =>
        eqb ty1 ty2 
    | CT_array ty1 len1, CT_array ty2 len2 =>
        eqb ty1 ty2 && option_eqb Z.eqb len1 len2
    | CT_function ty1 tys1, CT_function ty2 tys2 =>
        eqb ty1 ty2 && list_eqb eqb tys1 tys2
    | CT_struct i1 lvl1, CT_struct i2 lvl2 =>
        TypeName.eqb i1 i2 && Nat.eqb lvl1 lvl2
    | CT_union i1 lvl1, CT_union i2 lvl2 =>
        TypeName.eqb i1 i2 && Nat.eqb lvl1 lvl2
    | CT_enum i1 lvl1, CT_enum i2 lvl2 =>
        TypeName.eqb i1 i2 && Nat.eqb lvl1 lvl2
    | CT_alias s1 lvl1, CT_alias s2 lvl2 =>
        String.eqb s1 s2 && Nat.eqb lvl1 lvl2
    | _ , _ => false
    end.

  Lemma eqb_eq:
    forall t1 t2: SimpleCtype, eqb t1 t2 = true <-> t1 = t2.
  Proof.
    apply
      (SimpleCtype_full_ind
        (fun t1 => forall t2, eqb t1 t2 = true <-> t1 = t2)
        (fun ts1 => forall ts2, list_eqb eqb ts1 ts2 = true <-> ts1 = ts2)).
    + intros t1 t2.
      destruct t2 as [t2 | | | | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite CBasicType.eqb_eq.
      split; intros; congruence.
    + intros t1 IHt1 t2.
      destruct t2 as [| t2 | | | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite IHt1.
      split; intros; congruence.
    + intros t1 IHt1 len1 t2.
      destruct t2 as [| | t2 len2 | | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite option_eqb_eq by apply Z.eqb_eq.
      rewrite IHt1.
      split; [intros [? ?] | intros; split]; congruence.
    + intros t1 IHt1 ts1 IHts1 t2.
      destruct t2 as [| | | t2 ts2 | | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite IHt1, IHts1.
      split; [intros [? ?] | intros; split]; congruence.
    + intros i1 lvl1 t2.
      destruct t2 as [| | | | i2 lvl2 | | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite TypeName.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + intros i1 lvl1 t2.
      destruct t2 as [| | | | | i2 lvl2 | |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite TypeName.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + intros i1 lvl1 t2.
      destruct t2 as [| | | | | | i2 lvl2 |]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite TypeName.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + intros s1 lvl1 t2.
      destruct t2 as [| | | | | | | s2 lvl2]; simpl;
        try solve [split; intros; congruence].
      rewrite andb_true_iff.
      rewrite String.eqb_eq, Nat.eqb_eq.
      split; [intros [? ?] | intros; split]; congruence.
    + apply list_eqb_eq_nil.
    + intros t IHt ts IHts.
      apply list_eqb_eq_cons; auto.
  Qed.

  Include UsualIsEq.
  Include BoolEqualityFacts.
  Include HasEqBool2Dec.

End SimpleCtype.
