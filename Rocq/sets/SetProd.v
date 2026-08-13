Require Import Coq.Classes.Morphisms.
Require Coq.Lists.List.
Require Import SetsClass.SetsDomain.
Local Open Scope sets_scope.

Class SETS_PROD (T1 T2 T: Type): Type := {
  liftL: T1 -> T;
  liftR: T2 -> T;
}.

#[export] Instance Prop_SETS_PROD
           (T: Type)
           {SETS: Sets.SETS T}: SETS_PROD Prop T T :=
{|
  liftL := fun P => Sets.prop_inj P;
  liftR := fun x => x;
|}.

#[export] Instance lift_SETS_PROD
           (A T1 T2 T: Type)
           {_SETS: SETS_PROD T1 T2 T}:
  SETS_PROD (A -> T1) T2 (A -> T) :=
{|
  liftL := fun x a => liftL (x a);
  liftR := fun y a => liftR y;
|}.

Class SETS_PROD_Distr
        (T1 T2 T: Type)
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}: Prop :=
{
  Sets_liftL_intersect: forall x y: T1,
    liftL (Sets.intersect x y) == Sets.intersect (liftL x) (liftL y);
  Sets_liftR_intersect: forall x y: T2,
    liftR (Sets.intersect x y) == Sets.intersect (liftR x) (liftR y);
  Sets_liftL_union: forall x y: T1,
    liftL (Sets.union x y) == Sets.union (liftL x) (liftL y);
  Sets_liftR_union: forall x y: T2,
    liftR (Sets.union x y) == Sets.union (liftR x) (liftR y);
  Sets_liftL_prop_inj: forall P: Prop,
    liftL (Sets.prop_inj P) == Sets.prop_inj P;
  Sets_liftR_prop_inj: forall P: Prop,
    liftR (Sets.prop_inj P) == Sets.prop_inj P;
  Sets_liftL_mono::
    Proper (@Sets.included T1 _ ==> @Sets.included T _) liftL;
  Sets_liftR_mono::
    Proper (@Sets.included T2 _ ==> @Sets.included T _) liftR;
}.

Class SETS_PROD_Comp
        (T1 T2 T3 T12 T23 T: Type)
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD_1_2: SETS_PROD T1 T2 T12}
        {_SETS_PROD_2_3: SETS_PROD T2 T3 T23}
        {_SETS_PROD_1_23: SETS_PROD T1 T23 T}
        {_SETS_PROD_12_3: SETS_PROD T12 T3 T}: Prop :=
{
  Sets_liftL_liftL: forall x: T1,
    liftL (liftL x) == liftL x;
  Sets_liftL_liftR: forall x: T2,
    liftL (liftR x) == liftR (liftL x);
  Sets_liftR_liftR: forall x: T3,
    liftR (liftR x) == liftR x
}.

#[export] Instance Prop_SETS_PROD_Distr
           (T: Type)
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}:
  @SETS_PROD_Distr Prop T T _ _ _ (Prop_SETS_PROD T).
Proof.
  constructor; intros; simpl.
  + apply Sets_prop_inj_and.
  + reflexivity.
  + apply Sets_prop_inj_or.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + unfold Proper, respectful.
    apply Sets_prop_inj_mono.
  + unfold Proper, respectful.
    intros; exact H.
Qed.

#[export] Instance Prop_SETS_PROD_Comp
           (T2 T3 T23: Type)
           {_SETS_T2: Sets.SETS T2}
           {_SETS_T3: Sets.SETS T3}
           {_SETS_T23: Sets.SETS T23}
           {_SETS_Properties23: SETS_Properties T23}
           {_SETS_PROD_2_3: SETS_PROD T2 T3 T23}
           {_SETS_PROD_Distr_2_3: SETS_PROD_Distr T2 T3 T23}:
  SETS_PROD_Comp Prop T2 T3 T2 T23 T23.
Proof.
  constructor; simpl; intros.
  + apply Sets_liftL_prop_inj.
  + reflexivity.
  + reflexivity.
Qed.

#[export] Instance lift_SETS_PROD_Distr
           (A T1 T2 T: Type)
           {_SETS_T1: Sets.SETS T1}
           {_SETS_T2: Sets.SETS T2}
           {_SETS_T: Sets.SETS T}
           {_SETS: SETS_PROD T1 T2 T}
           {_SETS_Properties_T1: SETS_Properties T1}
           {_SETS_Properties_T2: SETS_Properties T2}
           {_SETS_Properties_T: SETS_Properties T}
           {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  @SETS_PROD_Distr (A -> T1) T2 (A -> T) _ _ _ (lift_SETS_PROD A T1 T2 T).
Proof.
  constructor; intros.
  + sets_unfold.
    intros a; simpl.
    apply Sets_liftL_intersect.
  + sets_unfold.
    intros a; simpl.
    apply Sets_liftR_intersect.
  + sets_unfold.
    intros a; simpl.
    apply Sets_liftL_union.
  + sets_unfold.
    intros a; simpl.
    apply Sets_liftR_union.
  + sets_unfold.
    intros a; simpl.
    apply Sets_liftL_prop_inj.
  + sets_unfold.
    intros a; simpl.
    apply Sets_liftR_prop_inj.
  + unfold Proper, respectful; sets_unfold; intros.
    apply Sets_liftL_mono, H.
  + unfold Proper, respectful; sets_unfold; intros.
    apply Sets_liftR_mono, H.
Qed.

#[export] Instance lift_SETS_PROD_Comp
        (A T1 T2 T3 T12 T23 T: Type)
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD_1_2: SETS_PROD T1 T2 T12}
        {_SETS_PROD_2_3: SETS_PROD T2 T3 T23}
        {_SETS_PROD_1_23: SETS_PROD T1 T23 T}
        {_SETS_PROD_12_3: SETS_PROD T12 T3 T}
        {_SETS_PROD_Comp: SETS_PROD_Comp T1 T2 T3 T12 T23 T}:
  SETS_PROD_Comp (A -> T1) T2 T3 (A -> T12) T23 (A -> T).
Proof.
  constructor; intros.
  + sets_unfold; intros a; simpl.
    apply Sets_liftL_liftL.
  + sets_unfold; intros a; simpl.
    apply Sets_liftL_liftR.
  + sets_unfold; intros a; simpl.
    apply Sets_liftR_liftR.
Qed.

Arguments liftL: simpl never.
Arguments liftR: simpl never.

Definition prod
             {T1 T2 T: Type}
             {_SETS_T: Sets.SETS T}
             {_SETS: SETS_PROD T1 T2 T}
             (x: T1) (y: T2): T :=
  Sets.intersect (liftL x) (liftR y).

Ltac any_prod x y :=
  match type of x with
  | Type =>
      match type of y with
      | Type => exact (prod (@Sets.full (x -> Prop) _) (@Sets.full (y -> Prop) _))
      | Set => exact (prod (@Sets.full (x -> Prop) _) (@Sets.full (y -> Prop) _))
      | _ => exact (prod (@Sets.full (x -> Prop) _) y)
      end
  | Set =>
      match type of y with
      | Type => exact (prod (@Sets.full (x -> Prop) _) (@Sets.full (y -> Prop) _))
      | Set => exact (prod (@Sets.full (x -> Prop) _) (@Sets.full (y -> Prop) _))
      | _ => exact (prod (@Sets.full (x -> Prop) _) y)
      end
  | _ =>
      match type of y with
      | Type => exact (prod x (@Sets.full (y -> Prop) _))
      | Set => exact (prod x (@Sets.full (y -> Prop) _))
      | _ => exact (prod x y)
      end
  end.

Notation "x × y" := (prod x y)
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (prod x (@Sets.full (y -> Prop) _))
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (prod (@Sets.full (x -> Prop) _) y)
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (prod (@Sets.full (x -> Prop) _) (@Sets.full (y -> Prop) _))
  (left associativity, only printing, at level 11): sets_scope.
Notation "x × y" := (ltac:(any_prod x y))
  (left associativity, only parsing, at level 11): sets_scope.

#[export] Instance Sets_liftL_congr
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  Proper (@Sets.equiv T1 _ ==> @Sets.equiv T _) liftL.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_liftL_mono.
    rewrite H.
    reflexivity.
  + apply Sets_liftL_mono.
    rewrite H.
    reflexivity.
Qed.

#[export] Instance Sets_liftR_congr
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  Proper (@Sets.equiv T2 _ ==> @Sets.equiv T _) liftR.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_liftR_mono.
    rewrite H.
    reflexivity.
  + apply Sets_liftR_mono.
    rewrite H.
    reflexivity.
Qed.

Lemma Sets_liftL_full
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  liftL Sets.full == Sets.full.
Proof.
  intros.
  rewrite <- Sets_prop_inj_full.
  rewrite Sets_liftL_prop_inj.
  rewrite Sets_prop_inj_full.
  reflexivity.
Qed.

Lemma Sets_liftR_full
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  liftR Sets.full == Sets.full.
Proof.
  intros.
  rewrite <- Sets_prop_inj_full.
  rewrite Sets_liftR_prop_inj.
  rewrite Sets_prop_inj_full.
  reflexivity.
Qed.

Lemma Sets_liftL_empty
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  liftL Sets.empty == Sets.empty.
Proof.
  intros.
  rewrite <- Sets_prop_inj_empty.
  rewrite Sets_liftL_prop_inj.
  rewrite Sets_prop_inj_empty.
  reflexivity.
Qed.

Lemma Sets_liftR_empty
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  liftR Sets.empty == Sets.empty.
Proof.
  intros.
  rewrite <- Sets_prop_inj_empty.
  rewrite Sets_liftR_prop_inj.
  rewrite Sets_prop_inj_empty.
  reflexivity.
Qed.

Lemma Sets_prod_union_distr_r
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  forall (x y: T1) (z: T2),
    (x ∪ y) × z == x × z ∪ y × z.
Proof.
  unfold prod.
  intros.
  rewrite Sets_liftL_union.
  apply Sets_intersect_union_distr_r.
Qed.

Lemma Sets_prod_union_distr_l
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  forall (x: T1) (y z: T2),
    x × (y ∪ z) == x × y ∪ x × z.
Proof.
  unfold prod.
  intros.
  rewrite Sets_liftR_union.
  apply Sets_intersect_union_distr_l.
Qed.

Lemma Sets_prod_assoc
        {T1 T2 T3 T12 T23 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T3: Sets.SETS T3}
        {_SETS_T12: Sets.SETS T12}
        {_SETS_T23: Sets.SETS T23}
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD_1_2: SETS_PROD T1 T2 T12}
        {_SETS_PROD_2_3: SETS_PROD T2 T3 T23}
        {_SETS_PROD_1_23: SETS_PROD T1 T23 T}
        {_SETS_PROD_12_3: SETS_PROD T12 T3 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T3: SETS_Properties T3}
        {_SETS_Properties_T12: SETS_Properties T12}
        {_SETS_Properties_T23: SETS_Properties T23}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr_1_2: SETS_PROD_Distr T1 T2 T12}
        {_SETS_PROD_Distr_3_3: SETS_PROD_Distr T2 T3 T23}
        {_SETS_PROD_Distr_12_3: SETS_PROD_Distr T12 T3 T}
        {_SETS_PROD_Distr_1_23: SETS_PROD_Distr T1 T23 T}
        {_SETS_PROD_Comp: SETS_PROD_Comp T1 T2 T3 T12 T23 T}:
  forall (x: T1) (y: T2) (z: T3),
    x × y × z == x × (y × z).
Proof.
  unfold prod.
  intros.
  rewrite Sets_liftL_intersect.
  rewrite Sets_liftR_intersect.
  rewrite Sets_liftL_liftL.
  rewrite Sets_liftL_liftR.
  rewrite Sets_liftR_liftR.
  rewrite Sets_intersect_assoc.
  reflexivity.
Qed.

Lemma Sets_prod_empty
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  forall (x: T1),
    x × (@Sets.empty T2 _) == (@Sets.empty T _).
Proof.
  unfold prod.
  intros.
  rewrite Sets_liftR_empty.
  rewrite Sets_intersect_empty.
  reflexivity.
Qed.

Lemma Sets_empty_prod
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  forall (x: T2),
    (@Sets.empty T1 _) × x == (@Sets.empty T _).
Proof.
  unfold prod.
  intros.
  rewrite Sets_liftL_empty.
  rewrite Sets_empty_intersect.
  reflexivity.
Qed.

#[export] Instance Sets_prod_mono
           {T1 T2 T: Type}
           {_SETS_T1: Sets.SETS T1}
           {_SETS_T2: Sets.SETS T2}
           {_SETS_T: Sets.SETS T}
           {_SETS: SETS_PROD T1 T2 T}
           {_SETS_Properties_T1: SETS_Properties T1}
           {_SETS_Properties_T2: SETS_Properties T2}
           {_SETS_Properties_T: SETS_Properties T}
           {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  Proper
    (@Sets.included T1 _ ==> @Sets.included T2 _ ==> @Sets.included T _)
    prod.
Proof.
  unfold Proper, respectful.
  unfold prod.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance Sets_prod_congr
           {T1 T2 T: Type}
           {_SETS_T1: Sets.SETS T1}
           {_SETS_T2: Sets.SETS T2}
           {_SETS_T: Sets.SETS T}
           {_SETS: SETS_PROD T1 T2 T}
           {_SETS_Properties_T1: SETS_Properties T1}
           {_SETS_Properties_T2: SETS_Properties T2}
           {_SETS_Properties_T: SETS_Properties T}
           {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  Proper
    (@Sets.included T1 _ ==> @Sets.included T2 _ ==> @Sets.included T _)
    prod.
Proof.
  unfold Proper, respectful.
  unfold prod.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_prod_full
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  forall (x: T1),
    x × (@Sets.full T2 _) == liftL x.
Proof.
  unfold prod.
  intros.
  rewrite Sets_liftR_full.
  rewrite Sets_intersect_full.
  reflexivity.
Qed.

Lemma Sets_full_prod
        {T1 T2 T: Type}
        {_SETS_T1: Sets.SETS T1}
        {_SETS_T2: Sets.SETS T2}
        {_SETS_T: Sets.SETS T}
        {_SETS_PROD: SETS_PROD T1 T2 T}
        {_SETS_Properties_T1: SETS_Properties T1}
        {_SETS_Properties_T2: SETS_Properties T2}
        {_SETS_Properties_T: SETS_Properties T}
        {_SETS_PROD_Distr: SETS_PROD_Distr T1 T2 T}:
  forall (x: T2),
    (@Sets.full T1 _) × x == liftR x.
Proof.
  unfold prod.
  intros.
  rewrite Sets_liftL_full.
  rewrite Sets_full_intersect.
  reflexivity.
Qed.

Ltac SETS_PROD_unfold1 _SETS_PROD :=
  match _SETS_PROD with
  | @lift_SETS_PROD _ _ _ _ _ =>
      let p := eval unfold lift_SETS_PROD at 1 in _SETS_PROD in
      constr:(p)
  | @Prop_SETS_PROD _ _ =>
      let p := eval unfold Prop_SETS_PROD in _SETS_PROD in
      constr:(p)
  | @Build_SETS_PROD _ _ _
      _ _ =>
      constr:(_SETS_PROD)
  end.

Ltac test_SETS_PROD_unit _SETS_PROD :=
  match _SETS_PROD with
  | @lift_SETS_PROD _ _ _ _ _ =>
      constr:(tt)
  | @Prop_SETS_PROD _ _ =>
      constr:(tt)
  | @Build_SETS_PROD _ _ _
      _ _ =>
      constr:(tt)
  end.

Ltac SETS_PROD_simplify T :=
  match T with
  | @prod ?S1 ?S2 ?S ?_SETS ?_SETS_PROD =>
      let _ := test_SETS_unit _SETS in
      let _ := test_SETS_PROD_unit _SETS_PROD in
      let op1 := eval cbv delta [prod] in (@prod) in
      let T1 := eval cbv beta zeta iota in (op1 S1 S2 S _SETS _SETS_PROD) in
      constr:(T1)
  | ?op ?S1 ?S2 ?S ?_SETS_PROD =>
      let _ := test_SETS_PROD_unit _SETS_PROD in
      let op1 := eval cbv delta [liftL liftR] in op in
      let _SETS_PROD1 := SETS_PROD_unfold1 _SETS_PROD in
      let T1 := eval cbv beta zeta iota in (op1 S1 S2 S _SETS_PROD1) in
      constr:(T1)
  end.

Ltac SETS_PROD_simplify_rec T :=
  match T with
  | context G [@prod ?S1 ?S2 ?S3 ?_SETS ?_SETS_PROD] =>
      let S := SETS_PROD_simplify (@prod S1 S2 S3 _SETS _SETS_PROD) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@liftL ?S1 ?S2 ?S3 ?_SETS_PROD] =>
      let S := SETS_PROD_simplify (@liftL S1 S2 S3 _SETS_PROD) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@liftR ?S1 ?S2 ?S3 ?_SETS_PROD] =>
      let S := SETS_PROD_simplify (@liftR S1 S2 S3 _SETS_PROD) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | _ =>
      let T1 := SETS_simplify_rec T in
      constr:(T1)
  end.

Ltac SIMPLIFY_TAC T ::= SETS_PROD_simplify_rec T.

Ltac add_MarkerWrapper_rec T :=
  match T with
  | context G [@prod ?S1 ?S2 ?S ?_SETS ?_SETS_PROD] =>
      let S := constr:(MarkerWrapper2 (@prod S1 S2 S _SETS) _SETS_PROD) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | _ =>
      let T1 := SetsDomain.add_MarkerWrapper_rec T in
      constr:(T1)
  end.

Ltac ADD_MARKER_WRAPPER_TAC T ::=
  add_MarkerWrapper_rec T.

Section TestTac.

Variable A: Type.
Variable F: A -> A.
Variable X: A.
Definition G := F.
Definition H := fun x => F (F x).

Ltac TEST_TAC T :=
  constr:(T).

Ltac test_tac :=
  match goal with
  | |- ?P => let P' := TEST_TAC P in
             change P'
  end.

Ltac UF1_rec T :=
  match T with
  | context C [G ?x] =>
      let T1 := context C [(F x)] in
      let T2 := TEST_TAC T1 in
      constr:(T2)
  | _ => constr:(T)
  end.

Ltac TEST_TAC T ::= UF1_rec T.

Goal G (G X) = G (G (G X)).
  test_tac.
Abort.

Ltac UF2_rec T :=
  match T with
  | context C [H ?x] =>
      let T1 := context C [(G (G x))] in
      let T2 := TEST_TAC T1 in
      constr:(T2)
  | _ => constr:(T)
  end.

Ltac TEST_TAC T ::=
  let T1 := UF1_rec T in
  let T2 := UF2_rec T1 in
  constr:(T2).

Goal G (H X) = H (G X).
  test_tac.
Abort.

End TestTac.
