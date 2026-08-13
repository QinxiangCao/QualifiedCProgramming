Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Setoids.Setoid.
Require Import SetsClass.SetElement.

Module Sets.

Class SETS (T: Type): Type :=
{
  full: T;
  empty: T;
  prop_inj: Prop -> T;
  complement: T -> T;
  intersect: T -> T -> T;
  union: T -> T -> T;
  indexed_intersect: forall {I}, (I -> T) -> T;
  indexed_union: forall {I}, (I -> T) -> T;
  equiv: T -> T -> Prop;
  included: T -> T -> Prop;
  Taux: Type -> Type;
  Qaux: forall T0, (T0 -> Prop) -> Taux T0;
  Paux: forall T0, (T0 -> T) -> Taux T0;
  conj_aux: forall T0, Taux T0 -> Taux T0 -> Taux T0;
  imply_aux: forall T0, Taux T0 -> Taux T0 -> Taux T0;
  forall_aux: forall T0, Taux T0 -> T;
  exists_aux: forall T0, Taux T0 -> T;
  inj_aux: forall T0, T -> Taux T0;
  derives_aux: forall T0, Taux T0 -> Taux T0 -> T0 -> Prop
}.

Definition general_union {T} {_SETS: SETS T}: (T -> Prop) -> T :=
  fun P => exists_aux T (conj_aux T (Qaux T P) (Paux T (fun x => x))).

Definition general_intersect {T} {_SETS: SETS T}: (T -> Prop) -> T :=
  fun P => forall_aux T (imply_aux T (Qaux T P) (Paux T (fun x => x))).

Definition lift_full {A B} {_SETS: SETS B}: A -> B := fun _ => full.

Definition lift_empty {A B} {_SETS: SETS B}: A -> B := fun _ => empty.

Definition lift_prop_inj {A B} {_SETS: SETS B}: Prop -> A -> B :=
  fun P _ => prop_inj P.

Definition lift_complement {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) :=
  fun x a => complement (x a).

Definition lift_intersect {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> (A -> B) :=
  fun x y a => intersect (x a) (y a).

Definition lift_union {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> (A -> B) :=
  fun x y a => union (x a) (y a).

Definition lift_indexed_intersect {A B} {_SETS: SETS B}: forall {I}, (I -> A -> B) -> (A -> B) :=
  fun I x a => indexed_intersect (fun i => x i a).

Definition lift_indexed_union {A B} {_SETS: SETS B}: forall {I}, (I -> A -> B) -> (A -> B) :=
  fun I x a => indexed_union (fun i => x i a).

Definition lift_equiv {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> Prop :=
  fun x y => forall a, equiv (x a) (y a).

Definition lift_included {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> Prop :=
  fun x y => forall a, included (x a) (y a).

Definition lift_Taux {A B} {_SETS: SETS B}: Type -> Type :=
  fun T => A -> Taux T.

Definition lift_Qaux {A B} {_SETS: SETS B}:
  forall T0, (T0 -> Prop) -> A -> Taux T0 := 
  fun T0 X _ => Qaux T0 X.

Definition lift_Paux {A B} {_SETS: SETS B}:
  forall T0, (T0 -> (A -> B)) -> A -> Taux T0 := 
  fun T0 inj a => Paux T0 (fun t => inj t a).
  
Definition lift_conj_aux {A B} {_SETS: SETS B}:
  forall T0, (A -> Taux T0) -> (A -> Taux T0) -> (A -> Taux T0) := 
  fun T0 x y a => conj_aux T0 (x a) (y a).

Definition lift_imply_aux {A B} {_SETS: SETS B}:
  forall T0, (A -> Taux T0) -> (A -> Taux T0) -> (A -> Taux T0) := 
  fun T0 x y a => imply_aux T0 (x a) (y a).

Definition lift_forall_aux {A B} {_SETS: SETS B}:
  forall T0, (A -> Taux T0) -> (A -> B) := 
  fun T0 x a => forall_aux T0 (x a).

Definition lift_exists_aux {A B} {_SETS: SETS B}:
  forall T0, (A -> Taux T0) -> (A -> B) := 
  fun T0 x a => exists_aux T0 (x a).

Definition lift_derives_aux {A B} {_SETS: SETS B}:
  forall T0, (A -> Taux T0) -> (A -> Taux T0) -> T0 -> Prop := 
  fun T0 x y t0 => forall a, derives_aux T0 (x a) (y a) t0.

Definition lift_inj_aux {A B} {_SETS: SETS B}:
  forall T0, (A -> B) -> (A -> Taux T0) := 
  fun T0 x a => inj_aux T0 (x a).

Definition test1 {A B} {_SETS: SETS B}: (A -> Prop) -> (A -> B) :=
  fun P a => prop_inj (P a).

Definition lift1 {A B} {_SETS: SETS B}: B -> (A -> B) :=
  fun x _ => x.

Definition filter1 {A B} {_SETS: SETS B}: (A -> Prop) -> (A -> B) -> (A -> B) :=
  fun P x => lift_intersect (test1 P) x.

Definition projB {A B} (s: (A * B) -> Prop): B -> Prop:= 
  fun b => exists a, s (a,b).

Definition singleton {A: Type} (a: A): A -> Prop := eq a.

End Sets.

Arguments Sets.full: simpl never.
Arguments Sets.empty: simpl never.
Arguments Sets.prop_inj: simpl never.
Arguments Sets.complement: simpl never.
Arguments Sets.intersect: simpl never.
Arguments Sets.union: simpl never.
Arguments Sets.indexed_intersect: simpl never.
Arguments Sets.indexed_union: simpl never.
Arguments Sets.general_intersect: simpl never.
Arguments Sets.general_union: simpl never.
Arguments Sets.equiv: simpl never.
Arguments Sets.included: simpl never.
Arguments Sets.singleton: simpl never.

#[export] Instance Prop_SETS: Sets.SETS Prop :=
  {|
    Sets.full := True;
    Sets.empty := False;
    Sets.prop_inj := fun P => P;
    Sets.complement := not;
    Sets.intersect := and;
    Sets.union := or;
    Sets.indexed_intersect := fun I P => forall i, P i;
    Sets.indexed_union := @ex;
    Sets.equiv := iff;
    Sets.included := fun P Q => P -> Q;
    Sets.Taux := fun T => T -> Prop;
    Sets.Qaux := fun T0 X P => X P;
    Sets.Paux := fun T0 inj P => inj P;
    Sets.conj_aux := fun T0 x y a => x a /\ y a;
    Sets.imply_aux := fun T0 x y a => x a -> y a;
    Sets.forall_aux := fun T0 P => forall x, P x;
    Sets.exists_aux := fun T0 P => exists x, P x;
    Sets.inj_aux := fun T0 P _ => P;
    Sets.derives_aux := fun T0 x y t0 => x t0 -> y t0
  |}.

#[export] Instance lift_SETS (A B: Type) (_SETS: Sets.SETS B): Sets.SETS (A -> B) :=
  {|
    Sets.full := Sets.lift_full;
    Sets.empty := Sets.lift_empty;
    Sets.prop_inj := Sets.lift_prop_inj;
    Sets.complement := Sets.lift_complement;
    Sets.intersect := Sets.lift_intersect;
    Sets.union := Sets.lift_union;
    Sets.indexed_intersect := @Sets.lift_indexed_intersect _ _ _;
    Sets.indexed_union := @Sets.lift_indexed_union _ _ _;
    Sets.equiv := Sets.lift_equiv;
    Sets.included := Sets.lift_included;
    Sets.Taux := @Sets.lift_Taux A B _;
    Sets.Qaux := Sets.lift_Qaux;
    Sets.Paux := Sets.lift_Paux;
    Sets.conj_aux := Sets.lift_conj_aux;
    Sets.imply_aux := Sets.lift_imply_aux;
    Sets.forall_aux := Sets.lift_forall_aux;
    Sets.exists_aux := Sets.lift_exists_aux;
    Sets.inj_aux := Sets.lift_inj_aux;
    Sets.derives_aux := Sets.lift_derives_aux
  |}.

  
Ltac SETS_unfold1 SETS :=
  match SETS with
  | lift_SETS _ _ _ =>
      let p := eval unfold lift_SETS at 1 in SETS in
      constr:(p)
  | Prop_SETS =>
      let p := eval unfold Prop_SETS in SETS in
      constr:(p)
  | @Sets.Build_SETS _
      _ _ _ _ _ _
      _ _ _ _ _ _
      _ _ _ _ _ _ =>
      constr:(SETS)
  end.

Ltac test_SETS_unit _SETS :=
  match _SETS with
  | lift_SETS _ _ _ =>
      constr:(tt)
  | Prop_SETS =>
      constr:(tt)
  | @Sets.Build_SETS _
      _ _ _ _ _ _
      _ _ _ _ _ _
      _ _ _ _ _ _ =>
      constr:(tt)
  end.

Ltac SETS_simplify_part1 T :=
  match T with
  | ?op ?A ?SETS =>
      let _ := test_SETS_unit SETS in
      let op1 := eval cbv delta
              [Sets.full
               Sets.empty
               Sets.prop_inj
               Sets.complement
               Sets.intersect
               Sets.union
               Sets.indexed_intersect
               Sets.indexed_union
               Sets.equiv
               Sets.included
               Sets.general_intersect
               Sets.general_union
               Sets.Taux
               Sets.Qaux
               Sets.Paux
               Sets.conj_aux
               Sets.imply_aux
               Sets.forall_aux
               Sets.exists_aux] in op in
      let SETS1 := SETS_unfold1 SETS in
      let T1 := eval cbv beta zeta iota in (op1 A SETS1) in
      let T2 := eval cbv beta delta
              [Sets.lift_full
               Sets.lift_empty
               Sets.lift_prop_inj
               Sets.lift_complement
               Sets.lift_intersect
               Sets.lift_union
               Sets.lift_indexed_intersect
               Sets.lift_indexed_union
               Sets.lift_equiv
               Sets.lift_included
               Sets.lift_Taux
               Sets.lift_Qaux
               Sets.lift_Paux
               Sets.lift_conj_aux
               Sets.lift_imply_aux
               Sets.lift_forall_aux
               Sets.lift_exists_aux] in T1 in
      constr:(T2)
  end.

Ltac SETS_simplify_part2 T :=
  match T with
  | @Sets.filter1 ?A ?B ?SETS =>
      let T1 := constr:(fun (P: A -> Prop) (X: A -> B) (a: A) => @Sets.intersect B SETS (@Sets.test1 A B SETS P a) (X a)) in
      constr:(T1)
  | ?op ?A ?B ?SETS =>
      let op1 := eval cbv delta [Sets.lift1 Sets.test1] in op in
      let T1 := eval cbv beta zeta iota in (op1 A B SETS) in
      let T2 := eval cbv delta [Sets.lift_intersect] in T1 in
      constr:(T2)
  end.

Ltac SIMPLIFY_TAC T := constr:(T).

Ltac PATTERN1_INNER_TAC tac T := fail.

Ltac PATTERN1_TAC tac T :=
  match T with
  | context G [?S] =>
      let S' := PATTERN1_INNER_TAC tac S in
      let T' := context G [S'] in
      T'
  end.

Ltac SETS_simplify_rec T :=
  match T with
  | context G [@Sets.full ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.full T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.empty ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.empty T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.prop_inj ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.prop_inj T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.complement ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.complement T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.equiv ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.equiv T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.intersect ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.intersect T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.union ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.union T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.indexed_intersect ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.indexed_intersect T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.indexed_union ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.indexed_union T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.general_intersect ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.general_intersect T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.general_union ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.general_union T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.Taux ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.Taux T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.Paux ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.Paux T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.Qaux ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.Qaux T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.conj_aux ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.conj_aux T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.imply_aux ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.imply_aux T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.exists_aux ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.exists_aux T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.forall_aux ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.forall_aux T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.included ?T ?_SETS] =>
      let S := SETS_simplify_part1 (@Sets.included T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.filter1 ?A ?T ?_SETS] =>
      let S := SETS_simplify_part2 (@Sets.filter1 A T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.lift1 ?A ?T ?_SETS] =>
      let S := SETS_simplify_part2 (@Sets.lift1 A T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | context G [@Sets.test1 ?A ?T ?_SETS] =>
      let S := SETS_simplify_part2 (@Sets.test1 A T _SETS) in
      let T1 := context G [S] in
      let T2 := SIMPLIFY_TAC T1 in
      constr:(T2)
  | _ => constr:(T)
  end.

Ltac SETS_inner_pattern1 tac T :=
  match T with
  | ?op ?A ?SETS =>
      let _ := test_SETS_unit SETS in
      let ret := constr:(op A SETS) in
      match op with
      | @Sets.full =>
          let ret' := tac ret in ret'
      | @Sets.empty =>
          let ret' := tac ret in ret'
      | @Sets.prop_inj =>
          let ret' := tac ret in ret'
      | @Sets.complement =>
          let ret' := tac ret in ret'
      | @Sets.intersect =>
          let ret' := tac ret in ret'
      | @Sets.union =>
          let ret' := tac ret in ret'
      | @Sets.indexed_intersect =>
          let ret' := tac ret in ret'
      | @Sets.indexed_union =>
          let ret' := tac ret in ret'
      | @Sets.equiv =>
          let ret' := tac ret in ret'
      | @Sets.included =>
          let ret' := tac ret in ret'
      | @Sets.general_intersect =>
          let ret' := tac ret in ret'
      | @Sets.general_union =>
          let ret' := tac ret in ret'
      end
  | @Sets.filter1 ?A ?B ?SETS =>
      let ret := constr:(@Sets.filter1 A B SETS) in
      let ret' := tac ret in ret'
  | @Sets.lift1 ?A ?B ?SETS =>
      let ret := constr:(@Sets.lift1 A B SETS) in
      let ret' := tac ret in ret'
  | @Sets.test1 ?A ?B ?SETS =>
      let ret := constr:(@Sets.test1 A B SETS) in
      let ret' := tac ret in ret'
  end.

Ltac SIMPLIFY_TAC T ::= SETS_simplify_rec T.

Ltac PATTERN1_INNER_TAC tac T ::= SETS_inner_pattern1 tac T.

Ltac unfold_SETS_in_goal_tac :=
  match goal with
  | |- ?T =>
         let P := SIMPLIFY_TAC T in
         change P;
         cbv beta iota
  end.

Ltac unfold_SETS_in_hypo_tac H :=
  match type of H with
  | ?T =>
         let P := SIMPLIFY_TAC T in
         change P in H;
         cbv beta iota in H
  end.

Ltac unfold1_SETS_in_goal_tac :=
  match goal with
  | |- ?T1 =>
         let T2 := PATTERN1_TAC SIMPLIFY_TAC T1 in
         change T1 with T2;
         cbv beta iota
  end.

Ltac unfold1_SETS_in_hypo_tac H :=
  match type of H with
  | ?T1 =>
         let T2 := PATTERN1_TAC SIMPLIFY_TAC T1 in
         change T1 with T2 in H;
         cbv beta iota in H
  end.

(** 先给所有集合算子套上MarkerWrapper（会把 F X拆成，MW F X，因此每个只会套上一次） *)
(** 再一次解开MarkerWrapper（用Marker_curr保证每次只处理一个），如果这个算子的参数不是算子的话
    即没有add_In_Marker_head的话，那就要做transform。 *)

Definition add_In_Marker_curr {A B: Type} (f: A -> B) (a: A) := f a.
Definition add_In_Marker1 {A B: Type} (f: A -> B) (a: A) := f a.
Definition add_In_Marker1i {A B: Type} (f: A -> B) (a: A) := f a.
Definition add_In_Marker2 {A B: Type} (f: A -> B) (a: A) := f a.
Definition add_In_Marker2t {A B: Type} (f: A -> B) (a: A) := f a.
Definition add_In_Marker_head {A: Type} (a: A) := a.
Definition MarkerWrapper0 {A B: Type} (f: A -> B): A -> B :=
  fun (a: A) =>
    add_In_Marker_head (f a).
Definition MarkerWrapper1 {A B C: Type} (f: A -> B -> C): A -> B -> C :=
  fun (a: A) (x: B) =>
    add_In_Marker_head (add_In_Marker1 f a x).
Definition MarkerWrapper1N {A B C: Type} (f: A -> B -> C): A -> B -> C :=
  fun (a: A) (x: B) =>
    add_In_Marker_head (f a x).
Definition MarkerWrapper1i {A B: Type} (f: A -> forall I: Type, (I -> B) -> B):
  A -> forall I: Type, (I -> B) -> B :=
  fun (a: A) I (x: I -> B) =>
    add_In_Marker_head (add_In_Marker1i f a I x).
Definition MarkerWrapper2
           {A B C D: Type}
           (f: A -> B -> C -> D): A -> B -> C -> D :=
  fun (a: A) (x: B) (y: C) =>
    add_In_Marker_head (add_In_Marker2 f a x y).
Definition MarkerWrapper2t
           {A B C: Type}
           (f: A -> B -> C -> C): A -> B -> C -> C :=
  fun (a: A) (x: B) (y: C) =>
    add_In_Marker_head (add_In_Marker2t f a x y).

Ltac ADD_MARKER_WRAPPER_TAC T := constr:(T).
  
Ltac add_MarkerWrapper_rec T :=
  match T with
  | context G [@Sets.full ?T ?_SETS] =>
      let S := constr:(MarkerWrapper0 (@Sets.full T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.empty ?T ?_SETS] =>
      let S := constr:(MarkerWrapper0 (@Sets.empty T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.prop_inj ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1N (@Sets.prop_inj T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.complement ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1 (@Sets.complement T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.equiv ?T ?_SETS] =>
      let S := constr:(MarkerWrapper2 (@Sets.equiv T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.intersect ?T ?_SETS] =>
      let S := constr:(MarkerWrapper2 (@Sets.intersect T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.union ?T ?_SETS] =>
      let S := constr:(MarkerWrapper2 (@Sets.union T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.indexed_intersect ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1i (@Sets.indexed_intersect T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.indexed_union ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1i (@Sets.indexed_union T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.general_intersect ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1N (@Sets.general_intersect T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.general_union ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1N (@Sets.general_union T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.included ?T ?_SETS] =>
      let S := constr:(MarkerWrapper2 (@Sets.included T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.filter1 ?A ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1N (@Sets.filter1 A T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.lift1 ?A ?T ?_SETS] =>
      let S := constr:(MarkerWrapper1 (@Sets.lift1 A T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | context G [@Sets.test1 ?A ?T ?_SETS] =>
      let S := constr:(MarkerWrapper2t (@Sets.test1 A T) _SETS) in
      let T1 := context G [S] in
      let T2 := ADD_MARKER_WRAPPER_TAC T1 in
      constr:(T2)
  | _ => constr:(T)
  end.

Ltac ADD_MARKER_WRAPPER_TAC T ::= add_MarkerWrapper_rec T.

Ltac RESOLVE_MARKER_TAC T := constr:(T).

Ltac resolve_Marker_rec T :=
  match T with
  | context G [add_In_Marker1 ?_F ?_SETS] =>
      match type of (_F _SETS) with
      | ?A -> _ =>
          let T1 := context G [add_In_Marker_curr _F _SETS] in
          match T1 with
          | context [add_In_Marker_curr _ _ (add_In_Marker_head _)] =>
              let T2 := context G [_F _SETS] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          | _ =>
              let F := SETS_ELE_transfer_simplify_func A in
              let T2 := context G [fun a: A => _F _SETS (F a)] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          end
      end
  | context G [add_In_Marker1i ?_F ?_SETS] =>
      match type of (_F _SETS) with
      | forall I, (I -> ?A) -> ?A =>
          let T1 := context G [add_In_Marker_curr _F _SETS] in
          match T1 with
          | context [add_In_Marker_curr _ _ _ (fun _ => add_In_Marker_head _)] =>
              let T2 := context G [_F _SETS] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          | _ =>
              let F := SETS_ELE_transfer_simplify_func A in
              let T2 := context G
                          [fun (I: Type) (a: I -> A) => _F _SETS I (fun i: I => F (a i))] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          end
      end
  | context G [add_In_Marker2 ?_F ?_SETS] =>
      match type of (_F _SETS) with
      | ?A -> ?B -> _ =>
          let T1 := context G [add_In_Marker_curr _F _SETS] in
          match T1 with
          | context [add_In_Marker_curr
                       _ _
                       (add_In_Marker_head _)
                       (add_In_Marker_head _)] =>
              let T2 := context G [_F _SETS] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          | context [add_In_Marker_curr
                       _ _
                       (add_In_Marker_head _)
                       _] =>
              let FB := SETS_ELE_transfer_simplify_func B in
              let T2 := context G [fun (a: A) (b: B) => _F _SETS a (FB b)] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          | context [add_In_Marker_curr
                       _ _
                       _
                       (add_In_Marker_head _)] =>
              let FA := SETS_ELE_transfer_simplify_func A in
              let T2 := context G [fun (a: A) (b: B) => _F _SETS (FA a) b] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          | context [add_In_Marker_curr
                       _ _
                       _
                       _] =>
              let FA := SETS_ELE_transfer_simplify_func A in
              let FB := SETS_ELE_transfer_simplify_func B in
              let T2 := context G [fun (a: A) (b: B) => _F _SETS (FA a) (FB b)] in
              let T3 := RESOLVE_MARKER_TAC T2 in
              constr:(T3)
          end
      end
  | _ => constr:(T)
  end.

Ltac RESOLVE_MARKER_TAC T ::= resolve_Marker_rec T.

Ltac handle_general T :=
  match T with
  | context G [@Sets.general_union ?T ?_SETS] =>
    let F := SETS_ELE_transfer_simplify_func T in
    let T0 := context G [fun P =>
                Sets.exists_aux T (Sets.conj_aux T (Sets.Qaux T P) (Sets.Paux T (fun x => F x)))] in
    constr:(T0)
  | context G [@Sets.general_intersect ?T ?_SETS] =>
    let F := SETS_ELE_transfer_simplify_func T in
    let T0 := context G [fun P =>
                Sets.forall_aux T (Sets.imply_aux T (Sets.Qaux T P) (Sets.Paux T (fun x => F x)))] in
    constr:(T0)
  | _ => constr:(T)
  end.

Ltac UNFOLD_MARKER_TAC T :=
  let T0 := eval cbv beta delta
              [MarkerWrapper0
               MarkerWrapper1
               MarkerWrapper1i
               MarkerWrapper1N
               MarkerWrapper2
               MarkerWrapper2t] in T in
  constr:(T0).

Ltac SETS_simplify_add_In T :=
  let T1 := ADD_MARKER_WRAPPER_TAC T in
  let T2 := UNFOLD_MARKER_TAC T1 in
  let T3 := RESOLVE_MARKER_TAC T2 in
  let T4 := eval cbv beta delta [add_In_Marker_head] in T3 in
  let T5 := handle_general T4 in
  let T6 := SIMPLIFY_TAC T5 in
  constr:(T6).

Ltac unfold_SETS_add_In_in_goal_tac :=
  match goal with
  | |- ?T =>
         let P := SETS_simplify_add_In T in
         change P;
         cbv beta iota
  end.

Ltac unfold_SETS_add_In_in_hypo_tac H :=
  match type of H with
  | ?T =>
         let P := SETS_simplify_add_In T in
         change P in H;
         cbv beta iota in H
  end.

Ltac unfold1_SETS_add_In_in_goal_tac :=
  match goal with
  | |- ?T =>
         match T with
         | context [?op ?e ?s] =>
             match op with
             | @SetsEle.In ?E ?S ?SETS_ELE =>
                 let T11 := constr:(@SetsEle.In E S SETS_ELE) in
                 let T12 := SETS_ELE_In_simplify_rec T11 in
                 let s' := PATTERN1_TAC SETS_simplify_add_In s in
                 change (op e s) with (T12 e s') at 1;
                 cbv beta iota
             | @Sets.equiv ?S ?SETS =>
                 let T11 := constr:(@Sets.equiv S SETS) in
                 let T12 := SETS_simplify_add_In T11 in
                 change op with T12 at 1;
                 cbv beta iota
             | @Sets.included ?S ?SETS =>
                 let T11 := constr:(@Sets.included S SETS) in
                 let T12 := SETS_simplify_add_In T11 in
                 change op with T12 at 1;
                 cbv beta iota
             end
         end
  end.

Ltac unfold1_SETS_add_In_in_hypo_tac H :=
  match type of H with
  | ?T =>
         match T with
         | context [?op ?e ?s] =>
             match op with
             | @SetsEle.In ?E ?S ?SETS_ELE =>
                 let T11 := constr:(@SetsEle.In E S SETS_ELE) in
                 let T12 := SETS_ELE_In_simplify_rec T11 in
                 let s' := PATTERN1_TAC SETS_simplify_add_In s in
                 change (op e s) with (T12 e s') in H at 1;
                 cbv beta iota in H
             | @Sets.equiv ?S ?SETS =>
                 let T11 := constr:(@Sets.equiv S SETS) in
                 let T12 := SETS_simplify_add_In T11 in
                 change op with T12 in H at 1;
                 cbv beta iota in H
             | @Sets.included ?S ?SETS =>
                 let T11 := constr:(@Sets.included S SETS) in
                 let T12 := SETS_simplify_add_In T11 in
                 change op with T12 in H at 1;
                 cbv beta iota in H
             end
         end
  end.

Class SETS_Properties (T: Type) {_SETS: Sets.SETS T}: Prop :=
{
  Sets_included_refl: Reflexive Sets.included;
  Sets_included_trans: Transitive Sets.included;
  Sets_equiv_Sets_included: forall x y, Sets.equiv x y <-> (Sets.included x y /\ Sets.included y x);
  Sets_empty_included: forall x, Sets.included Sets.empty x;
  Sets_included_full: forall x, Sets.included x Sets.full;
  Sets_prop_inj_included: forall (P: Prop) x y, (P -> Sets.included x y) -> Sets.included (Sets.intersect (Sets.prop_inj P) x) y;
  Sets_included_prop_inj: forall (P: Prop) x, P -> Sets.included x (Sets.prop_inj P);
  Sets_complement_fact: forall x y, Sets.included x (Sets.complement y) <-> Sets.equiv (Sets.intersect x y) Sets.empty;
  Sets_intersect_included1: forall x y, Sets.included (Sets.intersect x y) x;
  Sets_intersect_included2: forall x y, Sets.included (Sets.intersect x y) y;
  Sets_included_intersect: forall x y z, Sets.included x y -> Sets.included x z -> Sets.included x (Sets.intersect y z);
  Sets_included_union1: forall x y, Sets.included x (Sets.union x y);
  Sets_included_union2: forall x y, Sets.included y (Sets.union x y);
  Sets_union_included_strong2: forall x y z u, Sets.included (Sets.intersect x u) z -> Sets.included (Sets.intersect y u) z -> Sets.included (Sets.intersect (Sets.union x y) u) z;
  Sets_indexed_union_included_strong2: forall {I: Type} (xs: I -> T) z u, (forall i, Sets.included (Sets.intersect (xs i) u) z) -> Sets.included (Sets.intersect (Sets.indexed_union xs) u) z;
  Sets_included_indexed_union: forall {I: Type} n (xs: I -> T), Sets.included (xs n) (Sets.indexed_union xs);
  Sets_indexed_union_included: forall I (xs: I -> T) y, (forall n, Sets.included (xs n) y) -> Sets.included (Sets.indexed_union xs) y;
  Sets_indexed_intersect_included: forall {I: Type} n (xs: I -> T), Sets.included (Sets.indexed_intersect xs) (xs n);
  Sets_included_indexed_intersect: forall I (xs: I -> T) y, (forall n, Sets.included y (xs n)) -> Sets.included y (Sets.indexed_intersect xs);
  Sets_included_derives_aux: forall T0 x y t0, Sets.included x y -> Sets.derives_aux T0 (Sets.inj_aux T0 x) (Sets.inj_aux T0 y) t0;
  Sets_derives_aux_trans: forall T0 t0, Transitive (fun x y => Sets.derives_aux T0 x y t0);
  Sets_Qaux_right: forall T0 t0 (Pr: T0 -> Prop) P,
    Pr t0 ->
    Sets.derives_aux T0 P (Sets.Qaux T0 Pr) t0;
  Sets_Paux_left: forall T0 t0 (inj: T0 -> T),
    Sets.derives_aux T0 (Sets.Paux T0 inj) (Sets.inj_aux T0 (inj t0)) t0;
  Sets_Paux_right: forall T0 t0 (inj: T0 -> T),
    Sets.derives_aux T0 (Sets.inj_aux T0 (inj t0)) (Sets.Paux T0 inj) t0;
  Sets_Qaux_left_extract: forall T0 t0 (Pr: T0 -> Prop) Q1 Q2,
    (Pr t0 -> Sets.derives_aux T0 Q1 Q2 t0) ->
    Sets.derives_aux T0 (Sets.conj_aux T0 (Sets.Qaux T0 Pr) Q1) Q2 t0;
  Sets_Qaux_right_extract: forall T0 t0 (Pr: T0 -> Prop) Q1 Q2,
    (Pr t0 -> Sets.derives_aux T0 Q1 Q2 t0) ->
    Sets.derives_aux T0 Q1 (Sets.imply_aux T0 (Sets.Qaux T0 Pr) Q2) t0;
  Sets_Qaux_implies_left: forall T0 t0 (Pr: T0 -> Prop) Q1 Q2,
    Pr t0 ->
    Sets.derives_aux T0 Q1 Q2 t0 ->
    Sets.derives_aux T0 (Sets.imply_aux T0 (Sets.Qaux T0 Pr) Q1) Q2 t0;
  Sets_conj_aux_right: forall T0 t0 P Q1 Q2,
    Sets.derives_aux T0 P Q1 t0 ->
    Sets.derives_aux T0 P Q2 t0 ->
    Sets.derives_aux T0 P (Sets.conj_aux T0 Q1 Q2) t0;
  Sets_exists_aux_left: forall T0 P Q,
    (forall t0, Sets.derives_aux T0 Q (Sets.inj_aux T0 P) t0) ->
    Sets.included (Sets.exists_aux T0 Q) P;
  Sets_exists_aux_right: forall T0 t0 P Q,
    Sets.derives_aux T0 (Sets.inj_aux T0 P) Q t0 ->
    Sets.included P (Sets.exists_aux T0 Q);
  Sets_forall_aux_left: forall T0 t0 P Q,
    Sets.derives_aux T0 Q (Sets.inj_aux T0 P) t0 ->
    Sets.included (Sets.forall_aux T0 Q) P;
  Sets_forall_aux_right: forall T0 P Q,
    (forall t0, Sets.derives_aux T0 (Sets.inj_aux T0 P) Q t0) ->
    Sets.included P (Sets.forall_aux T0 Q);
}.

#[export] Existing Instances Sets_included_refl Sets_included_trans.

Lemma Sets_included_general_union: forall {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} (xs: _ -> Prop) x, xs x -> Sets.included x (Sets.general_union xs).
Proof.
  intros.
  apply Sets_exists_aux_right with x.
  apply Sets_conj_aux_right.
  + apply Sets_Qaux_right; auto.
  + apply (Sets_Paux_right T x (fun x => x)).
Qed.

Lemma Sets_general_union_included: forall {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} (xs: _ -> Prop) y, (forall x, xs x -> Sets.included x y) -> Sets.included (Sets.general_union xs) y.
Proof.
  intros.
  apply Sets_exists_aux_left; intros.
  apply Sets_Qaux_left_extract; intros.
  apply H in H0.
  eapply (Sets_included_derives_aux T) in H0.
  eapply Sets_derives_aux_trans; eauto.
  apply (Sets_Paux_left T t0 (fun x => x)).
Qed.

Lemma Sets_general_intersect_included: forall {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} (xs: _ -> Prop) x, xs x -> Sets.included (Sets.general_intersect xs) x.
Proof.
  intros.
  apply Sets_forall_aux_left with x.
  apply Sets_Qaux_implies_left; auto.
  apply (Sets_Paux_left T x (fun x => x)).
Qed.

Lemma Sets_included_general_intersect: forall {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} (xs: _ -> Prop) y, (forall x, xs x -> Sets.included y x) -> Sets.included y (Sets.general_intersect xs).
Proof.
  intros.
  apply Sets_forall_aux_right; intros.
  apply Sets_Qaux_right_extract; intros.
  apply H in H0.
  eapply (Sets_included_derives_aux T) in H0.
  eapply Sets_derives_aux_trans; eauto.
  apply (Sets_Paux_right T t0 (fun x => x)).
Qed.

Lemma Sets_filter1_defn: forall {S T} {_SETS: Sets.SETS T} (P: S -> Prop) (Q: S -> T),
  Sets.filter1 P Q = Sets.intersect (Sets.test1 P) Q.
Proof.
  intros.
  reflexivity.
Qed.

#[export] Instance Sets_equiv_refl {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Reflexive Sets.equiv.
Proof.
  hnf; intros.
  apply Sets_equiv_Sets_included.
  split; apply Sets_included_refl.
Qed.

#[export] Instance Sets_equiv_sym {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Symmetric Sets.equiv.
Proof.
  hnf; intros.
  rewrite Sets_equiv_Sets_included in H |- *.
  tauto.
Qed.

#[export] Instance Sets_equiv_trans {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Transitive Sets.equiv.
Proof.
  hnf; intros.
  rewrite Sets_equiv_Sets_included in H, H0 |- *.
  destruct H, H0.
  split; eapply Sets_included_trans; eauto.
Qed.

#[export] Instance Sets_equiv_equiv {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Equivalence Sets.equiv.
Proof.
  constructor; auto.
  + apply Sets_equiv_refl; auto.
  + apply Sets_equiv_sym; auto.
  + apply Sets_equiv_trans; auto.
Qed.

#[export] Instance Sets_included_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> iff) Sets.included.
Proof.
  unfold Proper, respectful.
  intros.
  rewrite Sets_equiv_Sets_included in H, H0.
  destruct H, H0.
  split; intros;
  repeat (eapply Sets_included_trans; eauto).
Qed.

Lemma Sets_intersect_full_r {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.intersect x Sets.full) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_intersect_included1.
  + apply Sets_included_intersect.
    - reflexivity.
    - apply Sets_included_full.
Qed.

Lemma Sets_intersect_full_l {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.intersect Sets.full x) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_intersect_included2.
  + apply Sets_included_intersect.
    - apply Sets_included_full.
    - reflexivity.
Qed.

Lemma Sets_union_full_r {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.union x Sets.full) Sets.full.
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_included_full.
  + apply Sets_included_union2.
Qed.

Lemma Sets_union_full_l {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.union Sets.full x) Sets.full.
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_included_full.
  + apply Sets_included_union1.
Qed.

Lemma Sets_equiv_full_fact {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.included Sets.full x <-> Sets.equiv x Sets.full.
Proof.
  intros.
  split; intros.
  + apply Sets_equiv_Sets_included; split.
    - apply Sets_included_full.
    - apply H.
  + rewrite H.
    reflexivity.
Qed.

Lemma Sets_union_included {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z, Sets.included x z -> Sets.included y z -> Sets.included (Sets.union x y) z.
Proof.
  intros.
  pose proof Sets_union_included_strong2 x y z Sets.full.
  rewrite !Sets_intersect_full_r in H1.
  auto.
Qed.

#[export] Instance Sets_union_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.union.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_union_included.
  + apply Sets_included_trans with y; auto.
    apply Sets_included_union1.
  + apply Sets_included_trans with y0; auto.
    apply Sets_included_union2.
Qed.

#[export] Instance Sets_union_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.union.
Proof.
  hnf; intros; hnf; intros.
  apply Sets_equiv_Sets_included in H.
  apply Sets_equiv_Sets_included in H0.
  apply Sets_equiv_Sets_included; split;
  apply Sets_union_mono; tauto.
Qed.

#[export] Instance Sets_intersect_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.intersect.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_included_intersect.
  + rewrite <- H.
    apply Sets_intersect_included1.
  + rewrite <- H0.
    apply Sets_intersect_included2.
Qed.

#[export] Instance Sets_intersect_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.intersect.
Proof.
  hnf; intros; hnf; intros.
  apply Sets_equiv_Sets_included in H.
  apply Sets_equiv_Sets_included in H0.
  apply Sets_equiv_Sets_included; split;
  apply Sets_intersect_mono; tauto.
Qed.

#[export] Instance Sets_indexed_union_mono {A T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.indexed_union _ _ A).
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_indexed_union_included.
  intros.
  apply Sets_included_trans with (y n); auto.
  apply Sets_included_indexed_union.
Qed.

#[export] Instance Sets_indexed_union_congr {A T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.indexed_union _ _ A).
Proof.
  hnf; intros.
  apply Sets_equiv_Sets_included; split;
  apply Sets_indexed_union_mono;
  intros n; specialize (H n);
  apply Sets_equiv_Sets_included in H; tauto.
Qed.

#[export] Instance Sets_indexed_intersect_mono {A T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.indexed_intersect _ _ A).
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_included_indexed_intersect.
  intros.
  apply Sets_included_trans with (x n); auto.
  apply Sets_indexed_intersect_included.
Qed.

#[export] Instance Sets_indexed_intersect_congr {A T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.indexed_intersect _ _ A).
Proof.
  hnf; intros.
  apply Sets_equiv_Sets_included; split;
  apply Sets_indexed_intersect_mono;
  intros n; specialize (H n);
  apply Sets_equiv_Sets_included in H; tauto.
Qed.

Lemma Sets_intersect_absorb1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.intersect x y) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included1.
  + apply Sets_included_intersect.
    - reflexivity.
    - auto.
Qed.

Lemma Sets_intersect_absorb2 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.intersect y x) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included2.
  + apply Sets_included_intersect.
    - auto.
    - reflexivity.
Qed.

Lemma Sets_union_absorb1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included y x ->
    Sets.equiv (Sets.union x y) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - reflexivity.
    - auto.
  + apply Sets_included_union1.
Qed.

Lemma Sets_union_absorb2 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.union x y) y.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - auto.
    - reflexivity.
  + apply Sets_included_union2.
Qed.

Lemma Sets_union_comm {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y,
  Sets.equiv (Sets.union x y) (Sets.union y x).
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split; apply Sets_union_included;
  first [ apply Sets_included_union1 | apply Sets_included_union2 ].
Qed.

Lemma Sets_union_assoc {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.union (Sets.union x y) z)
      (Sets.union x (Sets.union y z)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split;
    repeat apply Sets_union_included.
  + apply Sets_included_union1.
  + rewrite <- Sets_included_union2.
    apply Sets_included_union1.
  + rewrite <- Sets_included_union2.
    apply Sets_included_union2.
  + rewrite <- Sets_included_union1.
    apply Sets_included_union1.
  + rewrite <- Sets_included_union1.
    apply Sets_included_union2.
  + apply Sets_included_union2.
Qed.

Lemma Sets_intersect_comm {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y,
  Sets.equiv (Sets.intersect x y) (Sets.intersect y x).
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split; apply Sets_included_intersect;
  first [ apply Sets_intersect_included1 | apply Sets_intersect_included2 ].
Qed.

Lemma Sets_intersect_assoc {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.intersect (Sets.intersect x y) z)
      (Sets.intersect x (Sets.intersect y z)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + repeat apply Sets_included_intersect.
    - rewrite Sets_intersect_included1.
      apply Sets_intersect_included1.
    - rewrite Sets_intersect_included1.
      apply Sets_intersect_included2.
    - apply Sets_intersect_included2.
  + repeat apply Sets_included_intersect.
    - apply Sets_intersect_included1.
    - rewrite Sets_intersect_included2.
      apply Sets_intersect_included1.
    - rewrite Sets_intersect_included2.
      apply Sets_intersect_included2.
Qed.

Lemma Sets_union_included_strong1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z u, Sets.included (Sets.intersect u x) z -> Sets.included (Sets.intersect u y) z -> Sets.included (Sets.intersect u (Sets.union x y)) z.
Proof.
  intros.
  rewrite Sets_intersect_comm in H, H0 |- *.
  apply Sets_union_included_strong2; auto.
Qed.

Lemma Sets_indexed_union_included_strong1 {I T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall (xs: I -> T) z u, (forall i, Sets.included (Sets.intersect u (xs i)) z) -> Sets.included (Sets.intersect u (Sets.indexed_union xs)) z.
Proof.
  intros.
  rewrite Sets_intersect_comm.
  apply Sets_indexed_union_included_strong2.
  intros.
  rewrite Sets_intersect_comm.
  apply H.
Qed.

Lemma Sets_union_empty_r {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union x Sets.empty) x.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - reflexivity.
    - apply Sets_empty_included.
  + apply Sets_included_union1.
Qed.

Lemma Sets_union_empty_l {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union Sets.empty x) x.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - apply Sets_empty_included.
    - reflexivity.
  + apply Sets_included_union2.
Qed.

Lemma Sets_equiv_empty_fact {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x,
    Sets.included x Sets.empty <->
    Sets.equiv x Sets.empty.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included.
  pose proof Sets_empty_included x.
  tauto.
Qed.

Lemma Sets_intersect_empty_r {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.intersect x Sets.empty) Sets.empty.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included2.
  + apply Sets_empty_included.
Qed.

Lemma Sets_intersect_empty_l {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.intersect Sets.empty x) Sets.empty.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included1.
  + apply Sets_empty_included.
Qed.

Lemma Sets_prop_inj_included_prop_inj {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: Prop),
  (P -> Q) ->
  Sets.included
    (Sets.prop_inj P)
    (Sets.prop_inj Q).
Proof.
  intros.
  rewrite <- Sets_intersect_full_r.
  apply Sets_prop_inj_included.
  intros.
  apply Sets_included_prop_inj.
  tauto.
Qed.

Lemma Sets_prop_inj_and {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall P Q,
  Sets.equiv
    (Sets.prop_inj (P /\ Q))
    (Sets.intersect (Sets.prop_inj P) (Sets.prop_inj Q)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_included_intersect.
    - apply Sets_prop_inj_included_prop_inj; tauto.
    - apply Sets_prop_inj_included_prop_inj; tauto.
  + apply Sets_prop_inj_included.
    intros.
    apply Sets_prop_inj_included_prop_inj; tauto.
Qed.

Lemma Sets_prop_inj_or {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall P Q,
  Sets.equiv
    (Sets.prop_inj (P \/ Q))
    (Sets.union (Sets.prop_inj P) (Sets.prop_inj Q)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + rewrite <- Sets_intersect_full_r.
    apply Sets_prop_inj_included.
    intros [? | ?].
    - rewrite <- Sets_included_union1.
      apply Sets_included_prop_inj, H.
    - rewrite <- Sets_included_union2.
      apply Sets_included_prop_inj, H.
  + apply Sets_union_included.
    - apply Sets_prop_inj_included_prop_inj; tauto.
    - apply Sets_prop_inj_included_prop_inj; tauto.
Qed.

Lemma Sets_prop_inj_ex {I T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P: I -> Prop),
  Sets.equiv
    (Sets.prop_inj (ex P))
    (Sets.indexed_union (fun i => Sets.prop_inj (P i))).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + rewrite <- Sets_intersect_full_r.
    apply Sets_prop_inj_included.
    intros [? ?].
    rewrite <- Sets_included_indexed_union.
    apply Sets_included_prop_inj, H.
  + apply Sets_indexed_union_included.
    intros.
    apply Sets_prop_inj_included_prop_inj.
    intros; exists n; auto.
Qed.

Lemma Sets_test1_imply {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: S -> Prop),
  (forall a, P a -> Q a) ->
  Sets.included (Sets.test1 P) (Sets.test1 Q).
Proof.
  intros.
  unfold_SETS_in_goal_tac; intros.
  apply Sets_prop_inj_included_prop_inj.
  auto.
Qed.

Lemma Sets_test1_and {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: S -> Prop),
  Sets.equiv
    (Sets.test1 (fun a => P a /\ Q a))
    (Sets.intersect (Sets.test1 P) (Sets.test1 Q)).
Proof.
  intros.
  unfold_SETS_in_goal_tac; intros.
  apply Sets_prop_inj_and.
Qed.

Lemma Sets_test1_or {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: S -> Prop),
  Sets.equiv
    (Sets.test1 (fun a => P a \/ Q a))
    (Sets.union (Sets.test1 P) (Sets.test1 Q)).
Proof.
  intros.
  unfold_SETS_in_goal_tac; intros.
  apply Sets_prop_inj_or.
Qed.

Lemma omega_union_union {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y (xs ys zs: nat -> T),
  (forall n, zs n = Sets.union (xs n) (ys n)) ->
  Sets.equiv x (Sets.indexed_union xs) /\ (forall n, Sets.included (xs n) (xs (S n))) ->
  Sets.equiv y (Sets.indexed_union ys) /\ (forall n, Sets.included (ys n) (ys (S n))) ->
  Sets.equiv (Sets.union x y) (Sets.indexed_union zs) /\ (forall n, Sets.included (zs n) (zs (S n))).
Proof.
  intros ? ? ? ? ? Hzs [Hx Hxs] [Hy Hys].
  rewrite Hx, Hy; clear x y Hx Hy.
  split; [apply Sets_equiv_Sets_included; split |].
  + apply Sets_union_included; apply Sets_indexed_union_included; intros n.
    - rewrite (Sets_included_union1 _ (ys n)), <- Hzs.
      apply Sets_included_indexed_union.
    - rewrite (Sets_included_union2 (xs n)), <- Hzs.
      apply Sets_included_indexed_union.
  + apply Sets_indexed_union_included; intros n.
    rewrite Hzs.
    apply Sets_union_included.
    - rewrite <- Sets_included_union1.
      apply Sets_included_indexed_union.
    - rewrite <- Sets_included_union2.
      apply Sets_included_indexed_union.
  + intros; rewrite !Hzs.
    apply Sets_union_mono; auto.
Qed.

Lemma omega_union_const {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv x (Sets.indexed_union (fun _: nat => x)) /\ (forall n: nat, Sets.included x x).
Proof.
  intros.
  split; [apply Sets_equiv_Sets_included; split |].
  + change x with ((fun _ => x) O) at 1.
    apply Sets_included_indexed_union.
  + apply Sets_indexed_union_included; intros n.
    reflexivity.
  + intros.
    reflexivity.
Qed.

#[export] Instance Prop_SETS_Properties: SETS_Properties Prop.
Proof.
  constructor; unfold Proper, respectful; unfold_SETS_in_goal_tac; simpl;
  hnf; intros; try tauto.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
Qed.

#[export] Instance lift_SETS_Properties (A B: Type) (_SETS: Sets.SETS B) (_SETS_Properties: SETS_Properties B): SETS_Properties (A -> B).
Proof.
  constructor; unfold Proper, respectful; unfold_SETS_in_goal_tac; hnf; intros.
  + apply Sets_included_refl.
  + eapply Sets_included_trans; eauto.
  + split; intros.
    - split; intros; specialize (H a);
      rewrite Sets_equiv_Sets_included in H;
      tauto.
    - destruct H.
      intros.
      rewrite Sets_equiv_Sets_included; auto.
  + apply Sets_empty_included.
  + apply Sets_included_full.
  + apply Sets_prop_inj_included; auto.
  + apply Sets_included_prop_inj; auto.
  + apply all_iff_morphism; intros a;
    apply Sets_complement_fact.
  + apply Sets_intersect_included1.
  + apply Sets_intersect_included2.
  + apply Sets_included_intersect; auto.
  + apply Sets_included_union1.
  + apply Sets_included_union2.
  + apply Sets_union_included_strong2; auto.
  + apply Sets_indexed_union_included_strong2; auto.
  + apply (Sets_included_indexed_union _ (fun n => xs n a)).
  + apply (Sets_indexed_union_included _ (fun n => xs n a)).
    auto.
  + apply (Sets_indexed_intersect_included _ (fun n => xs n a)).
  + apply (Sets_included_indexed_intersect _ (fun n => xs n a)).
    auto.
  + intros a.
    apply Sets_included_derives_aux; auto.
  + intros ? ? ? ? ? a.
    eapply Sets_derives_aux_trans; auto.
  + intros a.
    apply Sets_Qaux_right.
    auto.
  + intros a.
    apply (Sets_Paux_left T0 t0 (fun t => inj t a)).
  + intros a.
    simpl.
    unfold Sets.lift_inj_aux.
    unfold Sets.lift_Paux.
    exact (Sets_Paux_right T0 t0 (fun t => inj t a)).
  + intros a.
    apply Sets_Qaux_left_extract.
    intros; apply H; auto.
  + intros a.
    apply Sets_Qaux_right_extract.
    intros; apply H; auto.
  + intros a.
    apply Sets_Qaux_implies_left; auto.
  + intros a.
    apply Sets_conj_aux_right; auto.
  + apply Sets_exists_aux_left.
    intros; apply H; auto.
  + apply (Sets_exists_aux_right _ t0).
    apply H.
  + apply (Sets_forall_aux_left _ t0).
    apply H.
  + apply Sets_forall_aux_right.
    intros; apply H; auto.
Qed.

#[export] Instance Sets_prop_inj_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.prop_inj T _).
Proof.
  unfold Proper, respectful, Sets.test1.
  unfold_SETS_in_goal_tac.
  intros.
  apply Sets_prop_inj_included_prop_inj.
  auto.
Qed.

#[export] Instance Sets_prop_inj_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.prop_inj T _).
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_equiv_Sets_included.
  rewrite Sets_equiv_Sets_included in H.
  split; apply Sets_prop_inj_mono; tauto.
Qed.

#[export] Instance Sets_test1_mono {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.test1 S T _).
Proof.
  unfold Proper, respectful, Sets.test1.
  intros; intros ?.
  rewrite (H a).
  reflexivity.
Qed.

#[export] Instance Sets_test1_congr {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.test1 S T _).
Proof.
  unfold Proper, respectful, Sets.test1.
  intros; intros ?.
  rewrite (H a).
  reflexivity.
Qed.

#[export] Instance Sets_filter1_mono {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) (@Sets.filter1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  rewrite !Sets_filter1_defn.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance Sets_filter1_congr {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@Sets.filter1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  rewrite !Sets_filter1_defn.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance Sets_lift1_mono {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.lift1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  unfold Sets.lift1; intros ?.
  auto.
Qed.

#[export] Instance Sets_lift1_congr {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.lift1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  unfold Sets.lift1; intros ?.
  auto.
Qed.

#[export] Instance Sets_general_union_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) Sets.general_union.
Proof.
  intros.
  hnf; intros.
  rewrite Sets_equiv_Sets_included.
  split.
  + apply Sets_general_union_included; intros.
    apply Sets_included_general_union.
    rewrite (H _) in H0.
    tauto.
  + apply Sets_general_union_included; intros.
    apply Sets_included_general_union.
    rewrite (H _).
    tauto.
Qed.

#[export] Instance Sets_general_intersect_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) Sets.general_intersect.
Proof.
  intros.
  hnf; intros.
  rewrite Sets_equiv_Sets_included.
  split.
  + apply Sets_included_general_intersect; intros.
    apply Sets_general_intersect_included.
    rewrite (H _).
    tauto.
  + apply Sets_included_general_intersect; intros.
    apply Sets_general_intersect_included.
    rewrite (H _) in H0.
    tauto.
Qed.

Lemma Sets_prop_inj_full {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  @Sets.equiv T _SETS (Sets.prop_inj True) Sets.full.
Proof.
  pose proof (Sets_included_prop_inj True (Sets.full)).
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_included_full.
  + tauto.
Qed.
Lemma Sets_prop_inj_empty {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  @Sets.equiv T _SETS (Sets.prop_inj False) Sets.empty.
Proof.
  pose proof (Sets_prop_inj_included False Sets.full Sets.empty).
  rewrite Sets_intersect_full_r in H.
  rewrite Sets_equiv_Sets_included; split.
  + tauto.
  + apply Sets_empty_included.
Qed.

Lemma Sets_intersect_union_distr_r {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.intersect (Sets.union x y) z)
      (Sets.union (Sets.intersect x z) (Sets.intersect y z)).
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_union_included_strong2.
    - apply Sets_included_union1.
    - apply Sets_included_union2.
  + apply Sets_union_included.
    - apply Sets_intersect_mono; [| reflexivity].
      apply Sets_included_union1.
    - apply Sets_intersect_mono; [| reflexivity].
      apply Sets_included_union2.
Qed.

Lemma Sets_intersect_union_distr_l {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.intersect x (Sets.union y z))
      (Sets.union (Sets.intersect x y) (Sets.intersect x z)).
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_union_included_strong1.
    - apply Sets_included_union1.
    - apply Sets_included_union2.
  + apply Sets_union_included.
    - apply Sets_intersect_mono; [reflexivity |].
      apply Sets_included_union1.
    - apply Sets_intersect_mono; [reflexivity |].
      apply Sets_included_union2.
Qed.

Lemma Sets_union_intersect_distr_r {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.union (Sets.intersect x y) z)
      (Sets.intersect (Sets.union x z) (Sets.union y z)).
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_union_included.
    - apply Sets_included_intersect.
      * rewrite Sets_intersect_included1.
        apply Sets_included_union1.
      * rewrite Sets_intersect_included2.
        apply Sets_included_union1.
    - apply Sets_included_intersect.
      * apply Sets_included_union2.
      * apply Sets_included_union2.
  + apply Sets_union_included_strong1; apply Sets_union_included_strong2.
    - apply Sets_included_union1.
    - rewrite Sets_intersect_included1.
      apply Sets_included_union2.
    - rewrite Sets_intersect_included2.
      apply Sets_included_union2.
    - rewrite Sets_intersect_included2.
      apply Sets_included_union2.
Qed.

Lemma Sets_union_intersect_distr_l {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.union x (Sets.intersect y z))
      (Sets.intersect (Sets.union x y) (Sets.union x z)).
Proof.
  intros.
  rewrite (Sets_union_comm x).
  rewrite Sets_union_intersect_distr_r.
  rewrite ! (Sets_union_comm x).
  reflexivity.
Qed.

Lemma Sets_intersect_indexed_union_distr_r {I T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall (xs: I -> T) y,
    Sets.equiv
      (Sets.intersect (Sets.indexed_union xs) y)
      (Sets.indexed_union (fun i => Sets.intersect (xs i) y)).
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included_strong2.
    intros.
    rewrite <- Sets_included_indexed_union.
    reflexivity.
  + apply Sets_indexed_union_included.
    intros.
    apply Sets_intersect_mono; [| reflexivity].
    apply Sets_included_indexed_union.
Qed.

Lemma Sets_intersect_indexed_union_distr_l {I T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x (ys: I -> T),
    Sets.equiv
      (Sets.intersect x (Sets.indexed_union ys))
      (Sets.indexed_union (fun i => Sets.intersect x (ys i))).
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_indexed_union_included_strong1.
    intros.
    rewrite <- Sets_included_indexed_union.
    reflexivity.
  + apply Sets_indexed_union_included.
    intros.
    apply Sets_intersect_mono; [reflexivity |].
    apply Sets_included_indexed_union.
Qed.

Lemma Sets_complement_self_intersect {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x,
    Sets.equiv
      (Sets.intersect (Sets.complement x) x)
      Sets.empty.
Proof.
  intros.
  rewrite <- Sets_complement_fact.
  reflexivity.
Qed.

Lemma Sets_intersect_complement_self {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x,
    Sets.equiv
      (Sets.intersect x (Sets.complement x))
      Sets.empty.
Proof.
  intros.
  rewrite Sets_intersect_comm.
  apply Sets_complement_self_intersect.
Qed.

Lemma Sets_contrapositive_PP {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.included (Sets.complement y) (Sets.complement x).
Proof.
  intros.
  rewrite Sets_complement_fact.
  apply Sets_equiv_empty_fact.
  rewrite H.
  rewrite Sets_complement_self_intersect.
  reflexivity.
Qed.

Lemma Sets_contrapositive_PC {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included y (Sets.complement x) ->
    Sets.included x (Sets.complement y).
Proof.
  intros.
  apply Sets_complement_fact.
  apply Sets_complement_fact in H.
  rewrite Sets_intersect_comm.
  apply H.
Qed.

(** If SetsDomain_Classic will be used, then _[Sets_complement_complement]_ is available. *)
Lemma Sets_included_double_complement {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x,
    Sets.included x (Sets.complement (Sets.complement x)).
Proof.
  intros.
  apply Sets_contrapositive_PC.
  reflexivity.
Qed.

(** If SetsDomain_Classic will be used, then _[Sets_complement_intersect]_ is available. *)
Lemma Sets_included_complement_intersect {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included
      (Sets.union (Sets.complement x) (Sets.complement y))
      (Sets.complement (Sets.intersect x y)).
Proof.
  intros.
  apply Sets_union_included; apply Sets_contrapositive_PP.
  + apply Sets_intersect_included1.
  + apply Sets_intersect_included2.
Qed.

Lemma Sets_complement_union {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.equiv
      (Sets.complement (Sets.union x y))
      (Sets.intersect (Sets.complement x) (Sets.complement y)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split; intros.
  + apply Sets_included_intersect; apply Sets_contrapositive_PP.
    - apply Sets_included_union1.
    - apply Sets_included_union2.
  + rewrite Sets_complement_fact.
    rewrite Sets_intersect_union_distr_l.
    apply Sets_equiv_empty_fact.
    apply Sets_union_included.
    - apply Sets_equiv_empty_fact.
      rewrite <- Sets_complement_fact.
      apply Sets_intersect_included1.
    - apply Sets_equiv_empty_fact.
      rewrite <- Sets_complement_fact.
      apply Sets_intersect_included2.
Qed.

Lemma Sets_complement_empty {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  @Sets.equiv T _ (Sets.complement Sets.empty) Sets.full.
Proof.
  apply Sets_equiv_Sets_included; split; intros.
  + apply Sets_included_full.
  + apply Sets_complement_fact.
    apply Sets_equiv_empty_fact.
    apply Sets_intersect_included2.
Qed.

Lemma Sets_complement_full {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  @Sets.equiv T _ (Sets.complement Sets.full) Sets.empty.
Proof.
  rewrite <- (Sets_intersect_full_r (Sets.complement Sets.full)).
  apply Sets_complement_fact.
  reflexivity.
Qed.

#[export] Instance Sets_complement_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  Proper (Sets.included --> Sets.included) (@Sets.complement T _).
Proof.
  unfold Proper, respectful, Basics.flip.
  intros.
  apply Sets_contrapositive_PP.
  auto.
Qed.

#[export] Instance Sets_complement_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  Proper (Sets.equiv ==> Sets.equiv) (@Sets.complement T _).
Proof.
  unfold Proper, respectful, Basics.flip.
  intros.
  apply Sets_equiv_Sets_included in H.
  destruct H.
  apply Sets_equiv_Sets_included.
  split; apply Sets_complement_mono; auto.
Qed.

Lemma general_union_lift {A T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall (X: (A -> T) -> Prop) (a: A),
    Sets.equiv
      (Sets.general_union X a)
      (Sets.general_union (fun y => exists x, X x /\ x a = y)).
Proof.
  intros.
  unfold_SETS_in_goal_tac.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_exists_aux_left.
    intros x.
    apply Sets_Qaux_left_extract.
    intros.
    eapply Sets_derives_aux_trans.
    { apply Sets_Paux_left. }
    simpl.
    apply Sets_included_derives_aux.
    apply Sets_included_general_union.
    exists x.
    tauto.
  + apply Sets_general_union_included.
    intros y [x [? ?] ].
    subst y.
    apply (Sets_exists_aux_right _ x).
    apply Sets_conj_aux_right.
    { apply Sets_Qaux_right; tauto. }
    eapply Sets_derives_aux_trans; [| apply Sets_Paux_right].
    apply Sets_included_derives_aux.
    reflexivity.
Qed.

Lemma Sets_empty_general_union {T : Type} {_SETS : Sets.SETS T} {_SETS_Properties : SETS_Properties T} :
  Sets.equiv (Sets.general_union (fun _ : T => False)) Sets.empty.
Proof.
  apply Sets_equiv_empty_fact.
  apply Sets_general_union_included.
  intros.
  contradiction.
Qed.

(* TODO: remove this legacy name *)
Lemma Sets_union_empty {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union x Sets.empty) x.
Proof. apply Sets_union_empty_r. Qed.

(* TODO: remove this legacy name *)
Lemma Sets_empty_union {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union Sets.empty x) x.
Proof. apply Sets_union_empty_l. Qed.

Lemma Sets_intersect_empty {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.intersect x Sets.empty) Sets.empty.
Proof. apply Sets_intersect_empty_r. Qed.

Lemma Sets_empty_intersect {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.intersect Sets.empty x) Sets.empty.
Proof. apply Sets_intersect_empty_l. Qed.

Lemma Sets_intersect_full {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.intersect x Sets.full) x.
Proof. apply Sets_intersect_full_r. Qed.

Lemma Sets_full_intersect {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.intersect Sets.full x) x.
Proof. apply Sets_intersect_full_l. Qed.

(*
Lemma Sets_complement_complement {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x,
    Sets.equiv (Sets.complement (Sets.complement x)) x.
Proof.
  intros.
  unfold Sets.complement; unfold_SETS_in_goal_tac.
  intros.
  tauto.
Qed.
*)
Declare Scope sets_scope.
Delimit Scope sets_scope with sets.
Local Open Scope sets_scope.

Notation "[ ]":= Sets.empty (format "[ ]"): sets_scope.
Notation "∅":= Sets.empty (at level 5, no associativity): sets_scope.
Notation "[ x ]":= (Sets.singleton x) : sets_scope.
Notation "x ∩ y" := (Sets.intersect x y)(at level 13, left associativity): sets_scope.
Notation "x ∪ y" := (Sets.union x y)(at level 14, left associativity): sets_scope.
Notation "⋃ x" := (Sets.indexed_union x)(at level 10, no associativity): sets_scope.
Notation "⋂ x" := (Sets.indexed_intersect x)(at level 10, no associativity): sets_scope.
Notation "x == y" := (Sets.equiv x y) (at level 70, no associativity): sets_scope.
Notation "x ⊆ y" := (Sets.included x y) (at level 70, no associativity): sets_scope.
Notation "x ∈ y" := (SetsEle.In x y) (at level 70, no associativity): sets_scope.
Notation "⌜ x ⌝" := (Sets.prop_inj x) (at level 40, no associativity): sets_scope.

Tactic Notation "sets_unfold" :=
  unfold Sets.singleton;
  unfold_SETS_in_goal_tac;
  unfold_In_in_goal_tac.

Tactic Notation "sets_unfold" "in" constr(H) :=
  unfold Sets.singleton in H;
  unfold_SETS_in_hypo_tac H;
  unfold_In_in_hypo_tac H.

Tactic Notation "Sets_unfold" :=
  unfold Sets.singleton;
  unfold_SETS_add_In_in_goal_tac.

Tactic Notation "Sets_unfold" "in" constr(H) :=
  unfold Sets.singleton in H;
  unfold_SETS_add_In_in_hypo_tac H.

Tactic Notation "sets_unfold1" :=
  unfold1_SETS_in_goal_tac.

Tactic Notation "sets_unfold1" "in" constr(H) :=
  unfold1_SETS_in_hypo_tac H.

Tactic Notation "Sets_unfold1" :=
  unfold1_SETS_add_In_in_goal_tac.

Tactic Notation "Sets_unfold1" "in" constr(H) :=
  unfold1_SETS_add_In_in_hypo_tac H.

(*
Goal (fun x: nat => x + 1) = (fun x: nat => x + 1).
  match goal with
  | |- context [_ + _] => idtac
  end.
  
*)
