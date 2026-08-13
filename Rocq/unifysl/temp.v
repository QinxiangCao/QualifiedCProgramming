(* Class CategoryOperator : Type := {  *)
  (* object : Type;
  morphism : Type;
  domain : morphism -> object;
  codomain : morphism -> object;
  identity : object -> morphism;
  composite : morphism -> morphism -> morphism }.
Class CategoryProperty (C : CategoryOperator) : Type := { 
  dom_id : forall A, domain (identity A) = A;
  cod_id : forall A, codomain (identity A) = A;
  cp_id1 : forall f, composite f (identity (domain (f))) = f;
  cp_id2 : forall f, composite (identity (codomain(f))) f = f;
  dom_cp : forall f g, domain (composite g f) = domain f;
  cod_cp : forall f g, codomain (composite g f) = codomain g;
  assoc  : forall f g h, 
    composite h (composite g f) = composite (composite h g) f }. *)


Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.


Class CatOp : Type := {
  obj : Type; 
  mph : obj -> obj -> Type;
  dom {x y : obj} : mph x y -> obj;
  cod {x y : obj} : mph x y -> obj; 
  idt (x : obj) : mph x x;
  cps {x y z : obj} : mph y z -> mph x y -> mph x z }.

Class CatProp (C : CatOp) : Type := {
  dom_id : forall x, dom (idt x) = x;
  cod_id : forall x, cod (idt x) = x;  
  cp_id1 : forall x y (f : mph x y), cps f (idt x) = f;
  cp_id2 : forall x y (f : mph x y), cps (idt y) f = f;
  dom_cp : forall x y z (f : mph x y) (g : mph y z),
    dom (cps g f) = dom f;
  cod_cp : forall x y z (f : mph x y) (g : mph y z),
    cod (cps g f) = cod g;
  assoc : forall w x y z (f : mph w x) (g : mph x y) (h : mph y z),
    cps h (cps g f) = cps (cps h g) f }.

Instance Sets : CatOp := {
  obj := Set;
  mph := fun x y => x -> y;
  dom := fun x y f => x;
  cod := fun x y f => y;
  idt := fun x => (fun a : x => a);
  cps := fun x y z g f a => g (f a) }.

Instance SetsCat : CatProp Sets.


Class SetCategoryOperator : Type := {
  object : Type;
  morphism : object -> object -> Type;
  domain : forall {x y}, morphism x y -> object;
  codomain : forall {x y}, morphism x y -> object;
  identity : forall x, morphism x x;
  composite : forall {x y z}, morphism y z -> morphism x y -> morphism x z
}.

Class SetCategoryProperty (C : SetCategoryOperator) : Type := {
  dom_id : forall {x y} (f : morphism x y), domain f = x;
  cod_id : forall {x y} (f : morphism x y), codomain f = y;
  cp_id1 : forall {x y} (f : morphism x y), composite f (identity x) = f;
  cp_id2 : forall {x y} (f : morphism x y), composite (identity y) f = f;
  dom_cp : forall {x y z} (f : morphism x y) (g : morphism y z), domain (composite g f) = domain f;
  cod_cp : forall {x y z} (f : morphism x y) (g : morphism y z), codomain (composite g f) = codomain g;
  assoc : forall {w x y z} (f : morphism w x) (g : morphism x y) (h : morphism y z),
    composite h (composite g f) = composite (composite h g) f
}.

Instance SetCategory : SetCategoryOperator := {
  object := Type;
  morphism := fun x y => x -> y;
  domain := fun x y f => x;
  codomain := fun x y f => y;
  identity := fun x => (fun a : x => a);
  composite := fun x y z g f a => g (f a)
}.




Definition option_Unit : Unit (option worlds) := (fun m => m = None).

Definition option_UJR {J : Join worlds} {SA : @SeparationAlgebra worlds J}: @UnitJoinRelation (option worlds) option_Unit  (@option_Join J).
Proof.
  constructor; intros; hnf in *; subst.
  + destruct n; constructor.
  + inversion H0; tauto.
Qed.

Definition fun_Join (A B: Type) {J_B: Join B}: Join (A -> B) :=
  (fun a b c => forall x, join (a x) (b x) (c x)).

Definition fun_SA
           (A B: Type)
           {Join_B: Join B}
           {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A -> B) (fun_Join A B).

  Definition sum_Unit (A B : Type) : Unit (A + B) := (fun _ => False).

  Definition sum_UJR (A B : Type) {J_A : Join A} {J_B : Join B} : @UnitJoinRelation (A + B) (sum_Unit A B) (sum_Join A B).
  Proof.
    constructor; intros; hnf in *; tauto.
  Qed.

Definition prod_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (A * B) :=
    (fun a b c => join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c)).

Definition prod_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A * B) (prod_Join A B).