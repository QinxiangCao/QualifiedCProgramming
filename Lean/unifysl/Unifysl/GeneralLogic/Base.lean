import Unifysl.Lib.Coqlib
import Unifysl.Lib.Ensembles_ext

universe u v w z

namespace Unifysl

class Language : Type (u + 1) where
  expr : Type u

export Language (expr)

def context {L : Language.{u}} : Type u :=
  @Language.expr L -> Prop

def empty_context {L : Language.{u}} : context (L := L) :=
  Empty_set (@Language.expr L)

class Provable (L : Language.{u}) : Type (u + 1) where
  provable : @Language.expr L -> Prop

export Provable (provable)

class Derivable (L : Language.{u}) : Type (u + 1) where
  derivable : context (L := L) -> @Language.expr L -> Prop

export Derivable (derivable)

class Derivable1 (L : Language.{u}) : Type (u + 1) where
  derivable1 : @Language.expr L -> @Language.expr L -> Prop

export Derivable1 (derivable1)

class LogicEquiv (L : Language.{u}) : Type (u + 1) where
  logic_equiv : @Language.expr L -> @Language.expr L -> Prop

export LogicEquiv (logic_equiv)

class Model : Type (u + 1) where
  model : Type u

export Model (model)

class Semantics (L : Language.{u}) (MD : Model.{v}) :
    Type (max (u + 1) (v + 1)) where
  denotation : @Language.expr L -> @Model.model MD -> Prop

export Semantics (denotation)

def satisfies {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD] :
    @Model.model MD -> @Language.expr L -> Prop :=
  fun m x => SM.denotation x m

def ModelClass (MD : Model.{u}) : Type u :=
  @Model.model MD -> Prop

class KripkeModel (MD : Model.{u}) :
    Type (max (u + 1) (max (v + 1) (w + 1))) where
  Kmodel : Type v
  Kworlds : Kmodel -> Type w
  build_model : forall M : Kmodel, Kworlds M -> @Model.model MD

export KripkeModel (Kmodel Kworlds build_model)

def Kdenotation {L : Language.{u}} {MD : Model.{v}} [kMD : KripkeModel.{v, w, z} MD]
    (M : kMD.Kmodel) [SM : Semantics L MD] :
    @Language.expr L -> Ensemble (kMD.Kworlds M) :=
  fun x m => SM.denotation x (kMD.build_model M m)

def unit_MD : Model :=
  { model := Unit }

def unit_kMD (MD : Model.{u}) : KripkeModel MD :=
  { Kmodel := Unit
    Kworlds := fun _ => @Model.model MD
    build_model := fun _ m => m }

def AllModel (MD : Model.{u}) : ModelClass MD :=
  fun _ => True

inductive KripkeModelClass (MD : Model.{u}) [kMD : KripkeModel.{u, v, w} MD]
    (H : kMD.Kmodel -> Prop) : ModelClass MD where
  | Build_KripkeModelClass :
      forall (M : kMD.Kmodel) (m : kMD.Kworlds M),
        H M -> KripkeModelClass MD H (kMD.build_model M m)

export KripkeModelClass (Build_KripkeModelClass)

def consistent {L : Language.{u}} [Gamma : Derivable L] : context (L := L) -> Prop :=
  fun Phi =>
    exists x : @Language.expr L, ¬ Gamma.derivable Phi x

def satisfiable {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD] :
    ModelClass MD -> context (L := L) -> Prop :=
  fun MC Phi =>
    exists m : @Model.model MD, MC m /\ forall x : @Language.expr L, Phi x -> satisfies m x

def consequence {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD] :
    ModelClass MD -> context (L := L) -> @Language.expr L -> Prop :=
  fun MC Phi y =>
    forall m : @Model.model MD,
      MC m -> (forall x, Phi x -> satisfies m x) -> satisfies m y

def valid {L : Language.{u}} {MD : Model.{v}} [SM : Semantics L MD] :
    ModelClass MD -> @Language.expr L -> Prop :=
  fun MC x =>
    forall m : @Model.model MD, MC m -> satisfies m x

def provable_sound {L : Language.{u}} (Gamma : Provable L) {MD : Model.{v}}
    (SM : Semantics L MD) (MC : ModelClass MD) : Prop :=
  forall x : @Language.expr L, Gamma.provable x -> @valid L MD SM MC x

def derivable_sound {L : Language.{u}} (Gamma : Derivable L) {MD : Model.{v}}
    (SM : Semantics L MD) (MC : ModelClass MD) : Prop :=
  forall Phi x, Gamma.derivable Phi x -> @consequence L MD SM MC Phi x

def weakly_complete {L : Language.{u}} (Gamma : Provable L) {MD : Model.{v}}
    (SM : Semantics L MD) (MC : ModelClass MD) : Prop :=
  forall x : @Language.expr L, @valid L MD SM MC x -> Gamma.provable x

def strongly_complete {L : Language.{u}} (Gamma : Derivable L) {MD : Model.{v}}
    (SM : Semantics L MD) (MC : ModelClass MD) : Prop :=
  forall (Phi : context (L := L)) (x : @Language.expr L),
    @consequence L MD SM MC Phi x -> Gamma.derivable Phi x

scoped notation:70 m " |= " x => satisfies m x
scoped notation:71 "|-- " x => Provable.provable x
scoped notation:70 Phi " |--- " x => Derivable.derivable Phi x
scoped notation:69 Phi " ;; " x => Union _ Phi (Singleton _ x)
scoped infix:71 " --||-- " => LogicEquiv.logic_equiv
scoped infix:70 " |-- " => Derivable1.derivable1

namespace KripkeModelFamilyNotation

scoped notation:59 "KRIPKE: " M ", " m => KripkeModel.build_model M m

end KripkeModelFamilyNotation

namespace KripkeModelSingleNotation

scoped notation:59 "KRIPKE: " m =>
  @KripkeModel.build_model _ (unit_kMD _) Unit.unit m

end KripkeModelSingleNotation

namespace KripkeModelClass

def kripke_model_class_join {MD : Model.{u}} [kMD : KripkeModel.{u, v, w} MD]
    (X Y : kMD.Kmodel -> Prop) : kMD.Kmodel -> Prop :=
  fun M => X M /\ Y M

scoped infix:65 " + " => kripke_model_class_join

end KripkeModelClass

end Unifysl
