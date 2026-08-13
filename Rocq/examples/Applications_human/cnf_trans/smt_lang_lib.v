Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

From SimpleC.EE.Applications_human Require Import super_poly_sll2.

(* Module smt_lang_enums1. *)

Unset Automatic Proposition Inductives.

Inductive SmtPropBop : Type :=
  | SMTPROP_AND: SmtPropBop
  | SMTPROP_OR: SmtPropBop
  | SMTPROP_IMPLY: SmtPropBop
  | SMTPROP_IFF: SmtPropBop.

Inductive SmtPropUop : Type :=
  | SMTPROP_NOT: SmtPropUop.

Inductive SmtPropType : Type :=
  | SMTB_PROP: SmtPropType
  | SMTU_PROP: SmtPropType
  | SMT_PROPVAR: SmtPropType.

Definition SmtPBID (t: SmtPropBop) : Z :=
  match t with
    | SMTPROP_AND => 0%Z
    | SMTPROP_OR => 1%Z
    | SMTPROP_IMPLY => 2%Z
    | SMTPROP_IFF => 3%Z
  end.

Definition SmtPUID (t: SmtPropUop) : Z :=
  match t with
    | SMTPROP_NOT => 4%Z
  end.

(* End smt_lang_enums1. *)

(* Import smt_lang_enums1. *)

Inductive smt_prop : Type :=
  | SmtB (op: SmtPropBop) (lt: smt_prop) (rt: smt_prop): smt_prop
  | SmtU (op: SmtPropUop) (prop: smt_prop): smt_prop
  | SmtV (var: Z): smt_prop.

Notation "'SmtProplist'" := (list smt_prop) (at level 0, only parsing).

Definition SmtPTID (t: smt_prop) : Z :=
  match t with
    | SmtB _ _ _ => 5%Z
    | SmtU _ _ => 6%Z
    | SmtV _ => 7%Z
  end.

Fixpoint store_SmtProp (x: addr) (s: smt_prop) : Assertion :=
  “ x <> NULL ” && &(x # "SmtProp" ->ₛ "type") # Int |-> SmtPTID s **
  match s with
    | SmtB op lt rt => EX y z: addr,
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op") # Int |-> SmtPBID op **
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1") # Ptr |-> y **
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2") # Ptr |-> z **
                        store_SmtProp y lt **
                        store_SmtProp z rt
    | SmtU op prop => EX y: addr,
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op") # Int |-> SmtPUID op **
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1") # Ptr |-> y **
                        store_SmtProp y prop
    | SmtV var => “ var <> 0 ” &&
                  &(x # "SmtProp" ->ₛ "prop" .ₛ "Propvar") # Int |-> var
  end.


Definition store_SmtProp' (x: addr) (s: smt_prop) : Assertion :=
  match s with
    | SmtB op lt rt => “ x <> NULL ” &&
                       EX y z: addr,
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op") # Int |-> SmtPBID op **
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1") # Ptr |-> y **
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2") # Ptr |-> z **
                        store_SmtProp y lt **
                        store_SmtProp z rt
    | SmtU op prop => “ x <> NULL ” &&
                      EX y: addr,
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op") # Int |-> SmtPUID op **
                        &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1") # Ptr |-> y **
                        store_SmtProp y prop
    | SmtV var => “ x <> NULL ” && “ var <> 0 ” &&
                  &(x # "SmtProp" ->ₛ "prop" .ₛ "Propvar") # Int |-> var
  end.

Lemma store_SmtProp_unfold: forall x s,
  store_SmtProp x s |--
  &(x # "SmtProp" ->ₛ "type") # Int |-> SmtPTID s **
  store_SmtProp' x s.
Proof.
  intros.
  unfold store_SmtProp, store_SmtProp'.
  destruct s; fold store_SmtProp; entailer!.
Qed.

Lemma store_SmtProp_fold: forall x s,
  &(x # "SmtProp" ->ₛ "type") # Int |-> SmtPTID s **
  store_SmtProp' x s |--
  store_SmtProp x s.
Proof.
  intros.
  unfold store_SmtProp, store_SmtProp'.
  destruct s; fold store_SmtProp; entailer!.
Qed.

Lemma store_SmtProp'_Binary: forall x s,
  SmtPTID s = 5%Z ->
  store_SmtProp' x s |--
  EX op lt rt, “ s = SmtB op lt rt ” && “ x <> NULL ” &&
  EX y z: addr,
    &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "op") # Int |-> SmtPBID op **
    &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop1") # Ptr |-> y **
    &(x # "SmtProp" ->ₛ "prop" .ₛ "Binary_prop" .ₛ "prop2") # Ptr |-> z **
    store_SmtProp y lt **
    store_SmtProp z rt.
Proof.
  intros.
  destruct s; try discriminate H.
  Exists op s1 s2.
  simpl.
  Intros y z.
  Exists y z.
  entailer!.
Qed.

Lemma store_SmtProp'_Unary: forall x s,
  SmtPTID s = 6%Z ->
  store_SmtProp' x s |--
  EX op prop, “ s = SmtU op prop ” && “ x <> NULL ” &&
  EX y: addr,
    &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "op") # Int |-> SmtPUID op **
    &(x # "SmtProp" ->ₛ "prop" .ₛ "Unary_prop" .ₛ "prop1") # Ptr |-> y **
    store_SmtProp y prop.
Proof.
  intros.
  destruct s; try discriminate H.
  Exists op s.
  simpl.
  Intros y.
  Exists y.
  entailer!.
Qed.

Lemma store_SmtProp'_Var: forall x s,
  SmtPTID s = 7%Z ->
  store_SmtProp' x s |--
  EX v, “ s = SmtV v ” && “ x <> NULL ” && “ v <> 0 ” &&
    &(x # "SmtProp" ->ₛ "prop" .ₛ "Propvar") # Int |-> v.
Proof.
  intros.
  destruct s; try discriminate H.
  Exists var.
  simpl.
  entailer!.
Qed.

Definition store_SmtProp_cell (x: addr) (s: smt_prop): Assertion :=
  “ x <> NULL ” &&
  EX y: addr,
   &(x # "SmtProplist" ->ₛ "prop") # Ptr |-> y **
   store_SmtProp y s.

(* Definition link_SmtProp_cell (x y: addr): Assertion :=
  “ x <> NULL ” &&
  &(x # "SmtProplist" ->ₛ "next") # Ptr |-> y. *)

(* Module smt_lang_store_lists2. *)

Definition sll_SmtProplist (x: addr) (l: SmtProplist): Assertion :=
  sll store_SmtProp_cell "SmtProplist" "next" x l.

Definition sllseg_SmtProplist (x: addr) (y: addr) (l: SmtProplist): Assertion :=
  sllseg store_SmtProp_cell "SmtProplist" "next" x y l.

Definition sllbseg_SmtProplist (x: addr) (y: addr) (l: SmtProplist): Assertion :=
  sllbseg store_SmtProp_cell "SmtProplist" "next" x y l.
  
(* End smt_lang_store_lists2. *)

(* Import smt_lang_store_lists2. *)

Fixpoint SmtProp_size (s: smt_prop) : Z :=
  match s with
    | SmtB _ lt rt => 1 + SmtProp_size lt + SmtProp_size rt
    | SmtU _ prop => 1 + SmtProp_size prop
    | SmtV _ => 1
  end.

Opaque Z.add Z.sub Z.mul Z.opp Z.of_nat Z.of_N Z.succ.

Lemma SmtProp_size_nonneg: forall s, 0 <= SmtProp_size s.
Proof.
  induction s as [b lt IHlt rt IHrt | u prop IH | v].
  - simpl SmtProp_size.
    lia. (* 1 + IHlt + IHrt >= 0 *)
  - simpl. (* SmtU *)
    lia.
  - simpl. lia. (* SmtV *)
Qed.
  