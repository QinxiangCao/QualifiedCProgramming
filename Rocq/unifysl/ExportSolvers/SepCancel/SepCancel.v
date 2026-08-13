Require Export Coq.Lists.List.
Require Export Coq.Numbers.BinNums.
Require Export Coq.PArith.BinPosDef.

Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses.
Require Import export_lib.
Import EXPO.
Import EXPO_TRANSPARENTS.
Local Open Scope expo_transparent_scope.
Local Declare Scope syntax.
Local Open Scope syntax.

Module SepCancelNotation.
Notation "|--  x" := ((provable) x) (only parsing, at level 71, no associativity) : syntax.
Notation "x --> y" := ((impp) x y) (only parsing, at level 55, right associativity) : syntax.
(*
  NOTE: (sepcon) (emp) can not refer to sepcon or emp
        in export_lib correctly.
*)
End SepCancelNotation.
Import SepCancelNotation.

Existing Instances logic_equiv_impp_proper
                   logic_equiv_sepcon_proper
                   provable_proper_equiv
                   logic_equiv_refl_instance.

Ltac unfold3_tac x :=
    eval cbv beta delta [
       EXPO.expr
       EXPO.sepcon
       EXPO.emp
    ] in x.

Ltac length_cont ls k :=
  match ls with
  | nil => k O
  | _ :: ?ls' => length_cont ls' ltac:(fun n => k (S n))
  end.
Ltac length ls := length_cont ls ltac:(fun l => l).

Ltac pred n :=
  match n with
  | O => O
  | S ?m => m
  end.

Ltac search_expr' n i l l0 :=
  match l with
  | nil => let len := length l0 in constr:((S len, n :: l0))
  | n :: ?t => constr:((i, l0))
  | _ :: ?t => let pi := pred i in search_expr' n pi t l0
  end.
Ltac search_expr n l := let len := length l in search_expr' n len l l.

Ltac shallowTodeep' se l0 :=
  let _sepcon := (unfold3_tac constr:(EXPO.sepcon)) in
  let _emp := (unfold3_tac constr:(EXPO.emp)) in
(*
  NOTE: using 'let _sepcon := (unfold3_tac EXPO.sepcon) in'
        will make implicit arguments explicit, name term.
*)
  match se with
  | _sepcon ?sp ?sq =>
    match shallowTodeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowTodeep' sq l1 with
      | (?dq, ?l2) => constr:((sepcon_deep dp dq, l2))
      end
    end
  | ?sp --> ?sq =>
    match shallowTodeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowTodeep' sq l1 with
      | (?dq, ?l2) => constr:((impp_deep dp dq, l2))
      end
    end
  | _emp => constr:((emp_deep, l0))
  | ?sp => match search_expr sp l0 with
          | (?i, ?l1) => constr:((varp_deep i, l1))
          end
  end.

Ltac shallowTodeep se :=
  match shallowTodeep' se (@nil (expr)) with
  | (?de, ?tbl) =>
    match de with
    | impp_deep ?dep ?deq => constr:((dep, deq, tbl))
    end
  end.

Ltac shallowTotree_odd se :=
  let _sepcon := (unfold3_tac constr:(EXPO.sepcon)) in
  match se with
  | _sepcon ?sp ?sq =>
    match shallowTotree_odd sp with
    | ?tp =>
      match shallowTotree_odd sq with
      | ?tq => constr:(sepcon_pos tp tq)
      end
    end
  | ?sp => constr:(var_pos sp None)
  end.

Ltac shallowTotree se :=
  match se with
  | ?sep --> ?seq =>
    match shallowTotree_odd sep with
    | ?tep =>
      match shallowTotree_odd seq with
      | ?teq => constr:((tep, teq))
      end
    end
  end.

Ltac same_handle :=
  cbv beta delta [cancel_same];
  reflexivity.

Ltac different_handle :=
  let _sepcon := (unfold3_tac constr:(EXPO.sepcon)) in
  let _emp := (unfold3_tac constr:(EXPO.emp)) in
  cbv beta delta
    [ cancel_different
      ___LogicTheorem___.cancel_different
      TheoryOfCancel.cancel_different
      TheoryOfCancel.unmark_sort
    ];
  repeat unfold TheoryOfCancel.unmark_sort';
  change Syntax.impp with impp;
  change Syntax.sepcon with _sepcon;
  change Syntax.emp with _emp;
  try apply (provable_impp_refl _emp).

Ltac sep_cancel' se :=
  match shallowTodeep se with
    | (?dep, ?deq, ?tbl) =>
    match shallowTotree se with
    | (?tep, ?teq) =>
    let te' := eval compute in (cancel_mark dep deq tep teq) in
    let tep' := eval compute in (fst te') in
    let teq' := eval compute in (snd te') in
    apply (cancel_sound tep' teq');
    [ same_handle
    | different_handle]
    end
  end.

Ltac sep_cancel :=
    match goal with
    | [|- |-- ?se] => sep_cancel' se
    end.