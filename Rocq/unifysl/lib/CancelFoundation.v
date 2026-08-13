Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.

Section StructOfCancel.
Context {Texpr : Type}
        {f1 : Texpr -> Texpr -> Texpr}
        {f2 : Texpr -> Texpr -> Texpr}
        {e : Texpr}.


Inductive expr_deep : Type :=
  | impp_deep : expr_deep -> expr_deep -> expr_deep
  | sepcon_deep : expr_deep -> expr_deep -> expr_deep
  | emp_deep : expr_deep
  | varp_deep : nat -> expr_deep.

Fixpoint beq e1 e2 :=
  match e1, e2 with
  | emp_deep, emp_deep => true
  | varp_deep x, varp_deep y => Nat.eqb x y
  | sepcon_deep p11 p12, sepcon_deep p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | impp_deep p11 p12, impp_deep p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | _, _ => false
  end.

Inductive tree_pos : Type :=
  | var_pos : Texpr -> option positive -> tree_pos
  | sepcon_pos : tree_pos -> tree_pos -> tree_pos.

Fixpoint cancel_mark_context dep q tep key : tree_pos * bool:=
  match dep, tep with
  | sepcon_deep dp dq, sepcon_pos tp tq =>
    match cancel_mark_context dp q tp key with
    | (tp', true) => ((sepcon_pos tp' tq), true)
    | (tp', false) =>
      match cancel_mark_context dq q tq key with
      | (tq', true) => ((sepcon_pos tp tq'), true)
      | (tq', false) => (tep, false)
      end
    end
  | p, (var_pos sp o) =>
    match (beq p q) with
    | true =>
      match o with
      | None => ((var_pos sp (Some key)), true)
      | _ => (tep, false)
      end
    | false => (tep, false)
    end
  | _, _ => (tep, false)
  end.

Fixpoint cancel_mark' dep deq tep teq key : tree_pos * tree_pos * positive :=
  match deq, teq with
  | sepcon_deep dp dq, sepcon_pos tp tq =>
    match (cancel_mark' dep dp tep tp key) with
    | (tep', tp', key') =>
      match (cancel_mark' dep dq tep' tq key') with
      | (tep'', tq', key'') => (tep'', sepcon_pos tp' tq', key'')
      end
    end
  | q, (var_pos sq o) =>
    match (cancel_mark_context dep q tep key) with
    | (tep', true) => (tep', (var_pos sq (Some key)), Pos.succ key)
    | (tep', false) => (tep', var_pos sq None, key)
    end
  | _, _ => (tep, teq, key)
  end.

Definition cancel_mark dep deq tep teq : tree_pos * tree_pos :=
  match (cancel_mark' dep deq tep teq xH) with
  | (tep', teq', key') => (tep', teq')
  end.

Fixpoint unmark_sort' tep : option Texpr :=
  match tep with
  | sepcon_pos tp tq =>
    match unmark_sort' tp with
    | None => unmark_sort' tq
    | Some sp =>
      match unmark_sort' tq with
      | None => Some sp
      | Some sq => Some (f1 sp sq)
      end
    end
  | var_pos sq o =>
    match o with
    | None => Some sq
    | _ => None
    end
  end.
Definition unmark_sort tep : Texpr :=
  match unmark_sort' tep with
  | Some sp => sp
  | None => e
  end.

Definition cancel_different tep teq : Texpr :=
  f2 (unmark_sort tep) (unmark_sort teq).

Fixpoint mark_sort' tep m : PTree.tree Texpr :=
  match tep with
  | sepcon_pos tp tq =>
    match mark_sort' tp m with
    | m' => mark_sort' tq m'
    end
  | var_pos sq o =>
    match o with
    | None => m
    | Some pos =>
      match PTree.get_rec Texpr pos m with
      | None => PTree.set_rec Texpr pos sq m
      | Some sp => PTree.set_rec Texpr pos (f1 sp sq) m
      end
    end
  end.
Definition mark_sort tep : PTree.tree Texpr :=
  mark_sort' tep PTree.empty.

Definition cancel_same tep teq : Prop :=
  mark_sort tep = mark_sort teq.

Fixpoint restore' tep : Texpr :=
  match tep with
  | sepcon_pos tp tq => f1 (restore' tp) (restore' tq)
  | var_pos sp o => sp
  end.
Definition restore tep teq : Texpr :=
  f2 (restore' tep ) (restore' teq ).

End StructOfCancel.