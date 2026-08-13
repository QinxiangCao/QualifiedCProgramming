Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Export naive_C_Rules.
Local Open Scope sac.

Inductive unop : Type :=
  | T_not
  | T_uminus.

Inductive binop : Type :=
  | T_plus 
  | T_minus
  | T_mul
  | T_div 
  | T_mod
  | T_lt
  | T_le 
  | T_ge
  | T_gt
  | T_eq
  | T_ne
  | T_and
  | T_or.

Inductive expr : Type :=
  | EConst : Z -> expr 
  | EVar : Z -> expr 
  | EUnop : unop -> expr -> expr
  | EBinop : binop -> expr -> expr -> expr.

Fixpoint expr_eval(e: expr)(vals: list Z) : Z :=
  match e with
  | EConst v => v
  | EVar name => Znth name vals 0
  | EUnop op e' =>
      let v' := expr_eval e' vals in
        match op with 
        | T_not => if Z.eqb v' 0 then 1 else 0
        | T_uminus => -v'
        end
  | EBinop op e1 e2 =>
      let v1 := expr_eval e1 vals in
      let v2 := expr_eval e2 vals in
      match op with
      | T_plus => v1 + v2
      | T_minus => v1 - v2
      | T_mul => v1 * v2
      | T_div => v1 ÷ v2
      | T_mod => v1 % (v2)
      | T_lt => if (v1 <? v2)%Z then 1 else 0
      | T_le => if (v1 <=? v2)%Z then 1 else 0
      | T_ge => if (v1 >=? v2)%Z then 1 else 0
      | T_gt => if (v1 >? v2)%Z then 1 else 0
      | T_eq => if (v1 =? v2)%Z then 1 else 0
      | T_ne => if (v1 =? v2)%Z then 0 else 1
      | T_and => if (v1 =? 0)%Z then 0 else (if (v2 =? 0)%Z then 0 else 1)
      | T_or => if (v1 =? 0)%Z then (if (v2 =? 0)%Z then 0 else 1) else 1
      end
  end.

Definition un_safe_cond(op: unop)(v: Z) : Prop :=
  match op with
  | T_not => True
  | T_uminus => v <> INT_MIN
  end.

Definition bin_safe_cond(op: binop)(v1 v2: Z) : Prop :=
  match op with
  | T_plus => INT_MIN <= v1 + v2 <= INT_MAX
  | T_minus => INT_MIN <= v1 - v2 <= INT_MAX
  | T_mul => INT_MIN <= v1 * v2 <= INT_MAX
  | T_div => v2 <> 0 /\ (v1 <> INT_MIN \/ v2 <> -1)
  | T_mod => v2 <> 0 /\ (v1 <> INT_MIN \/ v2 <> -1)
  | T_lt => True
  | T_le => True
  | T_ge => True 
  | T_gt => True 
  | T_eq => True 
  | T_ne => True 
  | T_and => True
  | T_or => True
  end.

Inductive safe_eval: expr -> list Z -> Prop :=
  | safe_eval_const: forall i vs, INT_MIN <= i /\ i <= INT_MAX -> safe_eval (EConst i) vs
  | safe_eval_var:
      forall name vs, 
        0 <= name < Z.of_nat (List.length vs) ->
          INT_MIN <= Znth name vs 0 <= INT_MAX -> 
            safe_eval (EVar name) vs
  | safe_eval_un:
      forall op e vs,
        safe_eval e vs -> un_safe_cond op (expr_eval e vs) -> 
          safe_eval (EUnop op e) vs
  | safe_eval_bin: 
      forall op e1 e2 vs, 
        safe_eval e1 vs -> safe_eval e2 vs -> 
          bin_safe_cond op (expr_eval e1 vs) (expr_eval e2 vs) -> 
            safe_eval (EBinop op e1 e2) vs.

Definition UnOpID(op: unop) : Z :=
  match op with
  | T_uminus => 0
  | T_not => 1
  end.

Definition BinOpID(op: binop) : Z :=
  match op with
  | T_plus => 0
  | T_minus => 1
  | T_mul => 2
  | T_div => 3
  | T_mod => 4
  | T_lt => 5
  | T_gt => 6
  | T_le => 7
  | T_ge => 8
  | T_eq => 9
  | T_ne => 10
  | T_and => 11
  | T_or => 12 
  end.

Fixpoint store_expr(p: addr)(e: expr) : Assertion :=
  match e with
  | EConst v =>
      (&((p) # "expr" ->ₛ "t") # Int  |-> 0) ** 
      (&((p) # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value") # Int |-> v)
  | EVar name =>
      (&((p) # "expr" ->ₛ "t") # Int  |-> 1) ** 
      (&((p) # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> name)
  | EBinop op e1 e2 =>
      EX p1 p2,
      (&((p) # "expr" ->ₛ "t") # Int  |-> 2) ** 
      (&((p) # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op") # Int |-> BinOpID op) **
      (&((p) # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left") # Ptr |-> p1) **
      (&((p) # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right") # Ptr |-> p2) **
      store_expr p1 e1 ** store_expr p2 e2
  | EUnop op e' =>
      EX p', 
      (&((p) # "expr" ->ₛ "t") # Int  |-> 3) ** 
      (&((p) # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op") # Int |-> UnOpID op) **
      (&((p) # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg") # Ptr |-> p') **
      store_expr p' e'
  end.

Definition store_expr_aux(p: addr)(t: Z)(e: expr) : Assertion :=
  match e with
  | EConst v =>
      “ t = 0 ” &&
      (&((p) # "expr" ->ₛ "d" .ₛ "CONST" .ₛ "value") # Int |-> v)
  | EVar name =>
      “ t = 1 ” &&
      (&((p) # "expr" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> name)
  | EBinop op e1 e2 =>
      EX p1 p2,
      “ t = 2 ” &&
      (&((p) # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "op") # Int |-> BinOpID op) **
      (&((p) # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "left") # Ptr |-> p1) **
      (&((p) # "expr" ->ₛ "d" .ₛ "BINOP" .ₛ "right") # Ptr |-> p2) **
      store_expr p1 e1 ** store_expr p2 e2
  | EUnop op e' =>
      EX p', 
      “ t = 3 ” &&
      (&((p) # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "op") # Int |-> UnOpID op) **
      (&((p) # "expr" ->ₛ "d" .ₛ "UNOP" .ₛ "arg") # Ptr |-> p') **
      store_expr p' e'
  end.

Ltac get_bin_op_from_id op :=
  match goal with
  | H: ?id = BinOpID ?op |- _ => destruct op; try discriminate; try tauto
  end.

Ltac get_un_op_from_id op :=
  match goal with
  | H: ?id = UnOpID ?op |- _ => destruct op; try discriminate; try tauto
  end.  
