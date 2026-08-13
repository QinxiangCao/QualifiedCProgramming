Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
Require Import MonadLib.MonadErr.StateRelMonadErr.

Import ListNotations.
Export MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.

(** ====================================================================== *)
(** 1. Definitions                                                         *)
(** ====================================================================== *)

(** Basic mathematical objects and semantic predicates. *)

Record Constraint: Type := {
  const: Z;
  coef: list Z;
}.

Definition LP: Type := list Constraint.

Definition LP_sol: Type := list Z.

Fixpoint sum_prod (s: Z) (a b: list Z): Z :=
  match a, b with
  | nil, _ => s
  | _, nil => s
  | cons a0 a', cons b0 b' => sum_prod (s + a0 * b0) a' b'
  end.

Definition assignment (s: LP_sol) (c: Constraint): Z :=
  sum_prod c.(const) s c.(coef).

Definition satisfy_constraint (s: LP_sol) (c: Constraint): Prop :=
  assignment s c <= 0.

Definition satisfy_LP (s: LP_sol) (p: LP): Prop :=
  forall c, In c p -> satisfy_constraint s c.

Definition UNSAT (p : LP) : Prop :=
  forall s, ~ satisfy_LP s p.

Definition LP_implies (p1 p2: LP): Prop :=
  forall s: LP_sol, satisfy_LP s p1 -> satisfy_LP s p2.

Definition nth_coef (n: Z) (c: Constraint): Z :=
  nth (Z.to_nat (n - 1)) c.(coef) 0.

Record BP: Type := {
  upper: LP;
  lower: LP;
  remain: LP;
}.

Record eliminate_xn (num: Z) (lp: LP) (bp: BP): Prop := {
  elim_upper:
    forall c, In c bp.(upper) <-> In c lp /\ nth_coef num c > 0;
  elim_lower:
    forall c, In c bp.(lower) <-> In c lp /\ nth_coef num c < 0;
  elim_remain:
    forall c, In c bp.(remain) <-> In c lp /\ nth_coef num c = 0;
}.

Fixpoint list_add (l1 l2 : list Z): list Z :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | a :: l1', b :: l2' => (a + b) :: list_add l1' l2'
  end.

Definition mul_list (k: Z) (l: list Z): list Z :=
  map (fun i => k * i) l.

Definition generate_new_constraint (n: Z) (c1 c2 c: Constraint): Prop :=
  exists m1 m2,
    m1 > 0 /\ m2 > 0 /\ nth_coef n c = 0 /\
    c = {|
      const := m1 * c1.(const) + m2 * c2.(const);
      coef := list_add (mul_list m1 c1.(coef)) (mul_list m2 c2.(coef));
    |}.

Definition generate_new_constraints (n: Z) (lp1 lp2 lp: LP): Prop :=
  forall c,
    In c lp ->
    exists c1 c2,
      In c1 lp1 /\ In c2 lp2 /\
      generate_new_constraint n c1 c2 c.

Definition Constraint_list (c: Constraint): list Z :=
  c.(const) :: c.(coef).

Definition list_Constraint (l: list Z): Constraint :=
  match l with
  | nil => {| const := 0; coef := nil |}
  | l0 :: l' => {| const := l0; coef := l' |}
  end.

Definition coef_Znth (i: Z) (c: Constraint) (default: Z): Z :=
  Znth i (Constraint_list c) default.

Definition coef_Zlength (c: Constraint): Z :=
  Z.of_nat (Datatypes.length (Constraint_list c)).

Definition InequList_Zeros (l : list Constraint) (lo hi : Z) : Prop :=
  forall c, In c l -> forall i, (lo <= i /\ i < hi) -> coef_Znth i c 0 = 0.

Definition NonPos (l : list Constraint) : Prop :=
  forall c, In c l -> coef_Znth 0 c 0 <= 0.

Definition HasPositiveConst (l: list Constraint): Prop :=
  exists c, In c l /\ coef_Znth 0 c 0 > 0.

Definition coef_replace_Znth (i v: Z) (c: Constraint): Constraint :=
  list_Constraint (replace_Znth i v (Constraint_list c)).

Definition generate_new_constraint_partial
  (n: Z) (m m1 m2: Z) (c1 c2 c: Constraint): Prop :=
  m1 > 0 /\ m2 > 0 /\
  m1 * coef_Znth n c1 0 + m2 * coef_Znth n c2 0 = 0 /\
  (forall i,
      0 <= i /\ i < m ->
      coef_Znth i c 0 =
        m1 * coef_Znth i c1 0 + m2 * coef_Znth i c2 0).

Definition generate_new_constraints_partial
  (n: Z) (lp11: LP) (x: Constraint) (lp21 lp22 lp: LP): Prop :=
  exists res1 res2,
    (forall c, In c lp <-> In c res1 \/ In c res2) /\
    generate_new_constraints n lp11 (lp21 ++ lp22) res1 /\
    (forall c2,
       In c2 res2 ->
       exists c1,
         In c1 lp21 /\ generate_new_constraint n x c1 c2).

Definition empty_bp : BP :=
  {| upper := nil;
     lower := nil;
     remain := nil |}.

Definition add_upper (c: Constraint) (bp: BP): BP :=
  {| upper := c :: bp.(upper);
     lower := bp.(lower);
     remain := bp.(remain) |}.

Definition add_lower (c: Constraint) (bp: BP): BP :=
  {| upper := bp.(upper);
     lower := c :: bp.(lower);
     remain := bp.(remain) |}.

Definition add_remain (c: Constraint) (bp: BP): BP :=
  {| upper := bp.(upper);
     lower := bp.(lower);
     remain := c :: bp.(remain) |}.

(** ====================================================================== *)
(** 2. Abstract Programs                                                    *)
(** ====================================================================== *)

(** 2.1. Eliminating one variable from a constraint list. *)

Definition eliminate_body (num: Z) (c: Constraint) (bp: BP):
  program unit BP :=
  choice
    (assume!! (nth_coef num c > 0);;
     return (add_upper c bp))
    (choice
      (assume!! (nth_coef num c < 0);;
       return (add_lower c bp))
      (assume!! (nth_coef num c = 0);;
       return (add_remain c bp))).

Definition eliminate_from (num: Z) (todo: LP) (bp: BP):
  program unit BP :=
  list_iter (eliminate_body num) todo bp.

Definition eliminate_prog (num: Z) (lp: LP):
  program unit BP :=
  eliminate_from num lp empty_bp.

(** 2.2. Generating constraints. *)

Definition generate_new_constr_body
  (m1 m2: Z) (c1 c2: Constraint) (_x: Z) (st: Z * list Z):
  program unit (Z * list Z) :=
  let '(i, prefix) := st in
  return
    (i + 1,
     prefix ++
       [m1 * coef_Znth i c1 0 +
        m2 * coef_Znth i c2 0]).

Definition generate_new_constr_from
  (m1 m2: Z) (c1 c2: Constraint) (i: Z) (prefix: list Z):
  program unit Constraint :=
  '(_, prefix') <-
    list_iter
      (generate_new_constr_body m1 m2 c1 c2)
      (skipn (Z.to_nat i) (Constraint_list c1))
      (i, prefix);;
  return (list_Constraint prefix').

Definition generate_new_constr_prog
  (cur_num: Z) (c1 c2: Constraint):
  program unit Constraint :=
  an <- return (coef_Znth cur_num c1 0);;
  bn <- return (- coef_Znth cur_num c2 0);;
  assert (an > 0);;
  assert (bn > 0);;
  g <- return (Z.gcd an bn);;
  m1 <- return (bn / g);;
  m2 <- return (an / g);;
  generate_new_constr_from m1 m2 c1 c2 0 nil.

Definition generate_new_constraints_inner_body
  (cur_num: Z) (c1 c2: Constraint) (acc: LP):
  program unit LP :=
  c3 <- generate_new_constr_prog cur_num c1 c2;;
  return (c3 :: acc).

Fixpoint generate_new_constraints_inner_loop
  (cur_num: Z) (c1: Constraint) (lp2 acc: LP):
  program unit LP :=
  match lp2 with
  | nil => return acc
  | c2 :: lp2' =>
      acc' <- generate_new_constraints_inner_body cur_num c1 c2 acc;;
      generate_new_constraints_inner_loop cur_num c1 lp2' acc'
  end.

Fixpoint generate_new_constraint_list_loop
  (cur_num: Z) (lp1 lp2 acc: LP):
  program unit LP :=
  match lp1 with
  | nil => return acc
  | c1 :: lp1' =>
      acc' <- generate_new_constraints_inner_loop cur_num c1 lp2 acc;;
      generate_new_constraint_list_loop cur_num lp1' lp2 acc'
  end.

Definition generate_new_constraints_after_one
  (cur_num: Z) (c1: Constraint) (lp2 acc lp1_tail full_lp2: LP)
  (c3: Constraint): program unit LP :=
  bind
    (generate_new_constraints_inner_loop cur_num c1 lp2 (c3 :: acc))
    (generate_new_constraint_list_loop cur_num lp1_tail full_lp2).

Definition generate_new_constraint_list_prog
  (cur_num: Z) (lp1 lp2 init: LP):
  program unit LP :=
  generate_new_constraint_list_loop cur_num lp1 lp2 init.

(** 2.3. Real shadow loop. *)

Definition real_shadow_step_prog (cnt: Z) (lp: LP):
  program unit LP :=
  bp <- eliminate_prog cnt lp;;
  generate_new_constraint_list_prog cnt bp.(upper) bp.(lower) bp.(remain).

Definition real_shadow_body_prog (st: Z * LP):
  program unit (Z * LP) :=
  let '(cnt, lp) := st in
  lp' <- real_shadow_step_prog cnt lp;;
  return (cnt - 1, lp').

Definition real_shadow_loop_body (st: Z * LP):
  program unit (CntOrBrk (Z * LP) LP) :=
  let '(cnt, _) := st in
  choice
    (assume!! (1 <= cnt);;
     st' <- real_shadow_body_prog st;;
     continue st')
    (assume!! (cnt < 1);;
     break (snd st)).

Definition real_shadow_loop_prog (cnt: Z) (lp: LP):
  program unit LP :=
  repeat_break real_shadow_loop_body (cnt, lp).

Definition real_shadow_prog (n: Z) (lp: LP):
  program unit LP :=
  real_shadow_loop_prog n lp.

(** 2.4. Final contradiction check and LIA deduction. *)

Definition lia_deduction_check_body (c: Constraint) (found: bool):
  program unit bool :=
  choice
    (assume!! (found = true);; return true)
    (assume!! (found = false);;
     choice
       (assume!! (coef_Znth 0 c 0 > 0);; return true)
       (assume!! (coef_Znth 0 c 0 <= 0);; return false)).

Definition lia_deduction_check_prog (lp: LP):
  program unit bool :=
  list_iter lia_deduction_check_body lp false.

Definition lia_deduction_prog (n: Z) (lp: LP):
  program unit (Z * LP) :=
  lp' <- real_shadow_prog n lp;;
  found <- lia_deduction_check_prog lp';;
  choice
    (assume!! (found = true);; return (1, lp'))
    (assume!! (found = false);; return (0, lp')).

(** ====================================================================== *)
(** 3. Hoare Triples                                                        *)
(** ====================================================================== *)

(** 3.1. Eliminating one variable. *)

Definition eliminate_body_triple: Prop :=
  forall num prefix c bp,
    Hoare (fun _ => eliminate_xn num prefix bp)
      (eliminate_body num c bp)
      (fun bp' _ => eliminate_xn num (prefix ++ [c]) bp').

Definition eliminate_from_triple: Prop :=
  forall num prefix todo bp,
    Hoare (fun _ => eliminate_xn num prefix bp)
      (eliminate_from num todo bp)
      (fun bp' _ => eliminate_xn num (prefix ++ todo) bp').

Definition eliminate_prog_triple: Prop :=
  forall num lp,
    Hoare ATrue
      (eliminate_prog num lp)
      (fun bp _ => eliminate_xn num lp bp).

(** 3.2. Generating constraints. *)

Definition generate_new_constr_triple: Prop :=
  forall cur_num c1 c2,
    Hoare
      (fun _ =>
         1 <= cur_num /\
         cur_num < coef_Zlength c1 /\
         coef_Zlength c1 = coef_Zlength c2 /\
         coef_Znth cur_num c1 0 > 0 /\
         coef_Znth cur_num c2 0 < 0)
      (generate_new_constr_prog cur_num c1 c2)
      (fun c3 _ =>
         generate_new_constraint cur_num c1 c2 c3).

Definition generate_new_constraints_inner_body_triple: Prop :=
  forall cur_num lp11 c1 lp21 c2 lp22 gen init acc,
    Hoare
      (fun _ =>
         acc = gen ++ init /\
         1 <= cur_num /\
         cur_num < coef_Zlength c1 /\
         coef_Zlength c1 = coef_Zlength c2 /\
         coef_Znth cur_num c1 0 > 0 /\
         coef_Znth cur_num c2 0 < 0 /\
         generate_new_constraints_partial
           cur_num lp11 c1 lp21 (c2 :: lp22) gen)
      (generate_new_constraints_inner_body cur_num c1 c2 acc)
      (fun acc' _ =>
         exists gen',
           acc' = gen' ++ init /\
           generate_new_constraints_partial
             cur_num lp11 c1 (lp21 ++ [c2]) lp22 gen').

Definition generate_new_constraints_inner_loop_triple: Prop :=
  forall cur_num lp11 c1 lp21 lp22 gen init acc,
    Hoare
      (fun _ =>
         acc = gen ++ init /\
         generate_new_constraints_partial
           cur_num lp11 c1 lp21 lp22 gen /\
         (forall c2,
            In c2 lp22 ->
            1 <= cur_num /\
            cur_num < coef_Zlength c1 /\
            coef_Zlength c1 = coef_Zlength c2 /\
            coef_Znth cur_num c1 0 > 0 /\
            coef_Znth cur_num c2 0 < 0))
      (generate_new_constraints_inner_loop cur_num c1 lp22 acc)
      (fun acc' _ =>
         exists gen',
           acc' = gen' ++ init /\
           generate_new_constraints_partial
             cur_num lp11 c1 (lp21 ++ lp22) nil gen').

Definition generate_new_constraints_inner_loop_complete_triple: Prop :=
  forall cur_num lp11 c1 lp2 gen init acc,
    Hoare
      (fun _ =>
         acc = gen ++ init /\
         generate_new_constraints cur_num lp11 lp2 gen /\
         (forall c2,
            In c2 lp2 ->
            1 <= cur_num /\
            cur_num < coef_Zlength c1 /\
            coef_Zlength c1 = coef_Zlength c2 /\
            coef_Znth cur_num c1 0 > 0 /\
            coef_Znth cur_num c2 0 < 0))
      (generate_new_constraints_inner_loop cur_num c1 lp2 acc)
      (fun acc' _ =>
         exists gen',
           acc' = gen' ++ init /\
           generate_new_constraints cur_num (lp11 ++ [c1]) lp2 gen').

Definition generate_new_constraint_list_loop_triple: Prop :=
  forall cur_num lp11 lp12 lp2 gen init acc,
    Hoare
      (fun _ =>
         acc = gen ++ init /\
         generate_new_constraints cur_num lp11 lp2 gen /\
         (forall c1 c2,
            In c1 lp12 ->
            In c2 lp2 ->
            1 <= cur_num /\
            cur_num < coef_Zlength c1 /\           
            coef_Zlength c1 = coef_Zlength c2 /\
            coef_Znth cur_num c1 0 > 0 /\
            coef_Znth cur_num c2 0 < 0))
      (generate_new_constraint_list_loop cur_num lp12 lp2 acc)
      (fun acc' _ =>
         exists gen',
           acc' = gen' ++ init /\
           generate_new_constraints cur_num (lp11 ++ lp12) lp2 gen').

Definition generate_new_constraint_list_triple: Prop :=
  forall cur_num lp1 lp2 init,
    Hoare
      (fun _ =>
         forall c1 c2,
           In c1 lp1 ->
           In c2 lp2 ->
           1 <= cur_num /\
           cur_num < coef_Zlength c1 /\
           coef_Zlength c1 = coef_Zlength c2 /\
           coef_Znth cur_num c1 0 > 0 /\
           coef_Znth cur_num c2 0 < 0)
      (generate_new_constraint_list_prog cur_num lp1 lp2 init)
      (fun out _ =>
         exists gen,
           generate_new_constraints cur_num lp1 lp2 gen /\
           out = gen ++ init).

(** 3.3. Real shadow. *)

Definition real_shadow_step_triple: Prop :=
  forall n cnt lp,
    Hoare
      (fun _ =>
         1 <= cnt /\
         cnt <= n /\
         InequList_Zeros lp (cnt + 1) (n + 1) /\
         (forall c, In c lp -> coef_Zlength c = n + 1))
      (real_shadow_step_prog cnt lp)
      (fun lp' _ =>
         LP_implies lp lp' /\
         InequList_Zeros lp' cnt (n + 1) /\
         (forall c, In c lp' -> coef_Zlength c = n + 1)).

Definition real_shadow_body_triple: Prop :=
  forall n lp0 cnt lp,
    Hoare
      (fun _ =>
         1 <= cnt /\
         cnt <= n /\
         LP_implies lp0 lp /\
         InequList_Zeros lp (cnt + 1) (n + 1) /\
         (forall c, In c lp -> coef_Zlength c = n + 1))
      (real_shadow_body_prog (cnt, lp))
      (fun st' _ =>
         let '(cnt', lp') := st' in
         cnt' = cnt - 1 /\
         0 <= cnt' /\
         cnt' <= n /\
         LP_implies lp0 lp' /\
         InequList_Zeros lp' (cnt' + 1) (n + 1) /\
         (forall c, In c lp' -> coef_Zlength c = n + 1)).

Definition real_shadow_loop_triple: Prop :=
  forall n cnt lp0 lp,
    Hoare
      (fun _ =>
         0 <= cnt /\
         cnt <= n /\
         LP_implies lp0 lp /\
         InequList_Zeros lp (cnt + 1) (n + 1) /\
         (forall c, In c lp -> coef_Zlength c = n + 1))
      (real_shadow_loop_prog cnt lp)
      (fun lp' _ =>
         LP_implies lp0 lp' /\
         InequList_Zeros lp' 1 (n + 1) /\
         (forall c, In c lp' -> coef_Zlength c = n + 1)).

Definition real_shadow_triple: Prop :=
  forall n lp,
    Hoare
      (fun _ =>
         1 <= n /\
         (forall c, In c lp -> coef_Zlength c = n + 1))
      (real_shadow_prog n lp)
      (fun lp' _ =>
         LP_implies lp lp' /\
         InequList_Zeros lp' 1 (n + 1) /\
         (forall c, In c lp' -> coef_Zlength c = n + 1)).

(** 3.4. LIA deduction. *)

Definition lia_deduction_check_body_triple: Prop :=
  forall prefix c found,
    Hoare
      (fun _ =>
         (found = true -> HasPositiveConst prefix) /\
         (found = false -> NonPos prefix))
      (lia_deduction_check_body c found)
      (fun found' _ =>
         (found' = true -> HasPositiveConst (prefix ++ [c])) /\
         (found' = false -> NonPos (prefix ++ [c]))).

Definition lia_deduction_check_triple: Prop :=
  forall lp,
    Hoare ATrue
      (lia_deduction_check_prog lp)
      (fun found _ =>
         (found = true -> HasPositiveConst lp) /\
         (found = false -> NonPos lp)).

Definition lia_deduction_triple: Prop :=
  forall n lp,
    Hoare
      (fun _ =>
         1 <= n /\
         (forall c, In c lp -> coef_Zlength c = n + 1))
      (lia_deduction_prog n lp)
      (fun ret_lp _ =>
         let '(ret, lp') := ret_lp in
         (ret = 1 /\ UNSAT lp) \/
         (ret = 0 /\
          LP_implies lp lp' /\
          InequList_Zeros lp' 1 (n + 1))).

(** ====================================================================== *)
(** 4. Proofs                                                              *)
(** ====================================================================== *)

(** 4.1. Elimination helper proofs. *)

Lemma eliminate_xn_empty:
  forall num, eliminate_xn num nil empty_bp.
Proof.
  intros.
  constructor; intros c; simpl; tauto.
Qed.

Lemma eliminate_xn_step_upper:
  forall num prefix c bp,
    eliminate_xn num prefix bp ->
    nth_coef num c > 0 ->
    eliminate_xn num (prefix ++ [c]) (add_upper c bp).
Proof.
  intros num prefix c bp Hbp Hc.
  destruct Hbp as [Hup Hlo Hre].
  constructor; intros d; simpl.
  - rewrite Hup, in_app_iff; simpl.
    split; intros H.
    + destruct H as [H | H].
      * subst; tauto.
      * tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; auto.
  - rewrite Hlo, in_app_iff; simpl.
    split; intros H.
    + tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; lia.
  - rewrite Hre, in_app_iff; simpl.
    split; intros H.
    + tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; lia.
Qed.

Lemma eliminate_xn_step_lower:
  forall num prefix c bp,
    eliminate_xn num prefix bp ->
    nth_coef num c < 0 ->
    eliminate_xn num (prefix ++ [c]) (add_lower c bp).
Proof.
  intros num prefix c bp Hbp Hc.
  destruct Hbp as [Hup Hlo Hre].
  constructor; intros d; simpl.
  - rewrite Hup, in_app_iff; simpl.
    split; intros H.
    + tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; lia.
  - rewrite Hlo, in_app_iff; simpl.
    split; intros H.
    + destruct H as [H | H].
      * subst; tauto.
      * tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; auto.
  - rewrite Hre, in_app_iff; simpl.
    split; intros H.
    + tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; lia.
Qed.

Lemma eliminate_xn_step_remain:
  forall num prefix c bp,
    eliminate_xn num prefix bp ->
    nth_coef num c = 0 ->
    eliminate_xn num (prefix ++ [c]) (add_remain c bp).
Proof.
  intros num prefix c bp Hbp Hc.
  destruct Hbp as [Hup Hlo Hre].
  constructor; intros d; simpl.
  - rewrite Hup, in_app_iff; simpl.
    split; intros H.
    + tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; lia.
  - rewrite Hlo, in_app_iff; simpl.
    split; intros H.
    + tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; lia.
  - rewrite Hre, in_app_iff; simpl.
    split; intros H.
    + destruct H as [H | H].
      * subst; tauto.
      * tauto.
    + destruct H as [[H | [H | []]] Hd].
      * tauto.
      * subst; auto.
Qed.

Lemma mul_list_length:
  forall m l, length (mul_list m l) = length l.
Proof.
  intros.
  induction l; simpl; auto.
Qed.

Lemma list_add_length:
  forall l1 l2,
    length l1 = length l2 ->
    length (list_add l1 l2) = length l1.
Proof.
  intros l1.
  induction l1; intros.
  - destruct l2; simpl in *; try discriminate; auto.
  - destruct l2; simpl in *; try discriminate.
    rewrite IHl1 by lia.
    reflexivity.
Qed.

Lemma constr_list_constr:
  forall l, l <> nil -> Constraint_list (list_Constraint l) = l.
Proof.
  intros.
  destruct l; simpl; tauto.
Qed.

Lemma coef_Zlength_pos:
  forall c, coef_Zlength c > 0.
Proof.
  intros.
  unfold coef_Zlength, Constraint_list.
  simpl.
  lia.
Qed.

Lemma coef_Zlength_length_coef:
  forall c n,
    n = coef_Zlength c -> Z.of_nat (length (coef c)) = n - 1.
Proof.
  intros.
  unfold coef_Zlength, Constraint_list in H.
  simpl in H.
  lia.
Qed.

Lemma coef_Zlength_overflow:
  forall c n,
    n >= coef_Zlength c ->
    coef_Znth n c 0 = 0.
Proof.
  intros.
  unfold coef_Znth, coef_Zlength, Constraint_list in *.
  unfold Znth.
  apply nth_overflow.
  lia.
Qed.

Lemma coef_Znth_nth:
  forall n c,
    n >= 1 ->
    coef_Znth n c 0 = nth_coef n c.
Proof.
  intros.
  unfold coef_Znth, nth_coef.
  unfold Constraint_list.
  rewrite Znth_cons by lia.
  unfold Znth.
  reflexivity.
Qed.

Lemma list_add_mul_ext:
  forall l l1 l2 m1 m2,
    length l1 = length l2 ->
    l = list_add (mul_list m1 l1) (mul_list m2 l2) ->
    length l = length l1 /\
    (forall i, nth i l 0 = m1 * nth i l1 0 + m2 * nth i l2 0).
Proof.
  intros.
  split.
  - assert (length (mul_list m1 l1) = length (mul_list m2 l2)).
    { repeat rewrite mul_list_length; auto. }
    assert (length l = length (mul_list m1 l1)).
    { rewrite H0. apply list_add_length; auto. }
    rewrite H2. apply mul_list_length.
  - revert l l2 H H0.
    induction l1; intros.
    + simpl in H.
      destruct l2; try discriminate.
      simpl in H0.
      subst l.
      destruct i; simpl; lia.
    + simpl in H.
      destruct l2; try discriminate.
      simpl in H0.
      destruct l; try discriminate.
      simpl in H.
      assert (length l1 = length l2) by lia; clear H.
      injection H0 as Hhead Htail.
      destruct i; simpl.
      * lia.
      * rewrite Htail.
        apply IHl1; auto.
Qed.

Lemma list_eq_ext_nat:
  forall (T: Type) (l1 l2: list T) d,
    length l1 = length l2 ->
    (forall i, (i < length l1)%nat -> nth i l1 d = nth i l2 d) ->
    l1 = l2.
Proof.
  intros T l1.
  induction l1; intros.
  - destruct l2; simpl in *; try lia; reflexivity.
  - destruct l2; simpl in *; try lia.
    f_equal.
    + specialize (H0 O ltac:(lia)).
      exact H0.
    + apply (IHl1 l2 d).
      * lia.
      * intros i Hi.
        specialize (H0 (S i) ltac:(lia)).
        exact H0.
Qed.

Lemma coef_Znth_list_Constraint_app_lt:
  forall l v i,
    0 <= i < Zlength l ->
    coef_Znth i (list_Constraint (l ++ [v])) 0 =
    coef_Znth i (list_Constraint l) 0.
Proof.
  intros.
  unfold coef_Znth.
  rewrite !constr_list_constr.
  - rewrite app_Znth1; auto.
  - destruct l; simpl in *; try congruence.
    rewrite Zlength_correct in H.
    simpl in H.
    lia.
  - destruct l; simpl; congruence.
Qed.

Lemma coef_Znth_list_Constraint_app_eq:
  forall l v,
    coef_Znth (Zlength l) (list_Constraint (l ++ [v])) 0 = v.
Proof.
  intros.
  unfold coef_Znth.
  rewrite constr_list_constr.
  - rewrite app_Znth2 by lia.
    rewrite Zminus_diag.
    simpl.
    reflexivity.
  - destruct l; simpl; congruence.
Qed.

Lemma generate_new_constraint_complete:
  forall num c1 c2 c3,
    num >= 1 ->
    (exists n m1 m2,
        n = coef_Zlength c1 /\
        n = coef_Zlength c2 /\
        n = coef_Zlength c3 /\
        generate_new_constraint_partial num n m1 m2 c1 c2 c3) ->
    generate_new_constraint num c1 c2 c3.
Proof.
  intros num c1 c2 c3 Hnum H.
  destruct H as [n [m1 [m2 [Hc1 [Hc2 [Hc3 Hpartial]]]]]].
  unfold generate_new_constraint_partial in Hpartial.
  destruct Hpartial as [Hm1 [Hm2 [Hcancel Hpartial]]].
  unfold generate_new_constraint.
  exists m1, m2.
  repeat split; auto.
  - rewrite <- coef_Znth_nth by lia.
    destruct (Z_lt_dec num n).
    + specialize (Hpartial num ltac:(lia)).
      rewrite Hcancel in Hpartial.
      lia.
    + apply coef_Zlength_overflow.
      lia.
  - destruct c3 as [c ef].
    pose proof coef_Zlength_pos c1.
    unfold coef_Znth, Constraint_list in Hpartial.
    unfold Znth in Hpartial.
    f_equal.
    + specialize (Hpartial 0 ltac:(lia)).
      simpl in Hpartial.
      exact Hpartial.
    + assert
        (K: forall k,
            Z.of_nat k < n - 1 ->
            nth k ef 0 =
              m1 * nth k (coef c1) 0 + m2 * nth k (coef c2) 0).
      {
        intros.
        specialize (Hpartial (Z.of_nat (S k)) ltac:(lia)).
        rewrite Nat2Z.id in Hpartial.
        simpl in Hpartial.
        exact Hpartial.
      }
      set (l := list_add (mul_list m1 (coef c1)) (mul_list m2 (coef c2))).
      pose proof coef_Zlength_length_coef _ _ Hc1.
      pose proof coef_Zlength_length_coef _ _ Hc2.
      pose proof coef_Zlength_length_coef _ _ Hc3.
      simpl in H2.
      assert (length (coef c1) = length (coef c2)) by lia.
      assert (L: l = list_add (mul_list m1 (coef c1)) (mul_list m2 (coef c2))) by reflexivity.
      pose proof list_add_mul_ext l _ _ m1 m2 H3 L as [Hlen Hnth].
      apply list_eq_ext_nat with (d := 0); try lia.
      intros.
      rewrite Hnth.
      apply K.
      lia.
Qed.

Lemma gcd_div_left_pos:
  forall x y,
    x > 0 ->
    y > 0 ->
    x / Z.gcd x y > 0.
Proof.
  intros.
  assert (0 < x / Z.gcd x y).
  {
    apply Z.div_str_pos.
    split.
    - pose proof Z.gcd_nonneg x y.
      destruct (Z.gcd x y) eqn: Hg; try lia.
      apply Z.gcd_eq_0_l in Hg.
      lia.
    - apply Z.divide_pos_le; try lia.
      apply Z.gcd_divide_l.
  }
  lia.
Qed.

Lemma gcd_div_right_pos:
  forall x y,
    x > 0 ->
    y > 0 ->
    y / Z.gcd x y > 0.
Proof.
  intros.
  assert (0 < y / Z.gcd x y).
  {
    apply Z.div_str_pos.
    split.
    - pose proof Z.gcd_nonneg x y.
      destruct (Z.gcd x y) eqn: Hg; try lia.
      apply Z.gcd_eq_0_l in Hg.
      lia.
    - apply Z.divide_pos_le; try lia.
      apply Z.gcd_divide_r.
  }
  lia.
Qed.

Lemma gcd_div_cancel:
  forall x y,
    x > 0 ->
    y > 0 ->
    (y / Z.gcd x y) * x + (x / Z.gcd x y) * (- y) = 0.
Proof.
  intros.
  rewrite Z.gcd_comm.
  rewrite Z.gcd_div_swap.
  lia.
Qed.

(** 4.2. Hoare triple proofs for elimination and constraint generation. *)

Theorem proof_of_eliminate_body_triple:
  eliminate_body_triple.
Proof.
  unfold eliminate_body_triple.
  intros num prefix c bp.
  unfold eliminate_body.
  apply Hoare_choice.
  - apply Hoare_assume_bind; intros Hc.
    apply Hoare_ret; intros _ Hbp.
    apply eliminate_xn_step_upper; auto.
  - apply Hoare_choice.
    + apply Hoare_assume_bind; intros Hc.
      apply Hoare_ret; intros _ Hbp.
      apply eliminate_xn_step_lower; auto.
    + apply Hoare_assume_bind; intros Hc.
      apply Hoare_ret; intros _ Hbp.
      apply eliminate_xn_step_remain; auto.
Qed.

Theorem proof_of_eliminate_from_triple:
  eliminate_from_triple.
Proof.
  unfold eliminate_from_triple.
  intros num prefix todo bp.
  unfold eliminate_from.
  eapply Hoare_cons_pre with
      (P := fun _ : unit => eliminate_xn num (prefix ++ nil) bp).
  - intros _ Hpre.
    rewrite app_nil_r.
    exact Hpre.
  - eapply Hoare_list_iter
      with (P := fun prefix_done bp_done _ =>
                  eliminate_xn num (prefix ++ prefix_done) bp_done).
    intros prefix_done c bp_done.
    replace (prefix ++ prefix_done ++ [c]) with
      ((prefix ++ prefix_done) ++ [c]) by now rewrite app_assoc.
    apply proof_of_eliminate_body_triple.
Qed.

Theorem proof_of_eliminate_prog_triple:
  eliminate_prog_triple.
Proof.
  unfold eliminate_prog_triple.
  intros num lp.
  unfold eliminate_prog.
  eapply Hoare_cons_pre with
      (P := fun _ : unit => eliminate_xn num nil empty_bp).
  - intros _ _.
    apply eliminate_xn_empty.
  - replace lp with (nil ++ lp) by reflexivity.
    apply proof_of_eliminate_from_triple.
Qed.

Theorem proof_of_generate_new_constr_triple:
  generate_new_constr_triple.
Proof.
  unfold generate_new_constr_triple.
  intros cur_num c1 c2.
  unfold generate_new_constr_prog.
  hoare_auto; try lia.
  set (an := coef_Znth cur_num c1 0).
  set (bn := - coef_Znth cur_num c2 0).
  set (g := Z.gcd an bn).
  set (m1 := bn / g).
  set (m2 := an / g).
  change
    (Hoare
      (fun _ : unit =>
         1 <= cur_num /\
         cur_num < coef_Zlength c1 /\
         coef_Zlength c1 = coef_Zlength c2 /\
         coef_Znth cur_num c1 0 > 0 /\
         coef_Znth cur_num c2 0 < 0)
      (generate_new_constr_from m1 m2 c1 c2 0 nil)
      (fun c3 _ => generate_new_constraint cur_num c1 c2 c3)).
  unfold generate_new_constr_from.
  change
    (Hoare
      (fun _ : unit =>
         1 <= cur_num /\
         cur_num < coef_Zlength c1 /\
         coef_Zlength c1 = coef_Zlength c2 /\
         coef_Znth cur_num c1 0 > 0 /\
         coef_Znth cur_num c2 0 < 0)
      ('(_, prefix') <-
         list_iter
           (generate_new_constr_body m1 m2 c1 c2)
           (skipn (Z.to_nat 0) (Constraint_list c1))
           (0, @nil Z);;
       return (list_Constraint prefix'))
      (fun c3 _ => generate_new_constraint cur_num c1 c2 c3)).
  replace (skipn (Z.to_nat 0) (Constraint_list c1)) with (Constraint_list c1) by reflexivity.
  eapply Hoare_bind.
  - eapply Hoare_cons_pre with
      (P :=
         fun _ : unit =>
           (1 <= cur_num /\
            cur_num < coef_Zlength c1 /\
            coef_Zlength c1 = coef_Zlength c2 /\
            coef_Znth cur_num c1 0 > 0 /\
            coef_Znth cur_num c2 0 < 0) /\
           0 = Zlength (@nil Z) /\
           Zlength (@nil Z) = 0 /\
           generate_new_constraint_partial
             cur_num 0 m1 m2 c1 c2 (list_Constraint nil)).
    + intros _ Hpre.
      destruct Hpre as [Hcur_lo [Hcur_hi [Hlen [Hpos Hneg]]]].
      repeat split; auto.
      * subst m1 m2 g an bn.
        apply gcd_div_right_pos; lia.
      * subst m1 m2 g an bn.
        apply gcd_div_left_pos; lia.
      * subst m1 m2 g an bn.
        pose proof
          (gcd_div_cancel
             (coef_Znth cur_num c1 0)
             (- coef_Znth cur_num c2 0)
             ltac:(lia) ltac:(lia)) as Hcancel.
        replace
          (coef_Znth cur_num c1 0 /
             Z.gcd (coef_Znth cur_num c1 0)
               (- coef_Znth cur_num c2 0) *
           coef_Znth cur_num c2 0)
          with
          (coef_Znth cur_num c1 0 /
             Z.gcd (coef_Znth cur_num c1 0)
               (- coef_Znth cur_num c2 0) *
           - (- coef_Znth cur_num c2 0)) by nia.
        exact Hcancel.
      * intros i Hi.
        lia.
    + refine (@Hoare_list_iter unit Z (Z * list Z)
        (fun prefix_done st _ =>
           (1 <= cur_num /\
            cur_num < coef_Zlength c1 /\
            coef_Zlength c1 = coef_Zlength c2 /\
            coef_Znth cur_num c1 0 > 0 /\
            coef_Znth cur_num c2 0 < 0) /\
           let '(i, prefix) := st in
           i = Zlength prefix_done /\
           Zlength prefix = i /\
           generate_new_constraint_partial
             cur_num i m1 m2 c1 c2 (list_Constraint prefix))
        (generate_new_constr_body m1 m2 c1 c2)
        _ (Constraint_list c1) (0, @nil Z)).
      intros prefix_done x [i prefix].
      unfold generate_new_constr_body.
      apply Hoare_ret; intros _ Hpre.
      destruct Hpre as [Htop [Hi [Hlen Hpartial]]].
      destruct Hpartial as [Hm1 [Hm2 [Hcancel Hpartial]]].
      simpl.
      split; [exact Htop |].
      split.
      * rewrite Zlength_app_cons; lia.
      * split.
        -- rewrite Zlength_app_cons; lia.
        -- unfold generate_new_constraint_partial.
           repeat split; auto.
           intros j Hj.
           destruct (Z_lt_ge_dec j i).
           ++ rewrite coef_Znth_list_Constraint_app_lt by lia.
              apply Hpartial.
              lia.
           ++ assert (j = i) by lia.
              subst j.
              replace i with (Zlength prefix) by lia.
              rewrite coef_Znth_list_Constraint_app_eq.
              reflexivity.
  - intros [i prefix].
    apply Hoare_ret; intros _ Hpost.
    simpl in Hpost.
    destruct Hpost as [Htop [Hi [Hlen Hpartial]]].
    destruct Htop as [Hcur_lo [Hcur_hi [Hc12len [Hpos Hneg]]]].
    apply generate_new_constraint_complete; [lia |].
    exists (coef_Zlength c1), m1, m2.
    split; [reflexivity |].
    split; [exact Hc12len |].
    split.
    + unfold coef_Zlength.
      rewrite constr_list_constr.
      * rewrite <- !Zlength_correct.
        rewrite Hlen, Hi.
        reflexivity.
      * destruct prefix; simpl in *.
        -- rewrite Zlength_correct in Hlen.
           simpl in Hlen.
           pose proof coef_Zlength_pos c1.
           unfold coef_Zlength, Constraint_list in H.
           simpl in H.
           rewrite Zlength_correct in Hi.
           unfold Constraint_list in Hi.
           simpl in Hi.
           lia.
        -- congruence.
    + replace (coef_Zlength c1) with i.
      * exact Hpartial.
      * unfold coef_Zlength.
        rewrite <- Zlength_correct.
        rewrite Hi.
        reflexivity.
Qed.

Lemma in_list_app1:
  forall (T: Type) (x1 x2: T) l,
    In x1 l -> In x1 (l ++ [x2]).
Proof.
  intros.
  apply in_or_app.
  auto.
Qed.

Lemma generate_new_constraints_step:
  forall n l1 x1 l21 x2 l22 x3 l3,
    generate_new_constraints_partial n l1 x1 l21 (x2 :: l22) l3 /\
    generate_new_constraint n x1 x2 x3 ->
    generate_new_constraints_partial n l1 x1 (l21 ++ [x2]) l22 (x3 :: l3).
Proof.
  unfold generate_new_constraints_partial.
  intros.
  destruct H as [Hpartial Hnew].
  destruct Hpartial as [res1 [res2 [Hmem [Hres1 Hres2]]]].
  exists res1.
  exists (x3 :: res2).
  split; intros.
  - pose proof Hmem c as [Hmem1 Hmem2].
    split; intros H.
    + simpl in H.
      destruct H as [H | H].
      * subst c.
        right; simpl; auto.
      * apply Hmem1 in H.
        destruct H as [H | H].
        -- auto.
        -- right; simpl; auto.
    + destruct H as [H | H].
      * simpl; right.
        apply Hmem2; auto.
      * simpl in H.
        destruct H as [H | H].
        -- subst c; simpl; auto.
        -- simpl; right.
           apply Hmem2; auto.
  - split; intros.
    + replace ((l21 ++ [x2]) ++ l22) with (l21 ++ x2 :: l22).
      * exact Hres1.
      * rewrite <- app_assoc.
        reflexivity.
    + simpl in H.
      destruct H as [H | H].
      * subst c2.
        exists x2.
        split.
        -- apply in_elt.
        -- exact Hnew.
      * apply Hres2 in H.
        destruct H as [x4 [Hx4 Hx4gen]].
        exists x4.
        split.
        -- apply in_list_app1.
           exact Hx4.
        -- exact Hx4gen.
Qed.

Lemma generate_new_constraints_complete:
  forall n l1 x1 l2 l3,
    generate_new_constraints_partial n l1 x1 l2 nil l3 ->
    generate_new_constraints n (l1 ++ [x1]) l2 l3.
Proof.
  intros.
  unfold generate_new_constraints_partial in H.
  destruct H as [res1 [res2 [Hmem [Hres1 Hres2]]]].
  unfold generate_new_constraints in *.
  intros c Hc.
  specialize (Hmem c).
  destruct Hmem as [Hmem _].
  apply Hmem in Hc.
  destruct Hc as [Hc | Hc].
  - apply Hres1 in Hc.
    destruct Hc as [c1 [c2 [Hc1 [Hc2 Hgen]]]].
    exists c1, c2.
    repeat split; try tauto.
    + apply in_or_app; left; exact Hc1.
    + apply in_app_or in Hc2.
      destruct Hc2 as [Hc2 | Hc2]; [exact Hc2 | contradiction].
  - apply Hres2 in Hc.
    destruct Hc as [c2 [Hc2 Hgen]].
    exists x1, c2.
    repeat split; try tauto.
    apply in_elt.
Qed.

Lemma generate_new_constraints_partial_init:
  forall n lp11 x lp22 lp,
    generate_new_constraints n lp11 lp22 lp ->
    generate_new_constraints_partial n lp11 x nil lp22 lp.
Proof.
  unfold generate_new_constraints_partial.
  intros.
  exists lp, nil.
  split.
  - intros c0; simpl.
    split; intros Hin.
    + left; exact Hin.
    + destruct Hin as [Hin | Hin]; [exact Hin | contradiction].
  - split.
    + exact H.
    + intros c2 Hc2; contradiction.
Qed.

Lemma generate_new_constraints_nil:
  forall n lp2,
    generate_new_constraints n nil lp2 nil.
Proof.
  unfold generate_new_constraints.
  intros n lp2 c Hc.
  contradiction.
Qed.

Theorem proof_of_generate_new_constraints_inner_body_triple:
  generate_new_constraints_inner_body_triple.
Proof.
  unfold generate_new_constraints_inner_body_triple.
  intros cur_num lp11 c1 lp21 c2 lp22 gen init acc.
  unfold generate_new_constraints_inner_body.
  eapply Hoare_bind with
    (Q := fun c3 _ =>
            generate_new_constraint cur_num c1 c2 c3 /\
            acc = gen ++ init /\
            generate_new_constraints_partial
              cur_num lp11 c1 lp21 (c2 :: lp22) gen).
  - apply Hoare_conj.
    + eapply Hoare_cons_pre with
      (P :=
           fun _ : unit =>
             1 <= cur_num /\
             cur_num < coef_Zlength c1 /\
             coef_Zlength c1 = coef_Zlength c2 /\
             coef_Znth cur_num c1 0 > 0 /\
             coef_Znth cur_num c2 0 < 0).
      * intros s Hpre.
        tauto.
      * apply proof_of_generate_new_constr_triple.
    + eapply Hoare_implies with
        (P' :=
           fun _ : unit =>
             1 <= cur_num /\
             cur_num < coef_Zlength c1 /\
             coef_Zlength c1 = coef_Zlength c2 /\
             coef_Znth cur_num c1 0 > 0 /\
             coef_Znth cur_num c2 0 < 0)
        (P0 :=
           acc = gen ++ init /\
           generate_new_constraints_partial
             cur_num lp11 c1 lp21 (c2 :: lp22) gen).
      * intros s Hpre.
        split; tauto.
      * intros Hkeep.
        eapply Hoare_cons_post.
        -- intros _ _ _; exact Hkeep.
        -- apply proof_of_generate_new_constr_triple.
  - intros c3.
    apply Hoare_ret; intros _ [Hgen [Hacc Hpartial]].
    exists (c3 :: gen).
    split.
    + rewrite Hacc. reflexivity.
    + apply generate_new_constraints_step.
      split; auto.
Qed.

Theorem proof_of_generate_new_constraints_inner_loop_triple:
  generate_new_constraints_inner_loop_triple.
Proof.
  unfold generate_new_constraints_inner_loop_triple.
  intros cur_num lp11 c1 lp21 lp22.
  revert lp21.
  induction lp22 as [| c2 lp22 IH]; intros lp21 gen init acc; simpl.
  - apply Hoare_ret; intros _ [Hacc [Hpartial _]].
    exists gen.
    split; [exact Hacc |].
    rewrite app_nil_r.
    exact Hpartial.
  - eapply Hoare_bind with
      (Q := fun acc' _ =>
              (exists gen',
                 acc' = gen' ++ init /\
                 generate_new_constraints_partial
                   cur_num lp11 c1 (lp21 ++ [c2]) lp22 gen') /\
              (forall c2',
                 In c2' lp22 ->
                 1 <= cur_num /\
                 cur_num < coef_Zlength c1 /\
                 coef_Zlength c1 = coef_Zlength c2' /\
                 coef_Znth cur_num c1 0 > 0 /\
                 coef_Znth cur_num c2' 0 < 0)).
    + apply Hoare_conj.
      * eapply Hoare_cons_pre with
      (P :=
             fun _ : unit =>
               acc = gen ++ init /\
               1 <= cur_num /\
               cur_num < coef_Zlength c1 /\
               coef_Zlength c1 = coef_Zlength c2 /\
               coef_Znth cur_num c1 0 > 0 /\
               coef_Znth cur_num c2 0 < 0 /\
               generate_new_constraints_partial
                 cur_num lp11 c1 lp21 (c2 :: lp22) gen).
        -- intros _ [Hacc [Hpartial Hall]].
           pose proof (Hall c2 ltac:(simpl; auto)) as Hc2.
           tauto.
        -- apply proof_of_generate_new_constraints_inner_body_triple.
      * eapply Hoare_implies with
          (P' :=
             fun _ : unit =>
               acc = gen ++ init /\
               1 <= cur_num /\
               cur_num < coef_Zlength c1 /\
               coef_Zlength c1 = coef_Zlength c2 /\
               coef_Znth cur_num c1 0 > 0 /\
               coef_Znth cur_num c2 0 < 0 /\
               generate_new_constraints_partial
                 cur_num lp11 c1 lp21 (c2 :: lp22) gen)
          (P0 :=
             forall c2',
               In c2' lp22 ->
               1 <= cur_num /\
               cur_num < coef_Zlength c1 /\
               coef_Zlength c1 = coef_Zlength c2' /\
               coef_Znth cur_num c1 0 > 0 /\
               coef_Znth cur_num c2' 0 < 0).
        -- intros _ [Hacc [Hpartial Hall]].
           split.
           ++ intros c2' Hc2'.
              apply Hall; simpl; auto.
           ++ pose proof (Hall c2 ltac:(simpl; auto)) as Hc2.
              tauto.
        -- intros Hall_tail.
           eapply Hoare_cons_post.
           ++ intros _ _ _; exact Hall_tail.
           ++ apply proof_of_generate_new_constraints_inner_body_triple.
    + intros acc'.
      eapply Hoare_cons_post with
      (Q :=
           fun acc'' _ =>
             exists gen',
               acc'' = gen' ++ init /\
               generate_new_constraints_partial
                 cur_num lp11 c1 ((lp21 ++ [c2]) ++ lp22) nil gen').
      * intros acc'' s Hpost.
        destruct Hpost as [gen' [Heq Hpartial]].
        exists gen'.
        split; [exact Heq |].
        replace (lp21 ++ c2 :: lp22) with ((lp21 ++ [c2]) ++ lp22) by
          (rewrite <- app_assoc; reflexivity).
        exact Hpartial.
      * eapply Hoare_cons_pre with
          (P :=
             fun _ : unit =>
               exists gen',
                 acc' = gen' ++ init /\
                 generate_new_constraints_partial
                   cur_num lp11 c1 (lp21 ++ [c2]) lp22 gen' /\
                 (forall c2' : Constraint,
                    In c2' lp22 ->
                    1 <= cur_num /\
                    cur_num < coef_Zlength c1 /\
                    coef_Zlength c1 = coef_Zlength c2' /\
                    coef_Znth cur_num c1 0 > 0 /\
                    coef_Znth cur_num c2' 0 < 0)).
        -- intros _ [[gen' [Heq Hpartial]] Hall].
           exists gen'.
           split; [exact Heq |].
           split; [exact Hpartial | exact Hall].
        -- eapply Hoare_pre_ex.
           intros gen'.
           eapply Hoare_cons_post with
             (Q :=
                fun acc'' _ =>
                  exists gen'',
                    acc'' = gen'' ++ init /\
                    generate_new_constraints_partial
                      cur_num lp11 c1 ((lp21 ++ [c2]) ++ lp22) nil gen'').
           ++ intros acc'' s Hpost.
              destruct Hpost as [gen'' [Heq Hpartial]].
              exists gen''.
              split; [exact Heq |].
              replace (lp21 ++ c2 :: lp22)
                with ((lp21 ++ [c2]) ++ lp22) by
                (rewrite <- app_assoc; reflexivity).
              exact Hpartial.
           ++ apply (IH (lp21 ++ [c2]) gen' init acc').
Qed.

Theorem proof_of_generate_new_constraints_inner_loop_complete_triple:
  generate_new_constraints_inner_loop_complete_triple.
Proof.
  unfold generate_new_constraints_inner_loop_complete_triple.
  intros cur_num lp11 c1 lp2 gen init acc.
  eapply Hoare_cons_pre with
      (P :=
       fun _ : unit =>
         acc = gen ++ init /\
         generate_new_constraints_partial cur_num lp11 c1 nil lp2 gen /\
         (forall c2,
            In c2 lp2 ->
            1 <= cur_num /\
            cur_num < coef_Zlength c1 /\
            coef_Zlength c1 = coef_Zlength c2 /\
            coef_Znth cur_num c1 0 > 0 /\
            coef_Znth cur_num c2 0 < 0)).
  - intros _ [Hacc [Hgen Hall]].
    split.
    + exact Hacc.
    + split.
      * apply generate_new_constraints_partial_init.
        exact Hgen.
      * exact Hall.
  - eapply Hoare_cons_post with
      (Q :=
         fun acc' _ =>
           exists gen',
             acc' = gen' ++ init /\
             generate_new_constraints_partial cur_num lp11 c1 (nil ++ lp2) nil gen').
    + intros acc' s Hpost.
      destruct Hpost as [gen' [Heq Hpartial]].
      exists gen'.
      split; [exact Heq |].
      replace (nil ++ lp2) with lp2 in Hpartial by reflexivity.
      apply generate_new_constraints_complete.
      exact Hpartial.
    + apply proof_of_generate_new_constraints_inner_loop_triple.
Qed.

Theorem proof_of_generate_new_constraint_list_loop_triple:
  generate_new_constraint_list_loop_triple.
Proof.
  unfold generate_new_constraint_list_loop_triple.
  intros cur_num lp11 lp12.
  revert lp11.
  induction lp12 as [| c1 lp12 IH]; intros lp11 lp2 gen init acc; simpl.
  - apply Hoare_ret; intros _ [Hacc [Hgen _]].
    exists gen.
    split; [exact Hacc |].
    rewrite app_nil_r.
    exact Hgen.
  - eapply Hoare_bind with
      (Q := fun acc' _ =>
              (exists gen',
                 acc' = gen' ++ init /\
                 generate_new_constraints cur_num (lp11 ++ [c1]) lp2 gen') /\
              (forall c1' c2,
                 In c1' lp12 ->
                 In c2 lp2 ->
                 1 <= cur_num /\
                 cur_num < coef_Zlength c1' /\
                 coef_Zlength c1' = coef_Zlength c2 /\
                 coef_Znth cur_num c1' 0 > 0 /\
                 coef_Znth cur_num c2 0 < 0)).
    + apply Hoare_conj.
      * eapply Hoare_cons_pre with
      (P :=
             fun _ : unit =>
               acc = gen ++ init /\
               generate_new_constraints cur_num lp11 lp2 gen /\
               (forall c2,
                  In c2 lp2 ->
                  1 <= cur_num /\
                  cur_num < coef_Zlength c1 /\
                  coef_Zlength c1 = coef_Zlength c2 /\
                  coef_Znth cur_num c1 0 > 0 /\
                  coef_Znth cur_num c2 0 < 0)).
        -- intros _ [Hacc [Hgen Hall]].
           split.
           ++ exact Hacc.
           ++ split; [exact Hgen |].
              intros c2 Hc2.
              apply Hall; simpl; auto.
        -- apply proof_of_generate_new_constraints_inner_loop_complete_triple.
      * eapply Hoare_implies with
          (P' :=
             fun _ : unit =>
               acc = gen ++ init /\
               generate_new_constraints cur_num lp11 lp2 gen /\
               (forall c2,
                  In c2 lp2 ->
                  1 <= cur_num /\
                  cur_num < coef_Zlength c1 /\
                  coef_Zlength c1 = coef_Zlength c2 /\
                  coef_Znth cur_num c1 0 > 0 /\
                  coef_Znth cur_num c2 0 < 0))
          (P0 :=
             forall c1' c2',
               In c1' lp12 ->
               In c2' lp2 ->
               1 <= cur_num /\
               cur_num < coef_Zlength c1' /\
               coef_Zlength c1' = coef_Zlength c2' /\
               coef_Znth cur_num c1' 0 > 0 /\
               coef_Znth cur_num c2' 0 < 0).
        -- intros _ [Hacc [Hgen Hall]].
           split.
           ++ intros c1' c2' Hc1' Hc2'.
              apply Hall; simpl; auto.
           ++ split.
              { exact Hacc. }
              split; [exact Hgen |].
              intros c2' Hc2'.
              apply Hall; simpl; auto.
        -- intros Hall_tail.
           eapply Hoare_cons_post.
           ++ intros _ _ _; exact Hall_tail.
           ++ apply proof_of_generate_new_constraints_inner_loop_complete_triple.
    + intros acc'.
      eapply Hoare_cons_post with
      (Q :=
           fun acc'' _ =>
             exists gen',
               acc'' = gen' ++ init /\
               generate_new_constraints
                 cur_num ((lp11 ++ [c1]) ++ lp12) lp2 gen').
      * intros acc'' s Hpost.
        destruct Hpost as [gen' [Heq Hgen]].
        exists gen'.
        split; [exact Heq |].
        replace (lp11 ++ c1 :: lp12) with ((lp11 ++ [c1]) ++ lp12) by
          (rewrite <- app_assoc; reflexivity).
        exact Hgen.
      * eapply Hoare_cons_pre with
          (P :=
             fun _ : unit =>
               exists gen',
                 acc' = gen' ++ init /\
                 generate_new_constraints cur_num (lp11 ++ [c1]) lp2 gen' /\
                 (forall c1' c2 : Constraint,
                    In c1' lp12 ->
                    In c2 lp2 ->
                    1 <= cur_num /\
                    cur_num < coef_Zlength c1' /\
                    coef_Zlength c1' = coef_Zlength c2 /\
                    coef_Znth cur_num c1' 0 > 0 /\
                    coef_Znth cur_num c2 0 < 0)).
        -- intros _ [[gen' [Heq Hgen]] Hall].
           exists gen'.
           split; [exact Heq |].
           split; [exact Hgen | exact Hall].
        -- eapply Hoare_pre_ex.
           intros gen'.
           eapply Hoare_cons_post with
             (Q :=
                fun acc'' _ =>
                  exists gen'',
                    acc'' = gen'' ++ init /\
                    generate_new_constraints
                      cur_num ((lp11 ++ [c1]) ++ lp12) lp2 gen'').
           ++ intros acc'' s Hpost.
              destruct Hpost as [gen'' [Heq Hgen]].
              exists gen''.
              split; [exact Heq |].
              replace (lp11 ++ c1 :: lp12)
                with ((lp11 ++ [c1]) ++ lp12) by
                (rewrite <- app_assoc; reflexivity).
              exact Hgen.
           ++ apply (IH (lp11 ++ [c1]) lp2 gen' init acc').
Qed.

Theorem proof_of_generate_new_constraint_list_triple:
  generate_new_constraint_list_triple.
Proof.
  unfold generate_new_constraint_list_triple.
  intros cur_num lp1 lp2 init.
  unfold generate_new_constraint_list_prog.
  eapply Hoare_cons_pre with
      (P :=
       fun _ : unit =>
         init = nil ++ init /\
         generate_new_constraints cur_num nil lp2 nil /\
         (forall c1 c2,
            In c1 lp1 ->
            In c2 lp2 ->
            1 <= cur_num /\
            cur_num < coef_Zlength c1 /\
            coef_Zlength c1 = coef_Zlength c2 /\
            coef_Znth cur_num c1 0 > 0 /\
            coef_Znth cur_num c2 0 < 0)).
  - intros _ Hall.
    split.
    + reflexivity.
    + split; auto.
      apply generate_new_constraints_nil.
  - eapply Hoare_cons_post with
      (Q :=
         fun out _ =>
           exists gen,
             out = gen ++ init /\
             generate_new_constraints cur_num (nil ++ lp1) lp2 gen).
    + intros out s Hpost.
      destruct Hpost as [gen [Heq Hgen]].
      exists gen.
      split.
      * rewrite app_nil_l in Hgen.
        exact Hgen.
      * exact Heq.
    + apply (proof_of_generate_new_constraint_list_loop_triple
               cur_num nil lp1 lp2 nil init init).
Qed.

(** 4.3. Semantic helper proofs for real shadow and LIA deduction. *)

Lemma self_LP_implies:
  forall lp, LP_implies lp lp.
Proof.
  unfold LP_implies; auto.
Qed.

Lemma LP_implies_trans:
  forall lp1 lp2 lp3,
    LP_implies lp1 lp2 ->
    LP_implies lp2 lp3 ->
    LP_implies lp1 lp3.
Proof.
  unfold LP_implies; intros.
  apply H0, H, H1.
Qed.

Lemma list_add_nil_r:
  forall l, list_add l nil = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma sum_prod_nil_r:
  forall s l, sum_prod s l nil = s.
Proof.
  destruct l; reflexivity.
Qed.

Lemma const_add_sum_prod:
  forall c1 c2 l1 l2,
    sum_prod (c1 + c2) l1 l2 = c1 + sum_prod c2 l1 l2.
Proof.
  intros.
  revert c1 c2 l2.
  induction l1; intros.
  - reflexivity.
  - destruct l2.
    + simpl; reflexivity.
    + simpl. rewrite IHl1. rewrite IHl1. lia.
Qed.

Lemma sum_prod_linear_add:
  forall c c1 c2 l l1 l2 s,
    c = c1 + c2 ->
    l = list_add l1 l2 ->
    sum_prod c s l = sum_prod c1 s l1 + sum_prod c2 s l2.
Proof.
  intros.
  revert c c1 c2 l l2 s H H0.
  induction l1; intros; simpl.
  - rewrite H, H0, sum_prod_nil_r.
    simpl. apply const_add_sum_prod.
  - destruct s.
    + simpl. exact H.
    + destruct l.
      * destruct l2; simpl; discriminate H0.
      * destruct l2.
        -- simpl.
           specialize (IHl1 (c + z * z0) (c1 + z * a) c2 l nil s).
           rewrite list_add_nil_r in H0.
           rewrite sum_prod_nil_r in IHl1.
           injection H0 as ? ?.
           apply IHl1.
           ++ lia.
           ++ rewrite list_add_nil_r.
              auto.
        -- simpl.
           simpl in H0.
           injection H0 as ? ?.
           apply IHl1.
           ++ nia.
           ++ auto.
Qed.

Lemma sum_prod_linear_mul:
  forall c c1 l l1 s k,
    c = k * c1 ->
    l = mul_list k l1 ->
    sum_prod c s l = k * sum_prod c1 s l1.
Proof.
  intros.
  revert c c1 l H H0 s.
  induction l1; intros; simpl.
  - simpl in H0.
    rewrite H0, sum_prod_nil_r, sum_prod_nil_r.
    lia.
  - destruct l; simpl in H0; try discriminate.
    injection H0 as ? ?.
    destruct s.
    + simpl. exact H.
    + simpl. apply IHl1; [nia | auto].
Qed.

Lemma sum_prod_linear:
  forall c c1 c2 l l1 l2 s k1 k2,
    c = k1 * c1 + k2 * c2 ->
    l = list_add (mul_list k1 l1) (mul_list k2 l2) ->
    sum_prod c s l =
      k1 * sum_prod c1 s l1 + k2 * sum_prod c2 s l2.
Proof.
  intros.
  assert
    (Hk1:
       sum_prod (k1 * c1) s (mul_list k1 l1) =
       k1 * sum_prod c1 s l1).
  { apply sum_prod_linear_mul; reflexivity. }
  rewrite <- Hk1.
  assert
    (Hk2:
       sum_prod (k2 * c2) s (mul_list k2 l2) =
       k2 * sum_prod c2 s l2).
  { apply sum_prod_linear_mul; reflexivity. }
  rewrite <- Hk2.
  apply sum_prod_linear_add; auto.
Qed.

Lemma generate_new_constraint_sum:
  forall n c1 c2 c s,
    generate_new_constraint n c1 c2 c ->
    exists m1 m2,
      m1 > 0 /\ m2 > 0 /\
      m1 * assignment s c1 + m2 * assignment s c2 = assignment s c.
Proof.
  intros.
  unfold generate_new_constraint in H.
  destruct H as [m1 [m2 [Hm1 [Hm2 [_ Hc]]]]].
  exists m1, m2.
  repeat split; auto.
  unfold assignment.
  destruct c.
  injection Hc as ? ?.
  simpl.
  symmetry.
  apply sum_prod_linear; auto.
Qed.

Lemma generate_new_constraint_sound:
  forall n c1 c2 c s,
    generate_new_constraint n c1 c2 c ->
    satisfy_constraint s c1 ->
    satisfy_constraint s c2 ->
    satisfy_constraint s c.
Proof.
  intros.
  pose proof generate_new_constraint_sum _ _ _ _ s H as Hsum.
  destruct Hsum as [m1 [m2 [Hm1 [Hm2 Hsum]]]].
  unfold satisfy_constraint in *.
  rewrite <- Hsum.
  nia.
Qed.

Lemma generate_new_constraints_sound:
  forall n lp1 lp2 lp s,
    generate_new_constraints n lp1 lp2 lp ->
    satisfy_LP s lp1 ->
    satisfy_LP s lp2 ->
    satisfy_LP s lp.
Proof.
  unfold generate_new_constraints, satisfy_LP.
  intros n lp1 lp2 lp s Hgen Hsat1 Hsat2 c Hc.
  specialize (Hgen c Hc).
  destruct Hgen as [c1 [c2 [Hc1 [Hc2 Hnew]]]].
  eapply generate_new_constraint_sound; eauto.
Qed.

Lemma eliminate_xn_iff:
  forall n lp bp c,
    eliminate_xn n lp bp ->
    In c lp <->
    In c bp.(upper) \/ In c bp.(lower) \/ In c bp.(remain).
Proof.
  intros n lp bp c Hbp.
  destruct Hbp as [Hup Hlo Hre].
  split; intros H.
  - destruct (Z_gt_dec (nth_coef n c) 0).
    + left. apply Hup. split; auto.
    + destruct (Z_lt_dec (nth_coef n c) 0).
      * right; left. apply Hlo. split; auto.
      * right; right. apply Hre. split; auto; lia.
  - destruct H as [H | [H | H]].
    + apply Hup in H; tauto.
    + apply Hlo in H; tauto.
    + apply Hre in H; tauto.
Qed.

Lemma step_LP_implies:
  forall n lp bp lp',
    eliminate_xn n lp bp ->
    generate_new_constraints n bp.(upper) bp.(lower) lp' ->
    LP_implies lp (lp' ++ bp.(remain)).
Proof.
  unfold LP_implies, satisfy_LP.
  intros n lp bp lp' Helim Hgen s Hsat c Hc.
  apply in_app_or in Hc.
  destruct Hc as [Hc | Hc].
  - eapply generate_new_constraints_sound; eauto.
    + intros c0 Hc0.
      apply Hsat.
      apply eliminate_xn_iff with (bp:=bp) (n:=n).
      * exact Helim.
      * left; exact Hc0.
    + intros c0 Hc0.
      apply Hsat.
      apply eliminate_xn_iff with (bp:=bp) (n:=n).
      * exact Helim.
      * right; left; exact Hc0.
  - apply Hsat.
    apply eliminate_xn_iff with (bp:=bp) (n:=n).
    + exact Helim.
    + right; right; exact Hc.

Qed.

Definition InequList_nth_zero (n : Z) (lp : LP) : Prop :=
  forall c, In c lp -> coef_Znth n c 0 = 0.

Lemma generate_new_constraints_nth_zero:
  forall n l1 l2 l3,
    n >= 1 ->
    generate_new_constraints n l1 l2 l3 ->
    InequList_nth_zero n l3.
Proof.
  unfold generate_new_constraints, InequList_nth_zero.
  intros n l1 l2 l3 Hn Hgen c Hc.
  specialize (Hgen c Hc).
  destruct Hgen as [c1 [c2 [_ [_ Hnew]]]].
  unfold generate_new_constraint in Hnew.
  destruct Hnew as [m1 [m2 [_ [_ [Hzero _]]]]].
  rewrite coef_Znth_nth by lia.
  exact Hzero.
Qed.

Lemma eliminate_remain_nth_zero:
  forall n lp bp,
    n >= 1 ->
    eliminate_xn n lp bp ->
    InequList_nth_zero n bp.(remain).
Proof.
  unfold InequList_nth_zero.
  intros n lp bp Hn Hbp c Hc.
  destruct Hbp as [_ _ Hre].
  apply Hre in Hc.
  destruct Hc as [_ Hzero].
  rewrite coef_Znth_nth by lia.
  exact Hzero.
Qed.

Lemma InequList_nth_zero_app:
  forall n l1 l2,
    InequList_nth_zero n l1 ->
    InequList_nth_zero n l2 ->
    InequList_nth_zero n (l1 ++ l2).
Proof.
  unfold InequList_nth_zero.
  intros n l1 l2 H1 H2 c Hc.
  apply in_app_or in Hc.
  destruct Hc; auto.
Qed.

Lemma InequList_Zeros_single:
  forall n l,
    InequList_nth_zero n l ->
    InequList_Zeros l n (n + 1).
Proof.
  unfold InequList_nth_zero, InequList_Zeros.
  intros n l Hzero c Hc i Hi.
  assert (i = n) by lia.
  subst i.
  apply Hzero; auto.
Qed.

Lemma InequList_Zeros_app:
  forall l1 l2 lo hi,
    InequList_Zeros l1 lo hi ->
    InequList_Zeros l2 lo hi ->
    InequList_Zeros (l1 ++ l2) lo hi.
Proof.
  unfold InequList_Zeros.
  intros l1 l2 lo hi H1 H2 c Hc i Hi.
  apply in_app_or in Hc.
  destruct Hc as [Hc | Hc]; auto.
Qed.

Lemma generate_new_constraint_length:
  forall n c1 c2 c len,
    generate_new_constraint n c1 c2 c ->
    coef_Zlength c1 = len ->
    coef_Zlength c2 = len ->
    coef_Zlength c = len.
Proof.
  intros n c1 c2 c len Hnew Hlen1 Hlen2.
  unfold generate_new_constraint in Hnew.
  destruct Hnew as [m1 [m2 [_ [_ [_ Hc]]]]].
  subst c.
  unfold coef_Zlength, Constraint_list in *.
  simpl in *.
  f_equal.
  rewrite list_add_length.
  - rewrite mul_list_length.
    lia.
  - repeat rewrite mul_list_length.
    lia.
Qed.

Lemma generate_new_constraints_length:
  forall n l1 l2 l3 len,
    generate_new_constraints n l1 l2 l3 ->
    (forall c, In c l1 -> coef_Zlength c = len) ->
    (forall c, In c l2 -> coef_Zlength c = len) ->
    forall c, In c l3 -> coef_Zlength c = len.
Proof.
  unfold generate_new_constraints.
  intros n l1 l2 l3 len Hgen Hlen1 Hlen2 c Hc.
  specialize (Hgen c Hc).
  destruct Hgen as [c1 [c2 [Hc1 [Hc2 Hnew]]]].
  eapply generate_new_constraint_length; eauto.
Qed.

Lemma step_length:
  forall n lp bp l4 len,
    eliminate_xn n lp bp ->
    generate_new_constraints n bp.(upper) bp.(lower) l4 ->
    (forall c, In c lp -> coef_Zlength c = len) ->
    forall c, In c (l4 ++ bp.(remain)) -> coef_Zlength c = len.
Proof.
  intros n lp bp l4 len Helim Hgen Hlen c Hc.
  apply in_app_or in Hc.
  destruct Hc as [Hc | Hc].
  - eapply generate_new_constraints_length; eauto.
    + intros c0 Hc0.
      apply Hlen.
      apply (proj2 (eliminate_xn_iff n lp bp c0 Helim)).
      left; exact Hc0.
    + intros c0 Hc0.
      apply Hlen.
      apply (proj2 (eliminate_xn_iff n lp bp c0 Helim)).
      right; left; exact Hc0.
  - apply Hlen.
    apply (proj2 (eliminate_xn_iff n lp bp c Helim)).
    right; right; exact Hc.
Qed.

Lemma step_nth_zero:
  forall n lp bp l4,
    n >= 1 ->
    eliminate_xn n lp bp ->
    generate_new_constraints n bp.(upper) bp.(lower) l4 ->
    InequList_nth_zero n (l4 ++ bp.(remain)).
Proof.
  intros.
  apply InequList_nth_zero_app.
  - eapply generate_new_constraints_nth_zero; eauto.
  - eapply eliminate_remain_nth_zero; eauto.
Qed.

Lemma eliminate_keep_Zeros:
  forall n lp bp lo hi,
    eliminate_xn n lp bp ->
    InequList_Zeros lp lo hi ->
    InequList_Zeros bp.(upper) lo hi /\
    InequList_Zeros bp.(lower) lo hi /\
    InequList_Zeros bp.(remain) lo hi.
Proof.
  unfold InequList_Zeros.
  intros n lp bp lo hi Helim Hzero.
  repeat split; intros c Hc i Hi; apply Hzero with (i:=i); auto.
  - apply (proj2 (eliminate_xn_iff n lp bp c Helim)).
    left; exact Hc.
  - apply (proj2 (eliminate_xn_iff n lp bp c Helim)).
    right; left; exact Hc.
  - apply (proj2 (eliminate_xn_iff n lp bp c Helim)).
    right; right; exact Hc.
Qed.

Lemma mul_list_zero:
  forall l m n,
    Znth n l 0 = 0 ->
    Znth n (mul_list m l) 0 = 0.
Proof.
  induction l; simpl; intros.
  - destruct (Z_lt_dec n 0); unfold Znth in *; simpl in *; auto.
  - destruct (Z_lt_dec n 1).
    + unfold Znth in *.
      replace (Z.to_nat n) with 0%nat in * by lia.
      simpl in *. lia.
    + rewrite Znth_cons in * by lia.
      apply IHl.
      exact H.
Qed.

Lemma list_add_zero:
  forall l1 l2 n,
    Znth n l1 0 = 0 ->
    Znth n l2 0 = 0 ->
    Znth n (list_add l1 l2) 0 = 0.
Proof.
  induction l1; simpl; intros.
  - exact H0.
  - destruct l2; simpl in *.
    + exact H.
    + destruct (Z_lt_dec n 1).
      * unfold Znth in *.
        replace (Z.to_nat n) with 0%nat in * by lia.
        simpl in *. lia.
      * rewrite Znth_cons in * by lia.
        apply IHl1; auto.
Qed.

Lemma generate_new_constraint_keep_zero:
  forall n i c1 c2 c,
    1 <= i ->
    generate_new_constraint n c1 c2 c ->
    coef_Znth i c1 0 = 0 ->
    coef_Znth i c2 0 = 0 ->
    coef_Znth i c 0 = 0.
Proof.
  intros n i c1 c2 c Hi Hgen Hzero1 Hzero2.
  unfold generate_new_constraint in Hgen.
  destruct Hgen as [m1 [m2 [_ [_ [_ Hc]]]]].
  subst c.
  unfold coef_Znth, Constraint_list in *.
  simpl in *.
  rewrite Znth_cons in * by lia.
  apply list_add_zero; apply mul_list_zero; auto.
Qed.

Lemma generate_new_constraints_keep_Zeros:
  forall n l1 l2 l3 lo hi,
    generate_new_constraints n l1 l2 l3 ->
    InequList_Zeros l1 lo hi ->
    InequList_Zeros l2 lo hi ->
    1 <= lo ->
    InequList_Zeros l3 lo hi.
Proof.
  unfold generate_new_constraints, InequList_Zeros.
  intros n l1 l2 l3 lo hi Hgen Hzero1 Hzero2 Hlo c Hc i Hi.
  specialize (Hgen c Hc).
  destruct Hgen as [c1 [c2 [Hc1 [Hc2 Hnew]]]].
  eapply generate_new_constraint_keep_zero; eauto; try lia.
Qed.

Lemma step_keep_Zeros:
  forall n lp bp l4 lo hi,
    eliminate_xn n lp bp ->
    generate_new_constraints n bp.(upper) bp.(lower) l4 ->
    InequList_Zeros lp lo hi ->
    1 <= lo ->
    InequList_Zeros (l4 ++ bp.(remain)) lo hi.
Proof.
  intros n lp bp l4 lo hi Helim Hgen Hzero Hlo.
  pose proof eliminate_keep_Zeros n lp bp lo hi Helim Hzero
    as [Hzup [Hzlo Hzre]].
  apply InequList_Zeros_app.
  - eapply generate_new_constraints_keep_Zeros; eauto.
  - exact Hzre.
Qed.

Lemma InequList_Zeros_join_left:
  forall l lo hi,
    InequList_Zeros l lo (lo + 1) ->
    InequList_Zeros l (lo + 1) hi ->
    InequList_Zeros l lo hi.
Proof.
  unfold InequList_Zeros.
  intros l lo hi Hone Hrest c Hc i Hi.
  destruct (Z_lt_dec i (lo + 1)).
  - apply Hone; auto; lia.
  - apply Hrest; auto; lia.
Qed.

Lemma sum_prod_zero:
  forall s l z,
    (forall i, 0 <= i < Zlength l -> Znth i l 0 = 0) ->
    sum_prod z s l = z.
Proof.
  induction s as [| x s IH]; intros l z Hzero.
  - destruct l; reflexivity.
  - destruct l as [| y l].
    + reflexivity.
    + simpl.
      assert (Hy: y = 0).
      {
        specialize (Hzero 0).
        rewrite Znth0_cons in Hzero.
        apply Hzero.
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l.
        lia.
      }
      subst y.
      replace (z + x * 0) with z by lia.
      apply IH.
      intros i Hi.
      specialize (Hzero (i + 1)).
      rewrite Znth_cons in Hzero by lia.
      replace (i + 1 - 1) with i in Hzero by lia.
      apply Hzero.
      rewrite Zlength_cons.
      lia.
Qed.

Lemma assignment_zero_tail:
  forall n c s,
    coef_Zlength c = n + 1 ->
    InequList_Zeros [c] 1 (n + 1) ->
    assignment s c = coef_Znth 0 c 0.
Proof.
  intros n [b cs] s Hlen Hzero.
  unfold assignment, coef_Znth, Constraint_list in *.
  simpl in *.
  rewrite Znth0_cons.
  apply sum_prod_zero.
  intros i Hi.
  specialize (Hzero {| const := b; coef := cs |}).
  simpl in Hzero.
  specialize (Hzero (or_introl eq_refl) (i + 1)).
  assert (Hrange: 1 <= i + 1 /\ i + 1 < n + 1).
  {
    unfold coef_Zlength, Constraint_list in Hlen.
    simpl in Hlen.
    rewrite Zlength_correct in Hi.
    lia.
  }
  specialize (Hzero Hrange).
  unfold coef_Znth, Constraint_list in Hzero.
  simpl in Hzero.
  rewrite Znth_cons in Hzero by lia.
  replace (i + 1 - 1) with i in Hzero by lia.
  apply Hzero.
Qed.

Lemma positive_const_unsat:
  forall n lp c,
    In c lp ->
    coef_Znth 0 c 0 > 0 ->
    InequList_Zeros lp 1 (n + 1) ->
    (forall c0, In c0 lp -> coef_Zlength c0 = n + 1) ->
    UNSAT lp.
Proof.
  unfold UNSAT, satisfy_LP, satisfy_constraint.
  intros n lp c Hin Hpos Hzero Hlen s Hsat.
  specialize (Hsat c Hin).
  assert (Hzero_c: InequList_Zeros [c] 1 (n + 1)).
  {
    unfold InequList_Zeros in *.
    intros c0 Hc0 i Hi.
    simpl in Hc0.
    destruct Hc0 as [Hc0 | []].
    subst c0.
    apply Hzero; auto.
  }
  pose proof assignment_zero_tail n c s (Hlen c Hin) Hzero_c as Hassn.
  rewrite Hassn in Hsat.
  lia.
Qed.

Lemma positive_const_implies_unsat:
  forall n lp lp',
    LP_implies lp lp' ->
    InequList_Zeros lp' 1 (n + 1) ->
    (forall c, In c lp' -> coef_Zlength c = n + 1) ->
    HasPositiveConst lp' ->
    UNSAT lp.
Proof.
  unfold HasPositiveConst, LP_implies, UNSAT.
  intros n lp lp' Himpl Hzero Hlen [c [Hin Hpos]] s Hsat.
  apply (positive_const_unsat n lp' c Hin Hpos Hzero Hlen s).
  apply Himpl.
  exact Hsat.
Qed.

(** 4.4. Hoare triple proofs for real shadow. *)

Theorem proof_of_real_shadow_step_triple:
  real_shadow_step_triple.
Proof.
  unfold real_shadow_step_triple.
  intros n cnt lp.
  unfold real_shadow_step_prog.
  eapply Hoare_bind with
    (Q := fun bp _ =>
            eliminate_xn cnt lp bp /\
            1 <= cnt /\
            cnt <= n /\
            InequList_Zeros lp (cnt + 1) (n + 1) /\
            (forall c, In c lp -> coef_Zlength c = n + 1)).
  - apply Hoare_conj.
    + eapply Hoare_cons_pre with
      (P := ATrue).
      * intros s _; exact I.
      * apply proof_of_eliminate_prog_triple.
    + eapply Hoare_implies with
        (P' := ATrue)
        (P0 :=
           1 <= cnt /\
           cnt <= n /\
           InequList_Zeros lp (cnt + 1) (n + 1) /\
           (forall c, In c lp -> coef_Zlength c = n + 1)).
      * intros st Hpre.
        split; [exact Hpre | exact I].
      * intros Hpre.
        eapply Hoare_cons_post.
        -- intros _ _ _; exact Hpre.
        -- apply proof_of_eliminate_prog_triple.
  - intros bp.
    eapply Hoare_cons_post with
      (Q :=
         fun lp' _ =>
           (exists gen,
              generate_new_constraints cnt bp.(upper) bp.(lower) gen /\
              lp' = gen ++ bp.(remain)) /\
           (eliminate_xn cnt lp bp /\
            1 <= cnt /\
            cnt <= n /\
            InequList_Zeros lp (cnt + 1) (n + 1) /\
            (forall c, In c lp -> coef_Zlength c = n + 1))).
    + intros lp' st [Hpost Hpre].
      destruct Hpost as [gen [Hgen Hlp']].
      subst lp'.
      destruct Hpre as [Helim [Hcnt_lo [Hcnt_hi [Hzero Hlen]]]].
      assert (Hzero_left: InequList_Zeros (gen ++ remain bp) cnt (cnt + 1)).
      {
        apply InequList_Zeros_single.
        eapply step_nth_zero; eauto; lia.
      }
      assert (Hzero_right: InequList_Zeros (gen ++ remain bp) (cnt + 1) (n + 1)).
      {
        eapply step_keep_Zeros; eauto; lia.
      }
      split.
      * eapply step_LP_implies; eauto.
      * split.
        { eapply InequList_Zeros_join_left; eauto. }
        { eapply step_length; eauto. }
    + apply Hoare_conj.
      * eapply Hoare_cons_pre with
      (P :=
             fun _ : unit =>
               forall c1 c2,
                 In c1 bp.(upper) ->
                 In c2 bp.(lower) ->
                 1 <= cnt /\
                 cnt < coef_Zlength c1 /\
                 coef_Zlength c1 = coef_Zlength c2 /\
                 coef_Znth cnt c1 0 > 0 /\
                 coef_Znth cnt c2 0 < 0).
        -- intros _ [Helim [Hcnt_lo [Hcnt_hi [_ Hlen]]]].
           intros c1 c2 Hc1 Hc2.
           destruct (elim_upper _ _ _ Helim c1) as [Hup _].
           destruct (elim_lower _ _ _ Helim c2) as [Hlo _].
           specialize (Hup Hc1).
           specialize (Hlo Hc2).
           destruct Hup as [Hc1_lp Hc1_pos].
           destruct Hlo as [Hc2_lp Hc2_neg].
           repeat split; auto.
           ++ rewrite Hlen by exact Hc1_lp.
              lia.
           ++ rewrite !Hlen by assumption.
              reflexivity.
           ++ rewrite coef_Znth_nth by lia.
              exact Hc1_pos.
           ++ rewrite coef_Znth_nth by lia.
              exact Hc2_neg.
        -- apply proof_of_generate_new_constraint_list_triple.
      * eapply Hoare_implies with
          (P' :=
             fun _ : unit =>
               forall c1 c2,
                 In c1 bp.(upper) ->
                 In c2 bp.(lower) ->
                 1 <= cnt /\
                 cnt < coef_Zlength c1 /\
                 coef_Zlength c1 = coef_Zlength c2 /\
                 coef_Znth cnt c1 0 > 0 /\
                 coef_Znth cnt c2 0 < 0)
          (P0 :=
             eliminate_xn cnt lp bp /\
             1 <= cnt /\
             cnt <= n /\
             InequList_Zeros lp (cnt + 1) (n + 1) /\
             (forall c, In c lp -> coef_Zlength c = n + 1)).
        -- intros s Hpre.
           split; [exact Hpre |].
           destruct Hpre as [Helim [Hcnt_lo [Hcnt_hi [_ Hlen]]]].
           intros c1 c2 Hc1 Hc2.
           destruct (elim_upper _ _ _ Helim c1) as [Hup _].
           destruct (elim_lower _ _ _ Helim c2) as [Hlo _].
           specialize (Hup Hc1).
           specialize (Hlo Hc2).
           destruct Hup as [Hc1_lp Hc1_pos].
           destruct Hlo as [Hc2_lp Hc2_neg].
           repeat split; auto.
           ++ rewrite Hlen by exact Hc1_lp.
              lia.
           ++ rewrite !Hlen by assumption.
              reflexivity.
           ++ rewrite coef_Znth_nth by lia.
              exact Hc1_pos.
           ++ rewrite coef_Znth_nth by lia.
              exact Hc2_neg.
        -- intros Hpre.
           eapply Hoare_cons_post.
           ++ intros _ _ _; exact Hpre.
           ++ apply proof_of_generate_new_constraint_list_triple.
Qed.

Theorem proof_of_real_shadow_body_triple:
  real_shadow_body_triple.
Proof.
  unfold real_shadow_body_triple.
  intros n lp0 cnt lp.
  unfold real_shadow_body_prog.
  eapply Hoare_bind with
    (Q := fun lp' _ =>
            (LP_implies lp lp' /\
             InequList_Zeros lp' cnt (n + 1) /\
             (forall c, In c lp' -> coef_Zlength c = n + 1)) /\
            (1 <= cnt /\
             cnt <= n /\
             LP_implies lp0 lp /\
             InequList_Zeros lp (cnt + 1) (n + 1) /\
             (forall c, In c lp -> coef_Zlength c = n + 1))).
  - apply Hoare_conj.
    + eapply Hoare_cons_pre with
      (P := fun _ : unit =>
                 1 <= cnt /\
                 cnt <= n /\
                 InequList_Zeros lp (cnt + 1) (n + 1) /\
                 (forall c, In c lp -> coef_Zlength c = n + 1)).
      * intros st [Hcnt_lo [Hcnt_hi [_ [Hzero Hlen]]]].
        repeat split; auto.
      * apply proof_of_real_shadow_step_triple.
    + eapply Hoare_implies with
        (P' :=
           fun _ : unit =>
             1 <= cnt /\
             cnt <= n /\
             InequList_Zeros lp (cnt + 1) (n + 1) /\
             (forall c, In c lp -> coef_Zlength c = n + 1))
        (P0 :=
           1 <= cnt /\
           cnt <= n /\
           LP_implies lp0 lp /\
           InequList_Zeros lp (cnt + 1) (n + 1) /\
           (forall c, In c lp -> coef_Zlength c = n + 1)).
      * intros s Hpre.
        split; [exact Hpre |].
        destruct Hpre as [Hcnt_lo [Hcnt_hi [_ [Hzero Hlen]]]].
        repeat split; auto.
      * intros Hpre.
        eapply Hoare_cons_post.
        -- intros _ _ _; exact Hpre.
        -- apply proof_of_real_shadow_step_triple.
  - intros lp'.
    apply Hoare_ret; intros _ [Hstep Hpre].
    destruct Hstep as [Himpl_step [Hzero_step Hlen_step]].
    destruct Hpre as [Hcnt_lo [Hcnt_hi [Himpl0 [_ _]]]].
    simpl.
    repeat split; auto; try lia.
    + eapply LP_implies_trans; eauto.
    + replace (cnt - 1 + 1) with cnt by lia.
      exact Hzero_step.
Qed.

Theorem proof_of_real_shadow_loop_triple:
  real_shadow_loop_triple.
Proof.
  unfold real_shadow_loop_triple.
  intros n cnt lp0 lp.
  unfold real_shadow_loop_prog.
  refine ((Hoare_repeat_break
    real_shadow_loop_body
    (fun st _ =>
       let '(cnt', lp') := st in
       0 <= cnt' /\
       cnt' <= n /\
       LP_implies lp0 lp' /\
       InequList_Zeros lp' (cnt' + 1) (n + 1) /\
       (forall c, In c lp' -> coef_Zlength c = n + 1))
    (fun lp' _ =>
       LP_implies lp0 lp' /\
       InequList_Zeros lp' 1 (n + 1) /\
       (forall c, In c lp' -> coef_Zlength c = n + 1))
    _) (cnt, lp)).
  intros [cnt' lp'].
  unfold real_shadow_loop_body.
  apply Hoare_choice.
  - apply Hoare_assume_bind; intros Hcnt_pos.
    eapply Hoare_bind.
    + eapply Hoare_cons_pre with
        (P := fun _ : unit =>
                1 <= cnt' /\
                cnt' <= n /\
                LP_implies lp0 lp' /\
                InequList_Zeros lp' (cnt' + 1) (n + 1) /\
                (forall c, In c lp' -> coef_Zlength c = n + 1)).
      * intros _ [Hcnt_nonneg [Hcnt_hi [Himpl [Hzero Hlen]]]].
        repeat split; auto.
      * pose proof proof_of_real_shadow_body_triple as Hbody.
        unfold real_shadow_body_triple in Hbody.
        apply Hbody.
    + intros [cnt'' lp''].
      apply Hoare_ret; intros _ Hpost.
      simpl in Hpost.
      destruct Hpost as [_ [Hcnt_nonneg [Hcnt_hi [Himpl [Hzero Hlen]]]]].
      repeat split; auto.
  - apply Hoare_assume_bind; intros Hcnt_lt.
    apply Hoare_ret; intros _ Hinv.
    simpl in Hinv.
    destruct Hinv as [Hcnt_nonneg [_ [Himpl [Hzero Hlen]]]].
    assert (cnt' = 0) by lia.
    subst cnt'.
    repeat split; auto.
Qed.

Theorem proof_of_real_shadow_triple:
  real_shadow_triple.
Proof.
  unfold real_shadow_triple.
  intros n lp.
  unfold real_shadow_prog.
  eapply Hoare_cons_pre with
      (P := fun _ : unit =>
             0 <= n /\
             n <= n /\
             LP_implies lp lp /\
             InequList_Zeros lp (n + 1) (n + 1) /\
             (forall c, In c lp -> coef_Zlength c = n + 1)).
  - intros st [Hn Hlen].
    repeat split; auto; try lia.
    + apply self_LP_implies.
    + unfold InequList_Zeros.
      intros c Hc i Hi.
      lia.
  - pose proof proof_of_real_shadow_loop_triple as Hloop.
  unfold real_shadow_loop_triple in Hloop.
  apply Hloop.
Qed.

(** 4.5. Hoare triple proofs for LIA deduction. *)

Theorem proof_of_lia_deduction_check_body_triple:
  lia_deduction_check_body_triple.
Proof.
  unfold lia_deduction_check_body_triple.
  intros prefix c found.
  unfold lia_deduction_check_body.
  apply Hoare_choice.
  - apply Hoare_assume_bind; intros Hfound.
    apply Hoare_ret; intros _ Hpre.
    destruct Hpre as [Hpos _].
    split.
    + intros _.
      unfold HasPositiveConst in *.
      destruct (Hpos Hfound) as [c0 [Hin Hc0]].
      exists c0.
      split; auto.
      apply in_or_app; auto.
    + intros Hfalse.
      discriminate.
  - apply Hoare_assume_bind; intros Hfound.
    apply Hoare_choice.
    + apply Hoare_assume_bind; intros Hcpos.
      apply Hoare_ret; intros _ _.
      split.
      * intros _.
        unfold HasPositiveConst.
        exists c.
        split; auto.
        apply in_or_app.
        right; simpl; auto.
      * intros Hfalse.
        discriminate.
    + apply Hoare_assume_bind; intros Hcnonpos.
      apply Hoare_ret; intros _ Hpre.
      destruct Hpre as [_ Hnonpos].
      split.
      * intros Htrue.
        discriminate.
      * intros _.
        unfold NonPos in *.
        intros c0 Hc0.
        apply in_app_or in Hc0.
        destruct Hc0 as [Hc0 | Hc0].
        -- apply Hnonpos; auto.
        -- simpl in Hc0.
           destruct Hc0 as [Hc0 | []].
           subst c0.
           exact Hcnonpos.
Qed.

Theorem proof_of_lia_deduction_check_triple:
  lia_deduction_check_triple.
Proof.
  unfold lia_deduction_check_triple.
  intros lp.
  unfold lia_deduction_check_prog.
  eapply Hoare_cons_pre with
      (P := fun _ : unit =>
             (false = true -> HasPositiveConst nil) /\
             (false = false -> NonPos nil)).
  - intros st _.
    split.
    + intros Hfalse_true.
      discriminate.
    + intros _.
      unfold NonPos.
      intros c Hc.
      simpl in Hc.
      contradiction.
  - eapply Hoare_list_iter
      with (P := fun prefix found _ =>
              (found = true -> HasPositiveConst prefix) /\
              (found = false -> NonPos prefix)).
    intros prefix c found.
    apply proof_of_lia_deduction_check_body_triple.
Qed.

Theorem proof_of_lia_deduction_triple:
  lia_deduction_triple.
Proof.
  unfold lia_deduction_triple.
  intros n lp.
  unfold lia_deduction_prog.
  eapply Hoare_bind with
    (Q := fun lp' _ =>
            (LP_implies lp lp' /\
             InequList_Zeros lp' 1 (n + 1) /\
             (forall c, In c lp' -> coef_Zlength c = n + 1))).
  - apply proof_of_real_shadow_triple.
  - intros lp'.
    eapply Hoare_bind with
      (Q := fun found _ =>
              ((found = true -> HasPositiveConst lp') /\
               (found = false -> NonPos lp')) /\
              (LP_implies lp lp' /\
               InequList_Zeros lp' 1 (n + 1) /\
               (forall c, In c lp' -> coef_Zlength c = n + 1))).
    + apply Hoare_conj.
      * eapply Hoare_cons_pre with
      (P := ATrue).
        -- intros st _; exact I.
        -- pose proof proof_of_lia_deduction_check_triple as Hcheck.
           unfold lia_deduction_check_triple in Hcheck.
           apply Hcheck.
      * eapply Hoare_implies with
          (P' := ATrue)
          (P0 :=
             LP_implies lp lp' /\
             InequList_Zeros lp' 1 (n + 1) /\
             (forall c, In c lp' -> coef_Zlength c = n + 1)).
        -- intros s Hpre.
           split; [exact Hpre | exact I].
        -- intros Hpre.
           eapply Hoare_cons_post.
           ++ intros _ _ _; exact Hpre.
           ++ pose proof proof_of_lia_deduction_check_triple as Hcheck.
              unfold lia_deduction_check_triple in Hcheck.
              apply Hcheck.
    + intros found.
      apply Hoare_choice.
      * apply Hoare_assume_bind; intros Hfound.
        apply Hoare_ret; intros _ [Hcheck Hshadow].
        left.
        split; auto.
        destruct Hcheck as [Hhas _].
        destruct Hshadow as [Himpl [Hzero Hlen]].
        eapply positive_const_implies_unsat; eauto.
      * apply Hoare_assume_bind; intros Hfound.
        apply Hoare_ret; intros _ [_ Hshadow].
        right.
        split; auto.
        destruct Hshadow as [Himpl [Hzero _]].
        split; auto.
Qed.
