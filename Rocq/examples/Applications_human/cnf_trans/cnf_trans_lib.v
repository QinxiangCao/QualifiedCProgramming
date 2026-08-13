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
From SimpleC.EE.Applications_human Require Import malloc.
From SimpleC.EE.Applications_human.cnf_trans Require Import smt_lang_lib.

Notation "'cnf_list_cell'" := (list Z) (at level 0, only parsing).

Notation "'cnf_list'" := (list (list Z)) (at level 0, only parsing).

(* Inductive PreData : Type :=
  | PD (cnf_res: cnf_list) (prop_cnt: Z) (clause_cnt: Z): PreData. *)

(* Print IntArray.full. *)
Definition init_int_array (x: addr) (size: Z): Assertion :=
  IntArray.full x size (all_zero_list size).

Definition store_clause (x: addr) (clause: list Z): Assertion :=
 “ Zlength clause <= 3 ” && “ Forall (fun z => z <> 0) clause ” &&
  IntArray.full x 3%Z (clause ++ all_zero_list (3 - Zlength clause)).

Definition store_cnf_list_cell (x: addr) (clause: list Z): Assertion :=
 “ x <> NULL ” && EX y: addr,
  &(x # "cnf_list" ->ₛ "size") # Int |-> 3%Z **
  &(x # "cnf_list" ->ₛ "clause") # Ptr |-> y **
  IntArray.full y 3%Z clause.

(* Module cnf_list_store_lists. *)
Lemma store_cnf_list_fold: forall x clause y,
  x <> NULL ->
  &(x # "cnf_list" ->ₛ "size") # Int |-> 3%Z **
  &(x # "cnf_list" ->ₛ "clause") # Ptr |-> y **
  IntArray.full y 3%Z clause |--
  store_cnf_list_cell x clause.
Proof.
  intros.
  unfold store_cnf_list_cell.
  Exists y.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Definition sll_cnf_list (x: addr) (l: cnf_list): Assertion :=
  sll store_cnf_list_cell "cnf_list" "next" x l.

Definition sllseg_cnf_list (x: addr) (y: addr) (l: cnf_list): Assertion :=
  sllseg store_cnf_list_cell "cnf_list" "next" x y l.

Definition sllbseg_cnf_list (x: addr) (y: addr) (l: cnf_list): Assertion :=
  sllbseg store_cnf_list_cell "cnf_list" "next" x y l.

(* End cnf_list_store_lists. *)

(* Import cnf_list_store_lists. *)

(* Definition Z_union (l1 l2 : list Z) : list Z :=
  nodup Z.eq_dec (l1 ++ l2).

Fixpoint all_vars (l: cnf_list): list Z :=
  match l with
    | nil => nil
    | (CNFCell size clause) :: l0 => Z_union clause (all_vars l0)
  end.

Definition all_vars_cnt (l: cnf_list): Z :=
  Zlength (all_vars l). *)

Fixpoint max_element (l: list Z): Z :=
  match l with
    | nil => 0%Z
    | h :: t => Z.max h (max_element t)
  end.

Fixpoint min_element (l: list Z): Z :=
  match l with
    | nil => 0%Z
    | h :: t => Z.min h (min_element t)
  end.
  
Fixpoint max_cnf (l: cnf_list): Z :=
  match l with
    | nil => 0%Z
    | clause :: t => Z.max (max_element clause) (max_cnf t)
  end.

Fixpoint min_cnf (l: cnf_list): Z :=
  match l with
    | nil => 0%Z
    | clause :: t => Z.min (min_element clause) (min_cnf t)
  end.

Definition prop_cnt_inf (l: cnf_list): Z :=
  Z.max (max_cnf l) (Z.abs (min_cnf l)).

Definition prop_cnt_nneg: forall l, prop_cnt_inf l >= 0%Z.
Proof.
  intros.
  unfold prop_cnt_inf.
  assert (forall a b, b >= 0 -> Z.max a b >= 0). {
    intros.
    destruct (Z_ge_dec a b).
    + assert (Z.max a b = a) by lia.
      lia.
    + assert (Z.max a b = b) by lia.
      lia.
  }
  apply H.
  lia.
Qed.

Definition store_predata (x: addr) (cnf_res: cnf_list) (prop_cnt clause_cnt: Z): Assertion :=
 “ x <> NULL ” && “ Zlength cnf_res = clause_cnt ” &&
 “ prop_cnt_inf cnf_res <= prop_cnt ” &&
  EX y: addr,
    &(x # "PreData" ->ₛ "cnf_res") # Ptr |-> y **
    &(x # "PreData" ->ₛ "prop_cnt") # Int |-> prop_cnt **
    &(x # "PreData" ->ₛ "clause_cnt") # Int |-> clause_cnt **
    sll_cnf_list y cnf_res.

(* Definition  (l: list Z): cnf_list_cell :=
  CNFCell 3 l. *)

Notation "x <>? y" := (negb (Z.eqb x y)) (at level 70).
Notation "x ==? y" := (Z.eq_dec x y) (at level 70).

(* Import smt_lang_enums1. *)

(* p3 <-> (p1 op p2) to cnf *)
Definition iff2cnf_binary (p1 p2 p3: Z) (op: SmtPropBop): cnf_list :=
  match op with
    | SMTPROP_AND => let c1 := [p1; -p3; 0] in
            let c2 := [p2; -p3; 0] in
              let c3 := if (p1 ==? p2) then [-p1; p3; 0] else [-p1; -p2; p3] in
                c1 :: c2 :: c3 :: nil
    | SMTPROP_OR => let c1 := [-p1; p3; 0] in
            let c2 := [-p2; p3; 0] in
              let c3 := if (p1 ==? p2) then [p1; -p3; 0] else [p1; p2; -p3] in
                c1 :: c2 :: c3 :: nil
    | SMTPROP_IMPLY => if (p1 ==? p2) then
              ( (p3 :: 0 :: 0 :: nil)) :: nil
           else
            let c1 := [p1; p3; 0] in
              let c2 := [-p2; p3; 0] in
                let c3 := [-p1; p2; -p3] in
                  c1 :: c2 :: c3 :: nil

    | SMTPROP_IFF => if (p1 ==? p2) then
            ( (p3 :: 0 :: 0 :: nil)) :: nil
           else
            let c1 := [p1; p2; p3] in
              let c2 := [-p1; -p2; p3] in
                let c3 := [p1; -p2; -p3] in
                  let c4 := [-p1; p2; -p3] in
                    c1 :: c2 :: c3 :: c4 :: nil
  end.

Definition iff2cnf_length_binary (p1 p2 p3: Z) (op: SmtPropBop): Z :=
  match op with
    | SMTPROP_AND => 3%Z
    | SMTPROP_OR => 3%Z
    | SMTPROP_IMPLY => if (p1 ==? p2) then 1%Z else 3%Z
    | SMTPROP_IFF => if (p1 ==? p2) then 1%Z else 4%Z
  end.

Lemma iff2cnf_binary_and:
  forall p1 p2 p3,
    iff2cnf_binary p1 p2 p3 SMTPROP_AND =
    [p1; -p3; 0] :: [p2; -p3; 0] :: (if (p1 ==? p2) then [-p1; p3; 0] else [-p1; -p2; p3]) :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_AND = 3%Z.
Proof.
  intros.
  split; reflexivity.
Qed.

Lemma iff2cnf_binary_and_eq:
  forall p1 p2 p3,
    p1 = p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_AND =
    [p1; -p3; 0] :: [p2; -p3; 0] :: [-p1; p3; 0] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_AND = 3%Z.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_binary_and_neq:
  forall p1 p2 p3,
    p1 <> p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_AND =
    [p1; -p3; 0] :: [p2; -p3; 0] :: [-p1; -p2; p3] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_AND = 3%Z.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_binary_or:
  forall p1 p2 p3,
    iff2cnf_binary p1 p2 p3 SMTPROP_OR =
    [-p1; p3; 0] :: [-p2; p3; 0] :: (if (p1 ==? p2) then [p1; -p3; 0] else [p1; p2; -p3]) :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_OR = 3%Z.
Proof.
  intros.
  split; reflexivity.
Qed.

Lemma iff2cnf_binary_or_eq:
  forall p1 p2 p3,
    p1 = p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_OR =
    [-p1; p3; 0] :: [-p2; p3; 0] :: [p1; -p3; 0] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_OR = 3%Z.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_binary_or_neq:
  forall p1 p2 p3,
    p1 <> p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_OR =
    [-p1; p3; 0] :: [-p2; p3; 0] :: [p1; p2; -p3] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_OR = 3%Z.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_binary_imply_eq:
  forall p1 p2 p3,
    p1 = p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_IMPLY = [p3; 0; 0] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_IMPLY = 1%Z.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_binary_imply_neq:
  forall p1 p2 p3,
    p1 <> p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_IMPLY =
    [p1; p3; 0] :: [-p2; p3; 0] :: [-p1; p2; -p3] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_IMPLY = 3%Z.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_binary_iff_eq:
  forall p1 p2 p3,
    p1 = p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_IFF = [p3; 0; 0] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_IFF = 1%Z.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_binary_iff_neq:
  forall p1 p2 p3,
    p1 <> p2 ->
    iff2cnf_binary p1 p2 p3 SMTPROP_IFF =
    [p1; p2; p3] :: [-p1; -p2; p3] :: [p1; -p2; -p3] :: [-p1; p2; -p3] :: nil /\
    iff2cnf_length_binary p1 p2 p3 SMTPROP_IFF = 4%Z. 
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  split; destruct (p1 ==? p2); try reflexivity; try lia.
Qed.

Lemma iff2cnf_length_eq:
  forall p1 p2 p3 op,
    Zlength (iff2cnf_binary p1 p2 p3 op) = iff2cnf_length_binary p1 p2 p3 op.
Proof.
  intros.
  unfold iff2cnf_binary, iff2cnf_length_binary, Zlength.
  destruct op; simpl; try reflexivity.
  + destruct (p1 ==? p2); simpl; try reflexivity; try lia.
  + destruct (p1 ==? p2); simpl; try reflexivity; try lia.
Qed.

(* Definition iff2cnf_binary (p1 p2 p3: Z) (op: Z): cnf_list :=
  match op with
    | 0 => let c1 := [p1; -p3] in
            let c2 := [p2; -p3] in
              let c3 := if (p1 ==? p2) then [-p1; p3] else [-p1; -p2; p3] in
                c1 :: c2 :: c3 :: nil
    | 1 => let c1 := [-p1; p3] in
            let c2 := [-p2; p3] in
              let c3 := if (p1 ==? p2) then [p1; -p3] else [p1; p2; -p3] in
                c1 :: c2 :: c3 :: nil
    | 2 => if (p1 ==? p2) then
              ( (p3 :: nil)) :: nil
            else
            let c1 := [p1; p3] in
              let c2 := [-p2; p3] in
                let c3 := [-p1; p2; -p3] in
                  c1 :: c2 :: c3 :: nil

    | 3 => if (p1 ==? p2) then
            ( (p3 :: nil)) :: nil
            else
            let c1 := [p1; p2; p3] in
              let c2 := [-p1; -p2; p3] in
                let c3 := [p1; -p2; -p3] in
                  let c4 := [-p1; p2; -p3] in
                    c1 :: c2 :: c3 :: c4 :: nil
    | _ => nil
  end.

Definition iff2cnf_length_binary (p1 p2 p3: Z) (op: Z): Z :=
  match op with
    | 0 => 3%Z
    | 1 => 3%Z
    | 2 => if (p1 ==? p2) then 1%Z else 3%Z
    | 3 => if (p1 ==? p2) then 1%Z else 4%Z
    | _ => 0%Z
  end. *)

Definition iff2cnf_unary (p2 p3: Z): cnf_list :=
  let c1 := [p2; p3; 0] in
    let c2 := [-p2; -p3; 0] in
      c1 :: c2 :: nil.

  (* 0 => AND
     1 => OR
     2 => IMPLY
     3 => IFF
     4 => NOT *)

Fixpoint max_var_SmtProp (s: smt_prop): Z :=
  match s with
    | SmtB op lt rt => Z.max (max_var_SmtProp lt) (max_var_SmtProp rt)
    | SmtU op prop => max_var_SmtProp prop
    | SmtV var => var
  end.

Fixpoint min_var_SmtProp (s: smt_prop): Z :=
  match s with
    | SmtB op lt rt => Z.min (min_var_SmtProp lt) (min_var_SmtProp rt)
    | SmtU op prop => min_var_SmtProp prop
    | SmtV var => var
  end.

Lemma min_le_max_var_SmtProp: forall s,
  min_var_SmtProp s <= max_var_SmtProp s.
Proof.
  intros.
  induction s; simpl; try lia.
Qed.

Definition prop_cnt_inf_SmtProp (s: smt_prop): Z :=
  Z.max (max_var_SmtProp s) (Z.abs (min_var_SmtProp s)).

Lemma prop_cnt_inf_var: forall var,
  prop_cnt_inf_SmtProp (SmtV var) = Z.abs var.
Proof.
  unfold prop_cnt_inf_SmtProp.
  intros.
  unfold max_var_SmtProp, min_var_SmtProp.
  lia.
Qed.

Lemma prop_cnt_inf_Binary_l: forall op lt rt pcnt,
  prop_cnt_inf_SmtProp (SmtB op lt rt) <= pcnt ->
  prop_cnt_inf_SmtProp lt <= pcnt.
Proof.
  unfold prop_cnt_inf_SmtProp.
  intros.
  apply Z.max_lub.
  + pose proof Z.max_lub_l _ _ _ H.
    simpl max_var_SmtProp in H0.
    pose proof Z.max_lub_l _ _ _ H0.
    easy.
  + pose proof Z.max_lub_r _ _ _ H.
    simpl max_var_SmtProp in H0.
    pose proof Z.abs_le (min_var_SmtProp (SmtB op lt rt)) pcnt.
    destruct H1.
    clear H2.
    specialize (H1 H0).
    simpl in H1.
    destruct H1.
    apply Z.abs_le.
    split.
    pose proof Z.min_glb_l _ _ _ H1.
    easy.
    pose proof min_le_max_var_SmtProp lt.
    pose proof Z.max_lub_l _ _ _ H.
    simpl max_var_SmtProp in H4.
    pose proof Z.max_lub_l _ _ _ H4.
    lia.
Qed.

Lemma prop_cnt_inf_Binary_r: forall op lt rt pcnt,
  prop_cnt_inf_SmtProp (SmtB op lt rt) <= pcnt ->
  prop_cnt_inf_SmtProp rt <= pcnt.
Proof.
  unfold prop_cnt_inf_SmtProp.
  intros.
  apply Z.max_lub.
  + pose proof Z.max_lub_l _ _ _ H.
    simpl max_var_SmtProp in H0.
    pose proof Z.max_lub_r _ _ _ H0.
    easy.
  + pose proof Z.max_lub_r _ _ _ H.
    simpl max_var_SmtProp in H0.
    pose proof Z.abs_le (min_var_SmtProp (SmtB op lt rt)) pcnt.
    destruct H1.
    clear H2.
    specialize (H1 H0).
    simpl in H1.
    destruct H1.
    apply Z.abs_le.
    split.
    pose proof Z.min_glb_r _ _ _ H1.
    easy.
    pose proof min_le_max_var_SmtProp rt.
    pose proof Z.max_lub_l _ _ _ H.
    simpl max_var_SmtProp in H4.
    pose proof Z.max_lub_r _ _ _ H4.
    lia.
Qed.

Lemma prop_cnt_inf_Unary_r: forall op prop pcnt,
  prop_cnt_inf_SmtProp (SmtU op prop) <= pcnt ->
  prop_cnt_inf_SmtProp prop <= pcnt.
Proof.
  unfold prop_cnt_inf_SmtProp.
  intros.
  apply Z.max_lub.
  + pose proof Z.max_lub_l _ _ _ H.
    simpl max_var_SmtProp in H0.
    easy.
  + pose proof Z.max_lub_r _ _ _ H.
    simpl min_var_SmtProp in H0.
    easy.
Qed.

Definition PreData : Type := cnf_list * Z * Z.
Definition prop2cnf_ret : Type := PreData * Z.

Definition make_predata (cnf_res: cnf_list) (prop_cnt clause_cnt: Z): PreData :=
  (cnf_res, prop_cnt, clause_cnt).

Definition make_prop2cnf_ret (data: PreData) (ret: Z): prop2cnf_ret :=
  (data, ret).

Fixpoint prop2cnf_logic (s: smt_prop) (data: PreData): prop2cnf_ret :=
  match s with
    | SmtB op lt rt =>
      let (data1, p1) := prop2cnf_logic lt data in
      let (data2, p2) := prop2cnf_logic rt data1 in
      let (tmp, clause_cnt) := data2 in
      let (cnf_res, prop_cnt) := tmp in
      let cnf_gen := (iff2cnf_binary p1 p2 (prop_cnt + 1) op) in
      let len_gen := (iff2cnf_length_binary p1 p2 (prop_cnt + 1) op) in
      let data_ret := ((app cnf_gen cnf_res), (prop_cnt + 1), (clause_cnt + len_gen)) in
      (data_ret, prop_cnt + 1)

    | SmtU op prop =>
      let (data1, p1) := prop2cnf_logic prop data in
      let (tmp, clause_cnt) := data1 in
      let (cnf_res, prop_cnt) := tmp in
      let cnf_gen := (iff2cnf_unary p1 (prop_cnt + 1)) in
      let data_ret := ((app cnf_gen cnf_res), (prop_cnt + 1), (clause_cnt + 2)) in
      (data_ret, prop_cnt + 1)

    | SmtV var => (data, var)
  end.

Lemma pcnt_upper_incr: forall prop clist' pcnt' ccnt' res' clist pcnt ccnt,
  (clist', pcnt', ccnt', res') = prop2cnf_logic prop (clist, pcnt, ccnt)
  -> pcnt <= pcnt'.
Proof.
  intro prop.
  induction prop; intros.
  + simpl in H.
    remember (prop2cnf_logic prop1 (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1].
    remember (prop2cnf_logic prop2 data1) as step2 eqn:Hstep2.
    destruct step2 as [data2 p2].
    destruct data2 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    destruct data1 as [tmp'' ccnt'_1].
    destruct tmp'' as [clist'_1 pcnt'_1].
    inversion H.
    specialize (IHprop2  _ _ _ _ _ _ _ Hstep2).
    specialize (IHprop1  _ _ _ _ _ _ _ Hstep1).
    lia.
  + simpl in H.
    remember (prop2cnf_logic prop (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1].
    destruct data1 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    inversion H.
    specialize (IHprop  _ _ _ _ _ _ _ Hstep1).
    lia.
  + simpl in H.
    inversion H.
    lia.
Qed.

Lemma iff2cnf_length_binary_upper_bound : forall p1 p2 p3 op,
  iff2cnf_length_binary p1 p2 p3 op <= 4.
Proof.
  intros.
  destruct op; simpl; destruct (p1 ==? p2); try lia.
Qed.


Lemma ccnt_upper_bound: forall prop clist' pcnt' ccnt' res' clist pcnt ccnt,
  (clist', pcnt', ccnt', res') = prop2cnf_logic prop (clist, pcnt, ccnt)
  -> ccnt' <= ccnt + 4 * SmtProp_size prop.
Proof.
  intro prop.
  induction prop.
  + intros.
    simpl in H.
    remember (prop2cnf_logic prop1 (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1].
    remember (prop2cnf_logic prop2 data1) as step2 eqn:Hstep2.
    destruct step2 as [data2 p2].
    destruct data2 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    destruct data1 as [tmp'' ccnt'_1].
    destruct tmp'' as [clist'_1 pcnt'_1].
    inversion H.
    specialize (IHprop2  _ _ _ _ _ _ _ Hstep2).
    specialize (IHprop1  _ _ _ _ _ _ _ Hstep1).
    assert (SmtProp_size (SmtB op prop1 prop2) = 1 + SmtProp_size prop1 + SmtProp_size prop2) as Hsize.
    {
      unfold SmtProp_size.
      simpl.
      lia.
    }
    rewrite Hsize.
    assert (clause_cnt <= 4 * SmtProp_size prop2 + 4 * SmtProp_size prop1 + ccnt) by lia.
    pose proof iff2cnf_length_binary_upper_bound p1 p2 (prop_cnt + 1) op as Hlen.
    lia.
  + intros.
    simpl in H.
    remember (prop2cnf_logic prop (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1].
    destruct data1 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    inversion H.
    specialize (IHprop  _ _ _ _ _ _ _ Hstep1).
    assert (SmtProp_size (SmtU op prop) = 1 + SmtProp_size prop) as Hsize.
    {
      unfold SmtProp_size.
      simpl.
      lia.
    }
    rewrite Hsize.
    lia.
  + intros.
    simpl in H.
    inversion H.
    simpl.
    lia.
Qed.

Lemma clist_upper_bound: forall prop clist' pcnt' ccnt' res' clist pcnt ccnt,
  (clist', pcnt', ccnt', res') = prop2cnf_logic prop (clist, pcnt, ccnt)
  -> Zlength clist' <= Zlength clist + 4 * SmtProp_size prop.
Proof.
  intro prop.
  induction prop; intros.
  + simpl in H.
    remember (prop2cnf_logic prop1 (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1].
    remember (prop2cnf_logic prop2 data1) as step2 eqn:Hstep2.
    destruct step2 as [data2 p2].
    destruct data2 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    destruct data1 as [tmp'' ccnt'_1].
    destruct tmp'' as [clist'_1 pcnt'_1].
    inversion H.
    specialize (IHprop2  _ _ _ _ _ _ _ Hstep2).
    specialize (IHprop1  _ _ _ _ _ _ _ Hstep1).
    assert (SmtProp_size (SmtB op prop1 prop2) = 1 + SmtProp_size prop1 + SmtProp_size prop2) as Hsize.
    {
      unfold SmtProp_size.
      simpl.
      lia.
    }
    rewrite Hsize.
    assert (Zlength cnf_res <= Zlength clist + 4 * SmtProp_size prop2 + 4 * SmtProp_size prop1) by lia.
    rewrite Zlength_app.
    rewrite iff2cnf_length_eq.
    pose proof iff2cnf_length_binary_upper_bound p1 p2 (prop_cnt + 1) op as Hlen.
    lia.
  + simpl in H.
    remember (prop2cnf_logic prop (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1].
    destruct data1 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    inversion H.
    specialize (IHprop  _ _ _ _ _ _ _ Hstep1).
    repeat rewrite Zlength_cons.
    assert (SmtProp_size (SmtU op prop) = 1 + SmtProp_size prop) as Hsize.
    {
      unfold SmtProp_size.
      simpl.
      lia.
    }
    rewrite Hsize.
    lia.
  + simpl in H.
    inversion H.
    simpl.
    lia.
Qed.

Lemma all_zero_list_3:
  all_zero_list 3 = [0; 0; 0].
Proof.
  unfold all_zero_list.
  simpl.
  reflexivity.
Qed.

Lemma replace_0th:
  forall (a b c v: Z),
    replace_Znth 0 v [a; b; c] = [v; b; c].
Proof.
  intros.
  unfold replace_Znth.
  simpl.
  reflexivity.
Qed.

Lemma replace_1st:
  forall (a b c v: Z),
    replace_Znth 1 v [a; b; c] = [a; v; c].
Proof.
  intros.
  unfold replace_Znth.
  simpl.
  reflexivity.
Qed.

Lemma replace_2nd:
  forall (a b c v: Z),
    replace_Znth 2 v [a; b; c] = [a; b; v].
Proof.
  intros.
  unfold replace_Znth.
  simpl.
  reflexivity.
Qed.
