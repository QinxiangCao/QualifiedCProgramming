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
From MonadLib.StateRelMonad Require Import StateRelMonad StateRelBasic StateRelHoare FixpointLib safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

From SimpleC.EE.Applications_human Require Import super_poly_sll2.
From SimpleC.EE.Applications_human Require Import malloc.

Import naive_C_Rules.
Local Open Scope sac.
Import MonadNotation.
Local Open Scope monad.

Definition var_name : Type := list Z.

(* all about ast basic structure *)

Inductive const_type : Type :=
  | CNum: const_type
  | CAdd: const_type
  | CMul: const_type
  | CEq: const_type
  | CLe: const_type
  | CAnd: const_type
  | COr: const_type
  | CImpl: const_type.

Inductive quant_type : Type :=
  | QForall: quant_type
  | QExists: quant_type.

Inductive term_type : Type :=
  | TVar: term_type
  | TConst: term_type
  | TApply: term_type
  | TQuant: term_type.
  
Definition ctID (t: const_type) :=
  match t with
    | CNum => 0%Z
    | CAdd => 1%Z
    | CMul => 2%Z
    | CEq => 3%Z
    | CLe => 4%Z
    | CAnd => 5%Z
    | COr => 6%Z
    | CImpl => 7%Z
  end.
  
Definition qtID (t: quant_type) :=
  match t with
    | QForall => 0%Z
    | QExists => 1%Z
  end.

Definition ttID (t: term_type) :=
  match t with
    | TVar => 0%Z
    | TConst => 1%Z
    | TApply => 2%Z
    | TQuant => 3%Z
  end.

Inductive term : Type :=
  | TermVar (var: var_name): term
  | TermConst (ctype: const_type) (content: Z): term
  | TermApply (lt: term) (rt: term): term
  | TermQuant (qtype: quant_type) (qvar: var_name) (body: term): term.

Definition term_list : Type := list term.

Definition termtypeID (t: term) : Z :=
  match t with
    | TermVar _ => 0%Z
    | TermConst _ _ => 1%Z
    | TermApply _ _ => 2%Z
    | TermQuant _ _ _ => 3%Z
  end.

(* Definition zlength {A: Type} (l: list A) : Z :=
  Z.of_nat (List.length l). *)

Definition store_string (x: addr) (str: var_name): Assertion :=
  EX n: Z,
  “ x <> NULL ” &&
  “ n >= 0 ” &&
  CharArray.full x (Zlength (str ++ (all_zero_list n))) (str ++ (all_zero_list n)).

Fixpoint store_term (x: addr) (t: term): Assertion :=
  “ x <> NULL ” && &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  match t with
    | TermVar var => EX y: addr,
                    &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
                    store_string y var
    | TermConst ctype content => &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
                                &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content
    | TermApply lt rt => EX y z: addr,
                        &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
                        &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
                        store_term y lt ** store_term z rt
    | TermQuant qtype qvar body => EX y z: addr,
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                  store_string y qvar ** store_term z body
  end.

Definition store_term' (x: addr) (t: term): Assertion :=
  match t with
    | TermVar var => EX y: addr,
                      &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
                      store_string y var
    | TermConst ctype content => &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
                                 &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content
    | TermApply lt rt => EX y z: addr,
                          &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
                          &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
                          store_term y lt ** store_term z rt
    | TermQuant qtype qvar body => EX y z: addr,
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                    store_string y qvar ** store_term z body
  end.

Lemma store_term_unfold: forall x t,
  store_term x t |--
  “ x <> NULL ” &&
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t.
Proof.
  intros.
  unfold store_term, store_term'.
  destruct t; fold store_term; entailer!.
Qed.

Lemma store_term_fold: forall x t,
  “ x <> NULL ” &&
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t |--
  store_term x t.
Proof.
  intros.
  unfold store_term, store_term'.
  destruct t; fold store_term; entailer!.
Qed.

Lemma store_null: forall t q,
  store_term 0 t |-- q.
Proof.
  intros.
  pose proof (store_term_unfold 0 t).
  unfold NULL.
  sep_apply H.
  entailer!.
Qed.

Lemma store_null_left: forall t p q,
  store_term 0 t ** p |-- q.
Proof.
  intros.
  pose proof (store_term_unfold 0 t).
  unfold NULL.
  sep_apply H.
  entailer!.
Qed.

Lemma store_null_right: forall t p q,
  p ** store_term 0 t |-- q.
Proof.
  intros.
  pose proof (store_term_unfold 0 t).
  unfold NULL.
  sep_apply H.
  entailer!.
Qed.

Lemma store_null_lr: forall t p q r,
  p ** store_term 0 t ** r |-- q.
Proof.
  intros.
  pose proof (store_term_unfold 0 t).
  sep_apply H.
  entailer!.
Qed.

Lemma store_term_fold_out: forall x t,
  x <> 0 ->
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t |--
  store_term x t.
Proof.
  intros.
  unfold store_term, store_term', NULL.
  destruct t; fold store_term.
  Intros y.
  Exists y.
  entailer!.
  entailer!.
  entailer!.
  Intros y z.
  Exists y z.
  entailer!.
  Intros y z.
  Exists y z.
  entailer!.
Qed.

Lemma store_term'_Var: forall x t,
  termtypeID t = 0%Z ->
  x <> NULL ->
  store_term' x t |--
  EX var, “ t = TermVar var ” && “ x <> NULL ” &&
  EX y: addr,
    &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
    store_string y var.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y.
  Exists var y.
  entailer!.
Qed.

Lemma store_term'_Const: forall x t,
  termtypeID t = 1%Z ->
  x <> NULL ->
  store_term' x t |--
  EX ctype content, “ t = TermConst ctype content ” && “ x <> NULL ” &&
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros.
  Exists ctype content.
  entailer!.
Qed.

Lemma store_term'_Apply: forall x t,
  termtypeID t = 2%Z ->
  x <> NULL ->
  store_term' x t |--
  EX lt rt, “ t = TermApply lt rt ” && “ x <> NULL ” &&
  EX y z: addr,
    &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
    &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ  "right") # Ptr |-> z **
    store_term y lt ** store_term z rt.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y z.
  Exists t1 t2 y z.
  entailer!.
Qed.

Lemma store_term'_Quant: forall x t,
  termtypeID t = 3%Z ->
  x <> NULL ->
  store_term' x t |--
  EX qtype qvar body, “ t = TermQuant qtype qvar body ” && “ x <> NULL ” &&
  EX y z: addr,
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
    store_string y qvar ** store_term z body.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y z.
  Exists qtype qvar t y z.
  entailer!.
Qed.

Definition store_term_cell (x: addr) (t: term): Assertion :=
  “ x <> NULL ” &&
  EX y: addr,
    &(x # "term_list" ->ₛ "element") # Ptr |-> y **
    store_term y t.

Definition sll_term_list (x: addr) (l: term_list): Assertion :=
  sll store_term_cell "term_list" "next" x l.

Definition sllseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllseg store_term_cell "term_list" "next" x y l.

Definition sllbseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllbseg store_term_cell "term_list" "next" x y l.
    

(* all about ast var_sub *)

Inductive var_sub : Type :=
  | VarSub (name: var_name) (t: term): var_sub.

Definition var_sub_list : Type := list var_sub.


(* Definition var_sub_list : Type := list var_sub. *)
(* v is stored on addr x *)
Definition store_var_sub (x: addr) (v: var_sub): Assertion :=
  match v with
    | VarSub name term => “ x <> NULL ” &&
                          EX y z: addr,
                           &(x # "var_sub" ->ₛ "var") # Ptr |-> y **
                           &(x # "var_sub" ->ₛ "sub_term") # Ptr |-> z **
                           store_string y name ** store_term z term
  end.

(* the linked list node stores the var_sub type addr *)
Definition store_var_sub_cell (x: addr) (v: var_sub): Assertion :=
  “ x <> NULL ” &&
  EX y: addr, 
    &(x # "var_sub_list" ->ₛ "cur") # Ptr |-> y **
    store_var_sub y v.

Definition sll_var_sub_list (x: addr) (l: var_sub_list): Assertion :=
  sll store_var_sub_cell "var_sub_list" "next" x l.

Definition sllseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllseg store_var_sub_cell "var_sub_list" "next" x y l.

Definition sllbseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllbseg store_var_sub_cell "var_sub_list" "next" x y l.

Lemma sll_var_sub_list_fold: forall x y l0 sy sz sv st n,
  x <> NULL -> y <> NULL ->
  &(x # "var_sub_list" ->ₛ "cur") # Ptr |-> y **
  &(y # "var_sub" ->ₛ "var") # Ptr |-> sy **
  &(y # "var_sub" ->ₛ "sub_term") # Ptr |-> sz **
  &(x # "var_sub_list" ->ₛ "next") # Ptr |-> n **
  store_term sz st ** store_string sy sv ** sll_var_sub_list n l0 |--
  sll_var_sub_list x ((VarSub sv st) :: l0).
Proof.
  intros.
  unfold sll_var_sub_list.
  unfold sll at 2.
  Exists n.
  unfold sll at 1.
  entailer!.
  unfold store_var_sub_cell.
  Exists y.
  unfold store_var_sub.
  Exists sy sz.
  entailer!.
Qed.

Lemma sll_var_sub_list_unfold: forall lis l,
  lis <> NULL ->
  sll_var_sub_list lis l |--
  EX n c vs l0 ,
  “ l = vs :: l0 ” &&
  &(lis # "var_sub_list" ->ₛ "cur") # Ptr |-> c **
  store_var_sub c vs **
  &(lis # "var_sub_list" ->ₛ "next") # Ptr |-> n ** 
  sll_var_sub_list n l0.
Proof.
  intros.
  unfold sll_var_sub_list.
  unfold sll.
  destruct l.
  + entailer!.
  + unfold store_var_sub_cell.
    Intros y y0.
    Exists y y0 v l.
    entailer!.
Qed.


(* all about ast solve result *)

Inductive res_type : Type :=
  | BoolRes: res_type
  | TermList: res_type.

Inductive solve_res : Type :=
  | SRBool (ans: Z): solve_res
  | SRTList (l: term_list): solve_res.


Definition restypeID (sr : solve_res) : Z :=
  match sr with
    | SRBool _ => 0%Z
    | SRTList _ => 1%Z
  end.

Definition store_solve_res (x: addr) (sr: solve_res): Assertion :=
  “ x <> NULL ” && &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  match sr with
    | SRBool ans => &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Int |-> ans
    | SRTList l => EX y: addr,
                   &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> y **
                   sll_term_list y l
  end.

Definition store_solve_res' (x: addr) (sr: solve_res): Assertion :=
  match sr with
    | SRBool ans => “ x <> NULL ” && &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Int |-> ans
    | SRTList l => “ x <> NULL ” && EX y: addr,
                   &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> y **
                   sll_term_list y l
  end.

Axiom store_solve_res'_equiv : forall x v, 
  &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Int |-> v --||-- 
  &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> v.

Lemma store_solve_res_unfold: forall x sr,
  store_solve_res x sr |--
  &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  store_solve_res' x sr.
Proof.
  intros.
  unfold store_solve_res, store_solve_res'.
  destruct sr; fold store_solve_res; entailer!.
Qed.

Lemma store_solve_res_fold: forall x sr,
  &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  store_solve_res' x sr |--
  store_solve_res x sr.
Proof.
  intros.
  unfold store_solve_res, store_solve_res'.
  destruct sr; fold store_solve_res; entailer!.
Qed.

Lemma store_solve_res'_Bool: forall x sr,
  restypeID sr = 0%Z ->
  store_solve_res' x sr |--
  EX ans, “ sr = SRBool ans ” && “ x <> NULL ” &&
  &(x # "solve_res" ->ₛ "d" .ₛ "ans") # Int |-> ans.
Proof.
  intros.
  unfold store_solve_res'.
  induction sr; try discriminate.
  Intros.
  Exists ans.
  entailer!.
Qed.

Lemma store_solve_res'_List: forall x sr,
  restypeID sr = 1%Z ->
  store_solve_res' x sr |--
  EX l, “ sr = SRTList l ” && “ x <> NULL ” &&
  EX y: addr,
    &(x # "solve_res" ->ₛ "d" .ₛ "list") # Ptr |-> y **
    sll_term_list y l.
Proof.
  intros.
  unfold store_solve_res'.
  induction sr; try discriminate.
  Intros y.
  Exists l y.
  entailer!.
Qed.

(* all about ImplyProp *)

Inductive ImplyProp : Type :=
  | ImplP (assum: term) (concl: term): ImplyProp.

Definition store_ImplyProp (x y z: addr) (assum concl: term): Assertion :=
  “ x <> NULL ” &&
  &(x # "imply_prop" ->ₛ "assum") # Ptr |-> y **
  &(x # "imply_prop" ->ₛ "concl") # Ptr |-> z **
  store_term y assum ** store_term z concl.

(* about list Z *)

Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => Z.eqb x1 x2 && list_Z_eqb t1 t2
  | _, _ => false
  end.

Definition list_Z_cmp (l1 l2 : list Z) : Z :=
  if list_Z_eqb l1 l2 then 0 else 1.

Lemma list_Z_eqb_eq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = true <-> l1 = l2.
Proof. 
  induction l1.
  + intros.
    destruct l2; [ split; try reflexivity | split; try discriminate ].
  + intros.
    destruct l2; [ split; try discriminate | split ].
    - unfold list_Z_eqb.
      fold list_Z_eqb.
      rewrite andb_true_iff.
      intros.
      destruct H as [Ha Hl].
      rewrite Z.eqb_eq in Ha.
      pose proof IHl1 l2.
      destruct H.
      pose proof H Hl.
      rewrite Ha, H1.
      reflexivity.
    - intros.
      injection H.
      intros.
      unfold list_Z_eqb.
      fold list_Z_eqb.
      rewrite andb_true_iff.
      pose proof IHl1 l2.
      destruct H2.
      pose proof H3 H0.
      split; [ | auto].
      rewrite Z.eqb_eq.
      auto.
Qed.

Lemma list_Z_eqb2eq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = true -> l1 = l2.
Proof.
  apply list_Z_eqb_eq.
Qed. 

Lemma list_Z_eq2eqb : forall l1 l2 : list Z,
  l1 = l2 -> list_Z_eqb l1 l2 = true.
Proof.
  apply list_Z_eqb_eq.
Qed. 

Lemma list_Z_neqb_neq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = false <-> l1 <> l2.
Proof.
  intros l1 l2. split.
  + intros H Hcontra.
    pose proof list_Z_eq2eqb l1 l2 Hcontra; congruence.
  + intros H.
    destruct (list_Z_eqb l1 l2) eqn:E.
    - pose proof list_Z_eqb2eq l1 l2 E; congruence.
    - reflexivity.  
Qed.

Lemma list_Z_neqb2neq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = false -> l1 <> l2.
Proof.
  apply list_Z_neqb_neq.
Qed. 

Lemma list_Z_neq2neqb : forall l1 l2 : list Z,
  l1 <> l2 -> list_Z_eqb l1 l2 = false.
Proof.
  apply list_Z_neqb_neq.
Qed. 

Lemma list_Z_eqb_refl : forall (l : list Z),
  list_Z_eqb l l = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  reflexivity.
Qed.

Lemma list_Z_eqb_symm : forall (l1 l2 : list Z),
  list_Z_eqb l1 l2 = list_Z_eqb l2 l1.
Proof.
  intros.
  destruct (list_Z_eqb l1 l2) eqn:E.
  + pose proof list_Z_eqb2eq l1 l2 E.
    rewrite H; pose proof list_Z_eqb_refl l2; rewrite H0; auto.
  + pose proof list_Z_neqb2neq l1 l2 E.
    destruct (list_Z_eqb l2 l1) eqn:Heq.
    - pose proof list_Z_eqb2eq l2 l1 Heq; congruence.
    - auto.
Qed.

Lemma list_Z_eqb_trans : forall (l1 l2 l3 : list Z),
  list_Z_eqb l1 l2 = true ->
  list_Z_eqb l2 l3 = true ->
  list_Z_eqb l1 l3 = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  pose proof list_Z_eqb2eq l1 l2 H.
  pose proof list_Z_eqb2eq l2 l3 H0.
  rewrite H1, H2.
  reflexivity.
Qed.

(* subst *)

Fixpoint term_subst_v (den src: var_name) (t: term): term :=
  match t with
    | TermVar v => if list_Z_eqb v src then TermVar den else TermVar v
    | TermConst ctype content => TermConst ctype content
    | TermApply lt rt => TermApply (term_subst_v den src lt) (term_subst_v den src rt)
    | TermQuant qtype qvar body =>
      if list_Z_eqb qvar src then
        TermQuant qtype qvar body
      else
        TermQuant qtype qvar (term_subst_v den src body)
  end.

Fixpoint term_subst_t (den: term) (src: var_name) (t: term): term :=
  match t with
    | TermVar v => if list_Z_eqb v src then den else TermVar v
    | TermConst ctype content => TermConst ctype content
    | TermApply lt rt => TermApply (term_subst_t den src lt) (term_subst_t den src rt)
    | TermQuant qtype qvar body =>
      if list_Z_eqb qvar src then
        TermQuant qtype qvar body
      else
        TermQuant qtype qvar (term_subst_t den src body)
  end.

(* alpha_equiv *)

Fixpoint term_alpha_eq (t1 t2 : term) : bool :=
  match t1, t2 with
  | TermVar v1, TermVar v2 => 
      if (list_Z_eqb v1 v2) then true else false
  | TermConst ctype1 content1, TermConst ctype2 content2 =>
      if Z.eqb (ctID ctype1) (ctID ctype2) then
        if Z.eqb (ctID ctype1) 0 then
          if Z.eqb content1 content2 then true else false
        else
          true
      else
        false
  | TermApply lt1 rt1, TermApply lt2 rt2 =>
      term_alpha_eq lt1 lt2 && term_alpha_eq rt1 rt2
  | TermQuant qtype1 qvar1 body1, TermQuant qtype2 qvar2 body2 =>
      if Z.eqb (qtID qtype1) (qtID qtype2) then
        term_alpha_eq body1 (term_subst_v qvar1 qvar2 body2)
      else
        false
  | _, _ => false
  end.

Definition term_alpha_eqn (t1 t2 : term) : Z :=
  if term_alpha_eq t1 t2 then 1 else 0.

(* thm_apply *)

Definition imply_res_Cont (assum concl: term) : option ImplyProp :=
  Some (ImplP assum concl).

Inductive partial_quant: Type :=
  | NQuant : partial_quant
  | PQuant (qt: quant_type) (x: var_name) (pq: partial_quant) : partial_quant.

Fixpoint store_partial_quant (rt fin: addr) (pq: partial_quant) : Assertion :=
  match pq with
  | NQuant => “ rt = fin ” && emp
  | PQuant qt x t => EX y z: addr,
                “ rt <> NULL ” && 
                &(rt # "term" ->ₛ "type") # Int |-> 3 ** 
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt **
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                &(rt # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                store_string y x ** store_partial_quant z fin t
  end.

Lemma store_partial_quant_fold: forall thm_pre retval_2 retval pq qt qvar qterm y,
  thm_pre <> NULL ->
  store_partial_quant retval_2 retval pq ** 
  &( thm_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt qvar qterm) **
  &( thm_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt **
  &( thm_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
  &( thm_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> retval_2 ** 
  store_string y qvar
  |-- store_partial_quant thm_pre retval (PQuant qt qvar pq).
Proof.
  intros.
  unfold store_partial_quant at 2.
  Exists y retval_2.
  fold store_partial_quant.
  entailer!.
Qed.

Definition store_term_res (x: addr) (t: option term): Assertion :=
  match t with
  | Some ti => store_term x ti
  | None => “ x = NULL ”
  end.

Fixpoint thm_subst_rem (thm: term) (l: var_sub_list): option partial_quant :=
  match l with 
    | nil => Some NQuant
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
            match thm_subst_rem body l0 with
            | Some p => Some (PQuant qt v' p)
            | None => None
            end
        | _ => None
      end
  end.

Fixpoint thm_subst (thm: term) (l: var_sub_list): option term :=
  match l with 
    | nil => Some thm
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
            thm_subst (term_subst_t t v body) l0
        | _ => None
      end
  end.

Fixpoint thm_subst' (thm: term) (l: var_sub_list): term :=
  match l with 
    | nil => thm
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
          TermQuant qt v' (thm_subst' (term_subst_t t v body) l0)
        | _ => thm
      end
  end.

Fixpoint thm_subst_allres (thm: term) (l: var_sub_list): option (partial_quant * term) :=
  match l with 
    | nil => Some (NQuant, thm)
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qt v' body =>
          match thm_subst_allres (term_subst_t t v body) l0 with
            | Some (pq, t) => Some (PQuant qt v' pq, t)
            | None => None
        end
        | _ => None
      end
  end.

Lemma thm_subst_allres_var: forall var a l0,
  thm_subst_allres (TermVar var) (a :: l0) = None.
Proof.
  intros.
  unfold thm_subst_allres.
  destruct a; reflexivity.
Qed.

Lemma thm_subst_allres_const: forall ct c a l0,
  thm_subst_allres (TermConst ct c) (a :: l0) = None.
Proof.
  intros.
  unfold thm_subst_allres.
  destruct a; reflexivity.
Qed.

Lemma thm_subst_allres_apply: forall lt rt a l0,
  thm_subst_allres (TermApply lt rt) (a :: l0) = None.
Proof.
  intros.
  unfold thm_subst_allres.
  destruct a; reflexivity.
Qed.

Lemma thm_subst'_var: forall var a l0,
  thm_subst' (TermVar var) (a :: l0) = TermVar var.
Proof.
  intros.
  unfold thm_subst'.
  destruct a; reflexivity.
Qed.

Lemma thm_subst'_const: forall ct c a l0,
  thm_subst' (TermConst ct c) (a :: l0) = TermConst ct c.
Proof.
  intros.
  unfold thm_subst'.
  destruct a; reflexivity.
Qed.

Lemma thm_subst'_apply: forall lt rt a l0,
  thm_subst' (TermApply lt rt) (a :: l0) = TermApply lt rt.
Proof.
  intros.
  unfold thm_subst'.
  destruct a; reflexivity.
Qed.

Definition store_sub_thm_res (rt fin: addr) (thm: term) (l: var_sub_list): Assertion :=
  match thm_subst_allres thm l with
    | None => “ fin = 0 ” && store_term rt (thm_subst' thm l)
    | Some (pq, t) => store_partial_quant rt fin pq ** store_term fin t
end.

Definition thm_subst_allres_rel (thm: term) (l: var_sub_list) (pq: partial_quant) (st: term): Prop :=
  thm_subst_allres thm l = Some (pq, st).

Lemma store_sub_thm_res_fold: forall retval_2 retval st sv qterm l0 thm_pre qt qvar y,
  thm_pre <> NULL ->
  store_sub_thm_res retval_2 retval (term_subst_t st sv qterm) l0 **
  &( thm_pre # "term" ->ₛ "type") # Int |-> termtypeID (TermQuant qt qvar qterm) **
  &( thm_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qt **
  &( thm_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
  &( thm_pre # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> retval_2 **
  store_string y qvar |--
  store_sub_thm_res thm_pre retval (TermQuant qt qvar qterm) (VarSub sv st :: l0).
Proof.
  intros.
  unfold store_sub_thm_res at 2.
  unfold thm_subst_allres; fold thm_subst_allres.
  unfold store_sub_thm_res.
  destruct (thm_subst_allres (term_subst_t st sv qterm) l0).
  + destruct p as [pq t].
    sep_apply store_partial_quant_fold ; try lia.
    entailer!.
  + unfold thm_subst' at 2; fold thm_subst'.
    unfold store_term; fold store_term.
    Exists y retval_2.
    entailer!.
Qed. 

Definition sep_impl (t : term): option ImplyProp :=
  match t with
    | TermApply (TermApply (TermConst CImpl c) r) tr => 
      Some (ImplP r tr)
    | _ => None
  end.

Definition store_imply_res (x: addr) (impl: option ImplyProp): Assertion :=
  match impl with
  | Some (ImplP assum concl) => EX y z,
              store_ImplyProp x y z assum concl
  | None => “ x = NULL ” && emp
  end.

Local Close Scope string.

Definition makepair (x : term) (p : list term): (term * (list term)) := (x, p).
Definition applyf {A B: Type} (f: A -> B) (a: A) := f a.

Definition check_list_gen_body:
  term * term * list term ->
  MONAD (CntOrBrk (term * term * list term) (term * list term)) :=
  fun '(thm, tar, l) =>
    if term_alpha_eq thm tar then
      ret (by_break (thm, l))
    else
      match sep_impl thm with 
      | Some (ImplP r tr) =>
        ret (by_continue (tr, tar, l ++ (r :: nil)))
      | None => ret (by_break (thm, nil))
      end.

Definition check_rel theo tar :=
  repeat_break check_list_gen_body (theo, tar, nil).

Definition check_from_mid_rel theo tar l :=
  repeat_break check_list_gen_body (theo, tar, l).

Definition get_list (x: term * list term): MONAD solve_res := 
  match x with
    | (_, lst) => ret (SRTList lst)
  end.

Definition thm_app: 
  term * var_sub_list * term ->
  MONAD (solve_res) :=
  fun '(t, l, g) =>
  match thm_subst_allres t l with
  | None => ret (SRBool 0)
  | Some (_, thm_ins) =>
      if (term_alpha_eq thm_ins g) then ret (SRBool 1)
      else x <- (check_rel thm_ins g) ;; get_list x
  end.

Definition thm_app_rel (thm : term) (l : var_sub_list) (goal : term) :=
  thm_app (thm, l, goal).

(* Lemmas *)

Local Open Scope string.

Lemma term_subst_v_same_name : forall (den src : var_name) (t : term),
  den = src ->
  term_subst_v den src t = t.
Proof.
  induction t.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    rewrite <- H.
    destruct list_Z_eqb eqn:Heq; [ | reflexivity].
    apply list_Z_eqb2eq in Heq.
    rewrite Heq; reflexivity.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    reflexivity.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    pose proof IHt1 H.
    pose proof IHt2 H.
    rewrite H0, H1; reflexivity.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    destruct (list_Z_eqb qvar src) eqn:Heq.
    - reflexivity.
    - pose proof IHt H; rewrite H0; reflexivity.
Qed.

Lemma thm_subst_nil: forall (t: term),
  thm_subst_allres t nil = Some (NQuant, t).
Proof.
  intros.
  unfold thm_subst_allres.
  reflexivity.
Qed.

Lemma sll_zero_right : forall (A : Type) P (storeA: addr -> A -> Assertion) s1 s2 l Q,
  l <> nil ->
  P ** sll storeA s1 s2 0 l |-- Q.
Proof.
  intros.
  unfold sll.
  destruct l.
  - contradiction.
  - unfold NULL.
    Intros y.
    contradiction.
Qed.

Lemma store_term_cell_fold: forall x y t,
  x <> NULL ->
  &(x # "term_list" ->ₛ "element") # Ptr |-> y **
  store_term y t |--
  store_term_cell x t.
Proof.
  intros.
  unfold store_term_cell.
  Exists y.
  entailer!.
Qed.

Lemma sllbseg_one: forall a y retval,
  retval <> NULL ->
  y # Ptr |-> retval **
  store_term_cell retval a |--
  sllbseg_term_list y &(retval # "term_list" ->ₛ "next") (a::nil).
Proof.
  unfold sllbseg_term_list, sllbseg.
  intros.
  Exists retval.
  entailer!.
Qed.

Lemma store_imply_res_zero: forall t,
  store_imply_res 0 (sep_impl t) |-- “ sep_impl t = None ” && “ 0 = NULL ” && emp.
Proof.
  intros.
  remember (sep_impl t) as r.
  unfold sep_impl in Heqr.
  destruct t; try simpl.
  + unfold store_imply_res; subst; entailer!.
  + unfold store_imply_res; subst; entailer!.
  + unfold store_imply_res.
    destruct r; [ | entailer!].
    destruct i; Intros x y.
    destruct t1; try congruence.
    destruct t1_1; try congruence.
    destruct ctype; try congruence.
    unfold store_ImplyProp.
    entailer!.
  + unfold store_imply_res; subst; entailer!.
Qed.

Lemma sllbseg_2_sllseg_term: forall x y l,
  sllbseg_term_list x y l ** y # Ptr |-> 0 |--
  EX h, x # Ptr |-> h ** sll_term_list h l.
Proof.
  intros.
  unfold sllbseg_term_list, sll_term_list.
  sep_apply (sllbseg_2_sllseg store_term_cell).
  Intros h; Exists h.
  sep_apply (sllseg_0_sll store_term_cell).
  entailer!.
Qed.

