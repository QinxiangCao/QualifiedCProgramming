From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Sorting.Permutation.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From Coq Require Import Lia.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Program.

Import CRules.
Local Open Scope sac_scope.

Set Asymmetric Patterns.

Module Induct.

(* A = Z (1, 2, 3)
P 1 = Z
P 2 = string
P 3 = bool
(1, 2, 3) (5, "asd", true) *)

Inductive dlist (A: Type) (P: A -> Type): list A -> Type :=
| dnil: dlist A P nil
| dcons (a: A) (x: P a) (l: list A) (L: dlist A P l): dlist A P (cons a l).

(* Definition P (n : Z) : Type :=
    if Z.eqb n 1 then Z
    else if Z.eqb n 2 then nat
    else bool
    . *)

Fixpoint dlist_eqb {A : Type} {P : A -> Type} (l1 l2 : list A)
                   (eqA : A -> A -> bool) (eqP : forall A B, P A -> P B -> bool)
                   (dl1 : dlist A P l1) (dl2 : dlist A P l2) : bool :=
    match dl1, dl2 with
    | dnil, dnil => true
    | dcons x Px xs Pxs, dcons y Py ys Pys =>
        (eqA x y && eqP _ _ Px Py && dlist_eqb _ _ eqA eqP Pxs Pys)%bool
    | _, _ => false
    end.

Lemma dlist_eqb_true_base_eq :
    forall A (P : A -> Type) (l1 l2 : list A)
           (eqA : A -> A -> bool) (eqP : forall A B, P A -> P B -> bool)
           (dl1 : dlist A P l1) (dl2 : dlist A P l2),
           (forall (x : A) (y : A), eqA x y = true -> x = y) ->
           dlist_eqb _ _ eqA eqP dl1 dl2 = true -> l1 = l2.
    intros.
    generalize dependent l2.
    induction dl1; destruct dl2; intros.
    - reflexivity.
    - simpl in H0; discriminate.
    - simpl in H0; discriminate.
    - simpl in H0.
      apply andb_true_iff in H0; destruct H0 as [? ?].
      apply andb_true_iff in H0; destruct H0 as [? ?].
      apply H in H0; subst.
      apply IHdl1 in H1; subst.
      reflexivity.
Qed.

Lemma dlist_eqb_true :
    forall A (P : A -> Type) (l1 l2 : list A)
           (eqA : A -> A -> bool) (eqP : forall A B, P A -> P B -> bool)
           (dl1 : dlist A P l1) (dl2 : dlist A P l2)
           (H1 : forall (x : A) (y : A), eqA x y = true -> x = y)
           (H2 : forall (a : A) (x : P a) (y : P a), eqP _ _ x y = true -> x = y)
           (H : dlist_eqb _ _ eqA eqP dl1 dl2 = true)
           (pf : l1 = l2),
           eq_rect _ (dlist A P) dl1 _ pf = dl2.
    intros.
    generalize dependent l2.
    induction dl1; destruct dl2; intros.
    - rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
      reflexivity.
    - discriminate.
    - discriminate.
    - inversion pf.
      simpl in *.
      apply andb_true_iff in H; destruct H as [? ?].
      apply andb_true_iff in H; destruct H as [? ?].
      apply H1 in H; subst.
      apply H2 in H5; subst.
      specialize (IHdl1 _ _ H0).
      specialize (IHdl1 eq_refl).
      rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq in IHdl1.
      rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
      subst; reflexivity.
Qed.

Lemma dlist_eqb_refl :
    forall A (P : A -> Type) (l : list A)
           (eqA : A -> A -> bool) (eqP : forall A B, P A -> P B -> bool)
           (dl : dlist A P l),
           (forall (x : A), eqA x x = true) ->
           (forall (a : A) (x : P a), eqP _ _ x x = true) ->
           dlist_eqb _ _ eqA eqP dl dl = true.
    intros; induction dl.
    - reflexivity.
    - simpl.
      rewrite H, H0, IHdl.
      reflexivity.
Qed.

Definition dmap {A: Type} {P Q: A -> Type} (f: forall a: A, P a -> Q a):
  forall {l: list A} (x: dlist A P l), dlist A Q l :=
  fix dmap {l: list A} (x: dlist A P l): dlist A Q l :=
    match x as x0 in dlist _ _ l0 return dlist _ _ l0 with
    | @dnil _ _ => dnil _ _
    | @dcons _ _ a xa l1 xl1 => dcons _ _ a (f a xa) l1 (dmap xl1)
    end.

Lemma nil_map_inv: forall {A B: Type} {f: B -> A} {lB: list B},
  nil = map f lB -> nil = lB.
Proof.
  intros.
  destruct lB.
  + reflexivity.
  + simpl in H.
    discriminate H.
Defined.

Lemma cons_map_inv:
  forall {A B: Type} {f: B -> A} {a: A} {lA0: list A} {lB: list B},
    cons a lA0 = map f lB ->
    sigT
      (fun b =>
         sig (fun lB0 => cons b lB0 = lB /\ a = f b /\ lA0 = map f lB0)).
Proof.
  intros.
  destruct lB as [ | b lB0].
  + simpl in H.
    discriminate H.
  + injection H as ? ?.
    exists b, lB0.
    split; [ | split].
    - reflexivity.
    - assumption.
    - assumption.
Defined.

Lemma map_inv_fact:
  forall {A B: Type} {f: B -> A} {lA: list A} {lB: list B} (e: lA = map f lB),
    match lA as lA0 return lA0 = map f lB -> Prop with
    | nil => fun e => e = f_equal (map f) (nil_map_inv e)
    | _ => fun e => 
        match cons_map_inv e with
        | @existT _ _ b (@exist _ _ lB1 (conj H0 (conj H1 H2))) =>
            e = ltac:(rewrite H1, H2; exact (f_equal (map f) H0))
        end
    end e.
Proof.
  intros.
  subst lA.
  unfold nil_map_inv.
  destruct lB; simpl.
  + reflexivity.
  + reflexivity.
Qed.

Definition dlist_map_dlist_aux (A B: Type) (P: A -> Type) (f: B -> A):
  forall lA: list A, dlist A P lA ->
    forall lB: list B, lA = map f lB -> dlist B (fun b => P (f b)) lB :=
  fix dlist_map_dlist_aux lA x :=
    match x as x0 in dlist _ _ lA0
      return forall lB: list B, lA0 = map f lB -> dlist B (fun b => P (f b)) lB
    with
    | @dnil _ _ => fun lB H_map =>
        @eq_rect _ _
          (dlist B (fun b => P (f b)))
          (dnil _ _) _
          (nil_map_inv H_map)
    | @dcons _ _ a xa lA1 x1 => fun lB H_map =>
        match cons_map_inv H_map with
        | @existT _ _ b (@exist _ _ lB1 (conj H0 (conj H1 H2))) =>
            @eq_rect _ _
              (dlist B (fun b => P (f b)))
              (dcons _ _
                 b
                 (@eq_rect _ _ P xa _ H1)
                 lB1
                 (dlist_map_dlist_aux lA1 x1 lB1 H2)) _
              H0
        end
    end.

Definition dlist_map_dlist (A B: Type) (P: A -> Type) (f: B -> A):
  forall lB: list B, dlist A P (map f lB) -> dlist B (fun b => P (f b)) lB :=
  fun lB x => dlist_map_dlist_aux A B P f (map f lB) x lB eq_refl.

Definition dlist_dlist_map (A B: Type) (P: A -> Type) (f: B -> A):
  forall l: list B, dlist B (fun b => P (f b)) l -> dlist A P (map f l) :=
  fix dlist_dlist_map l x :=
    match x as x0 in dlist _ _ l0 return dlist A P (map f l0) with
    | @dnil _ _ => dnil _ _
    | @dcons _ _ b xb l1 x1 =>
        dcons _ _ (f b) xb (map f l1) (dlist_dlist_map l1 x1)
    end.

Lemma dmap_dmap: forall A P Q R
  (f: forall a: A, P a -> Q a)
  (g: forall a: A, Q a -> R a)
  (l: list A)
  (x: dlist A P l),
  dmap g (dmap f x) = dmap (fun a x => g a (f a x)) x.
Proof.
  intros.
  induction x; simpl.
  + reflexivity.
  + rewrite IHx.
    reflexivity.
Qed.

Lemma dmap_id: forall A P f (l: list A) (x: dlist A P l),
  (forall a x, f a x = x) ->
  dmap f x = x.
Proof.
  intros.
  induction x; simpl.
  + reflexivity.
  + rewrite IHx, H.
    reflexivity.
Qed.

Lemma dlist_dlist_map_eq_rect: forall A B (P: A -> Type) (f: B -> A) (lB1 lB2: list B) (e: lB1 = lB2) (x: dlist B (fun b : B => P (f b)) lB1),
  dlist_dlist_map _ _ _ _ _ (eq_rect lB1 (dlist B (fun b => P (f b))) x lB2 e) =
  eq_rect (map f lB1) (dlist A P)(dlist_dlist_map A B P f lB1 x) (map f lB2) (f_equal (map f) e).
Proof.
  intros.
  subst lB2.
  simpl.
  reflexivity.
Qed.

Lemma dlist_map_dlist_dlist_map: forall A B (P: A -> Type) (f: B -> A) (lB: list B) (x: dlist A P (map f lB)),
  dlist_dlist_map _ _ _ _ _ (dlist_map_dlist _ _ _ _ _ x) = x.
Proof.
  unfold dlist_map_dlist.
  intros.
  change x with (@eq_rect _ _ (dlist A P) x _ eq_refl) at 2.
  generalize (@eq_refl _ (map f lB)).
  revert x.
  generalize (map f lB) at 1 2 5 6 as lA.
  intros.
  revert lB e.
  induction x; simpl; intros.
  + pose proof map_inv_fact e.
    simpl in H.
    set (e0 := nil_map_inv e) in H |- *.
    rewrite H.
    clearbody e0.
    rewrite dlist_dlist_map_eq_rect.
    simpl.
    reflexivity.
  + pose proof map_inv_fact e.
    simpl in H.
    destruct (cons_map_inv e) as [b [lB1 [H1 [H2 H3]]]] eqn:?H.
    subst a l.
    unfold eq_ind_r, eq_ind in H.
    simpl in H.
    rewrite H.
    simpl.
    rewrite dlist_dlist_map_eq_rect.
    simpl.
    specialize (IHx lB1 eq_refl).
    clear - IHx.
    rewrite IHx.
    reflexivity.
Qed.

Lemma dlist_dlist_map_dlist: forall A B (P: A -> Type) (f: B -> A) (lB: list B) (x: dlist B (fun b => P (f b)) lB),
  dlist_map_dlist _ _ _ _ _ (dlist_dlist_map _ _ _ _ _ x) = x.
Proof.
  intros.
  unfold dlist_map_dlist.
  induction x; simpl.
  + reflexivity.
  + rewrite IHx.
    reflexivity.
Qed.

End Induct.

Inductive WFuncSig : Type :=
| FSig (args : list Z) (ret : Z)
.

Inductive WPredSig : Type :=
| PSig (args : list Z)
.

Fixpoint list_eqb (l1 : list Z) (l2 : list Z) : bool :=
    match l1, l2 with
    | nil, nil => true
    | x :: xs, y :: ys => Z.eqb x y && list_eqb xs ys
    | _, _ => false
    end.

Lemma list_eqb_refl :
    forall l, list_eqb l l = true.
    induction l; simpl; auto.
    - apply andb_true_iff; split.
      apply Z.eqb_refl.
      apply IHl.
Qed.

Lemma list_eqb_true :
    forall l1 l2, list_eqb l1 l2 = true -> l1 = l2.
    induction l1; destruct l2; intros.
    - reflexivity.
    - simpl in H; discriminate H.
    - simpl in H; discriminate H.
    - simpl in H.
      apply andb_true_iff in H as [? ?].
      apply Z.eqb_eq in H; subst.
      f_equal; auto.
Qed.

Definition wfunc_sig_eqb (s1 s2 : WFuncSig) : bool :=
    match s1, s2 with
    | FSig args1 ret1, FSig args2 ret2 =>
        andb (list_eqb args1 args2) (Z.eqb ret1 ret2)
    end.

Lemma wfunc_sig_eqb_refl :
    forall s, wfunc_sig_eqb s s = true.
    intros s; destruct s; simpl.
    apply andb_true_iff; split.
    - apply list_eqb_refl.
    - apply Z.eqb_refl.
Qed.

Lemma wfunc_sig_eqb_true :
    forall s1 s2, wfunc_sig_eqb s1 s2 = true -> s1 = s2.
    intros; destruct s1, s2; simpl in *.
    apply andb_true_iff in H as [? ?].
    apply list_eqb_true in H;
    apply Z.eqb_eq in H0; subst; reflexivity.
Qed.

Definition wpred_sig_eqb (s1 s2 : WPredSig) : bool :=
    match s1, s2 with
    | PSig args1, PSig args2 => list_eqb args1 args2
    end.

Lemma wpred_sig_eqb_refl :
    forall s, wpred_sig_eqb s s = true.
    intros s; destruct s; simpl.
    apply list_eqb_refl.
Qed.

Lemma wpred_sig_eqb_true :
    forall s1 s2, wpred_sig_eqb s1 s2 = true -> s1 = s2.
    intros; destruct s1, s2; simpl in *.
    apply list_eqb_true in H; subst; reflexivity.
Qed.

Definition wfunc_sig_eq_dec : forall (s1 s2 : WFuncSig), {s1 = s2} + {s1 <> s2}.
    intros.
    destruct s1, s2.
    destruct (Z.eq_dec ret ret0).
    - destruct (list_eq_dec Z.eq_dec args args0).
      subst; apply (left eq_refl).
      right; congruence.
    - right; congruence.
Defined. 

Definition wpred_sig_eq_dec : forall (s1 s2 : WPredSig), {s1 = s2} + {s1 <> s2}.
    intros.
    destruct s1, s2.
    destruct (list_eq_dec Z.eq_dec args args0).
    subst; apply (left eq_refl).
    right; congruence.
Defined.

Definition get_func_sig_args (f : WFuncSig) :=
    match f with
    | FSig args _ => args
    end.

Definition get_func_sig_ret (f : WFuncSig) :=
    match f with
    | FSig _ ret => ret
    end.

Definition get_pred_sig_args (p : WPredSig) :=
    match p with
    | PSig args => args
    end.

Definition TypeMapping : Type := Z -> Type.

Definition tylookup (ty_env : TypeMapping) (ty : Z) : Type :=
         if (Z.eq_dec ty 0) then Z
    else ty_env ty.

Definition function_type_denote (ret : Type) (args : list Type) : Type :=
    fold_right (fun ty ret => ty -> ret) ret args.

Definition type_mapping_update (ty_env : TypeMapping) (ty : Z) (v : Type) :=
    fun ty' =>
        match (Z.eq_dec ty ty') with
        | left _ => v
        | right _ => ty_env ty'
        end.

Definition TermMapping (ty_env : TypeMapping) : Type :=
    forall (n : Z) (ty : Z), tylookup ty_env ty.

Definition StringMapping : Type := Z -> string.

Definition wfunc_sig_denote (ty_env : TypeMapping) (sig : WFuncSig) : Type :=
    Induct.dlist Z (fun ty => tylookup ty_env ty) (get_func_sig_args sig) ->
    tylookup ty_env (get_func_sig_ret sig).

Definition wpred_sig_denote (ty_env : TypeMapping) (ret : Type) (sig : WPredSig):=
    Induct.dlist Z (fun ty => tylookup ty_env ty) (get_pred_sig_args sig) ->
    ret.

Definition gen_func (ty_env : TypeMapping) (sig : WFuncSig)
                    (f : function_type_denote (tylookup ty_env (get_func_sig_ret sig)) (map (tylookup ty_env) (get_func_sig_args sig))) : wfunc_sig_denote ty_env sig.
    destruct sig; unfold wfunc_sig_denote; intros.
    induction X.
    - exact f.
    - exact (IHX (f x)).
Defined.

Definition gen_pred (ty_env : TypeMapping) (sig : WPredSig) (ret : Type)
                    (f : function_type_denote ret (map (tylookup ty_env) (get_pred_sig_args sig))) : wpred_sig_denote ty_env ret sig.
    destruct sig; unfold wpred_sig_denote; intros.
    induction X.
    - exact f.
    - exact (IHX (f x)).
Defined.

Definition FuncMapping (ty_env : TypeMapping) : Type :=
    forall (n : Z) (sig : WFuncSig), wfunc_sig_denote ty_env sig.

Definition PredMapping (ty_env : TypeMapping) : Type :=
    forall (n : Z) (sig : WPredSig), wpred_sig_denote ty_env expr sig.

Definition PropMapping (ty_env : TypeMapping) : Type :=
    forall (n : Z) (sig : WPredSig), wpred_sig_denote ty_env Prop sig.

Inductive environment (ty_env : TypeMapping) : Type :=
| GEnv (tm_env : TermMapping ty_env)
       (str_env : StringMapping)
       (func_env : FuncMapping ty_env)
       (pred_env : PredMapping ty_env)
       (prop_env : PropMapping ty_env)
.

Definition get_tm_env {ty_env : TypeMapping} (env : environment ty_env) :=
    match env with
    | GEnv tm_env _ _ _ _=> tm_env
    end.

Definition get_str_env {ty_env : TypeMapping} (env : environment ty_env) :=
    match env with
    | GEnv _ str_env _ _ _ => str_env
    end.

Definition get_func_env {ty_env : TypeMapping} (env : environment ty_env) :=
    match env with
    | GEnv _ _ func_env _ _ => func_env
    end.

Definition get_pred_env {ty_env : TypeMapping} (env : environment ty_env) :=
    match env with
    | GEnv _ _ _ pred_env _ => pred_env
    end.

Definition get_prop_env {ty_env : TypeMapping} (env : environment ty_env) :=
    match env with
    | GEnv _ _ _ _ prop_env => prop_env
    end.

Definition term_mapping_update {ty_env : TypeMapping} (env : TermMapping ty_env) (n ty : Z) (v : tylookup ty_env ty) :=
    fun n' ty' =>
        match (Z.eq_dec n n') with
        | left _ => match (Z.eq_dec ty ty') with
                    | left H => eq_rect _ (tylookup ty_env) v _ H
                    | right _ => env n' ty'
                    end
        | right _ => env n' ty'
        end.

Definition term_mapping_update_env {ty_env : TypeMapping} (env : environment ty_env) (n ty : Z) (v : tylookup ty_env ty) :=
    match env with
    | GEnv tm_env str_env func_env pred_env prop_env =>
        GEnv ty_env (term_mapping_update tm_env n ty v) str_env func_env pred_env prop_env
    end.

Definition string_mapping_update (env : StringMapping) (n : Z) (v : string) :=
    fun n' => if (Z.eq_dec n n') then v else env n'.

Definition func_mapping_update {ty_env : TypeMapping} (env : FuncMapping ty_env) (n : Z) (sig : WFuncSig) (v : wfunc_sig_denote ty_env sig) :=
    fun n' sig' =>
        match (Z.eq_dec n n') with
        | left _ => match (wfunc_sig_eq_dec sig sig') with
                    | left H => eq_rect _ (wfunc_sig_denote ty_env)  v _ H
                    | right _ => env n' sig'
                    end
        | right _ => env n' sig'
        end.

Definition pred_mapping_update {ty_env : TypeMapping} (env : PredMapping ty_env) (n : Z) (sig : WPredSig) (v : wpred_sig_denote ty_env expr sig) :=
    fun n' sig' =>
        match (Z.eq_dec n n') with
        | left _ => match (wpred_sig_eq_dec sig sig') with
                    | left H => eq_rect _ (wpred_sig_denote ty_env expr)  v _ H
                    | right _ => env n' sig'
                    end
        | right _ => env n' sig'
        end.

Definition prop_mapping_update {ty_env : TypeMapping} (env : PropMapping ty_env) (n : Z) (sig : WPredSig) (v : wpred_sig_denote ty_env Prop sig) :=
    fun n' sig' =>
        match (Z.eq_dec n n') with
        | left _ => match (wpred_sig_eq_dec sig sig') with
                    | left H => eq_rect _ (wpred_sig_denote ty_env Prop)  v _ H
                    | right _ => env n' sig'
                    end
        | right _ => env n' sig'
        end.

Lemma term_mapping_update_lookup :
    forall ty_env (env : TermMapping ty_env) (n ty : Z),
        (term_mapping_update env n ty (env n ty)) = env.
    intros.
    apply functional_extensionality; intros.
    apply functional_extensionality_dep; intros.
    unfold term_mapping_update.
    destruct (Z.eq_dec n x); try reflexivity.
    destruct (Z.eq_dec ty x0); try reflexivity.
    rewrite e, e0.
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma func_mapping_update_lookup :
    forall ty_env (env : FuncMapping ty_env) (n : Z) (sig : WFuncSig),
        (func_mapping_update env n sig (env n sig)) = env.
    intros.
    apply functional_extensionality; intros.
    apply functional_extensionality_dep; intros.
    unfold func_mapping_update.
    destruct (Z.eq_dec n x); try reflexivity.
    destruct (wfunc_sig_eq_dec sig x0); try reflexivity.
    rewrite e, e0.
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma pred_mapping_update_lookup :
    forall ty_env (env : PredMapping ty_env) (n : Z) (sig : WPredSig),
        (pred_mapping_update env n sig (env n sig)) = env.
    intros.
    apply functional_extensionality; intros.
    apply functional_extensionality_dep; intros.
    unfold pred_mapping_update.
    destruct (Z.eq_dec n x); try reflexivity.
    destruct (wpred_sig_eq_dec sig x0); try reflexivity.
    rewrite e, e0.
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma prop_mapping_update_lookup :
    forall ty_env (env : PropMapping ty_env) (n : Z) (sig : WPredSig),
        (prop_mapping_update env n sig (env n sig)) = env.
    intros.
    apply functional_extensionality; intros.
    apply functional_extensionality_dep; intros.
    unfold prop_mapping_update.
    destruct (Z.eq_dec n x); try reflexivity.
    destruct (wpred_sig_eq_dec sig x0); try reflexivity.
    rewrite e, e0.
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma term_mapping_update_eq :
    forall ty_env (env : TermMapping ty_env) (n ty : Z) v,
        (term_mapping_update env n ty v) n ty = v.
    intros.
    unfold term_mapping_update.
    destruct (Z.eq_dec n n); [ | contradiction ].
    destruct (Z.eq_dec ty ty); [ | contradiction ].
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma func_mapping_update_eq :
    forall ty_env (env : FuncMapping ty_env) (n : Z) (sig : WFuncSig) v,
        (func_mapping_update env n sig v) n sig = v.
    intros.
    unfold func_mapping_update.
    destruct (Z.eq_dec n n); [ | contradiction ].
    destruct (wfunc_sig_eq_dec sig sig); [ | contradiction ].
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma pred_mapping_update_eq :
    forall ty_env (env : PredMapping ty_env) (n : Z) (sig : WPredSig) v,
        (pred_mapping_update env n sig v) n sig = v.
    intros.
    unfold pred_mapping_update.
    destruct (Z.eq_dec n n); [ | contradiction ].
    destruct (wpred_sig_eq_dec sig sig); [ | contradiction ].
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma prop_mapping_update_eq :
    forall ty_env (env : PropMapping ty_env) (n : Z) (sig : WPredSig) v,
        (prop_mapping_update env n sig v) n sig = v.
    intros.
    unfold prop_mapping_update.
    destruct (Z.eq_dec n n); [ | contradiction ].
    destruct (wpred_sig_eq_dec sig sig); [ | contradiction ].
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma term_mapping_update_neq :
    forall ty_env (env : TermMapping ty_env) (n n' ty ty': Z) v,
        n <> n' \/ ty <> ty' ->
        (term_mapping_update env n ty v) n' ty' = env n' ty'.
    intros.
    unfold term_mapping_update.
    destruct (Z.eq_dec n n').
    - destruct (Z.eq_dec ty ty').
      + destruct H; contradiction.
      + reflexivity.
    - reflexivity.
Qed.

Lemma func_mapping_update_neq :
    forall ty_env (env : FuncMapping ty_env) (n n' : Z) (sig sig' : WFuncSig) v,
        n <> n' \/ sig <> sig' ->
        (func_mapping_update env n sig v) n' sig' = env n' sig'.
    intros.
    unfold func_mapping_update.
    destruct (Z.eq_dec n n').
    - destruct (wfunc_sig_eq_dec sig sig').
      + destruct H; contradiction.
      + reflexivity.
    - reflexivity.
Qed.

Lemma pred_mapping_update_neq :
    forall ty_env (env : PredMapping ty_env) (n n' : Z) (sig sig' : WPredSig) v,
        n <> n' \/ sig <> sig' ->
        (pred_mapping_update env n sig v) n' sig' = env n' sig'.
    intros.
    unfold pred_mapping_update.
    destruct (Z.eq_dec n n').
    - destruct (wpred_sig_eq_dec sig sig').
      + destruct H; contradiction.
      + reflexivity.
    - reflexivity.
Qed.

Lemma prop_mapping_update_neq :
    forall ty_env (env : PropMapping ty_env) (n n' : Z) (sig sig' : WPredSig) v,
        n <> n' \/ sig <> sig' ->
        (prop_mapping_update env n sig v) n' sig' = env n' sig'.
    intros.
    unfold prop_mapping_update.
    destruct (Z.eq_dec n n').
    - destruct (wpred_sig_eq_dec sig sig').
      + destruct H; contradiction.
      + reflexivity.
    - reflexivity.
Qed.

Lemma term_mapping_update_swap :
    forall ty_env (env : TermMapping ty_env) x1 ty1 v1 x2 ty2 v2,
        x1 <> x2 \/ ty1 <> ty2 ->
        (term_mapping_update (term_mapping_update env x1 ty1 v1) x2 ty2 v2) =
        (term_mapping_update (term_mapping_update env x2 ty2 v2) x1 ty1 v1).
    intros.
    apply functional_extensionality_dep; intros x.
    apply functional_extensionality_dep; intros ty.
    destruct (Z.eq_dec x x1); try (subst x1);
    destruct (Z.eq_dec x x2); try (subst x2);
    destruct (Z.eq_dec ty ty1); try (subst ty1);
    destruct (Z.eq_dec ty ty2); try (subst ty2);
    destruct H;
    try (repeat (rewrite ! term_mapping_update_eq));
    try (rewrite term_mapping_update_neq);
    try (repeat (rewrite ! term_mapping_update_eq));
    try (rewrite term_mapping_update_neq);
    try (repeat (rewrite ! term_mapping_update_eq));
    try (rewrite term_mapping_update_neq);
    try (repeat (rewrite ! term_mapping_update_eq));
    try (rewrite term_mapping_update_neq);
    try reflexivity;
    try lia.
Qed.

Lemma term_mapping_update_shallow :
    forall ty_env (env : TermMapping ty_env) x ty v1 v2,
        term_mapping_update (term_mapping_update env x ty v1) x ty v2 = term_mapping_update env x ty v2.
    intros.
    apply functional_extensionality_dep; intros x'.
    apply functional_extensionality_dep; intros ty'.
    destruct (Z.eq_dec x x'); destruct (Z.eq_dec ty ty'); subst.
    -   rewrite ! term_mapping_update_eq; reflexivity.
    -   rewrite ! term_mapping_update_neq by (right; assumption).
        reflexivity.
    -   rewrite ! term_mapping_update_neq by (left; assumption).
        reflexivity.
    -   rewrite ! term_mapping_update_neq by (left; assumption).
        reflexivity.
Qed.

Inductive Ctype : Type :=
| C8
| C32
| C64
| CPtr
.

Inductive Wexpr : Z -> Type :=
| EVar (x : Z) (ty : Z) : Wexpr ty
| EConstZ (val : Z) : Wexpr 0
| EField (addr : Wexpr 0) (struct_id field_id : Z) : Wexpr 0
| EFunc (f : Z) (sig : WFuncSig) (args : Induct.dlist Z Wexpr (get_func_sig_args sig)) : Wexpr (get_func_sig_ret sig)
.

Definition wexpr_ind
    (P : forall ty, Wexpr ty -> Prop)
    (Q : forall l, Induct.dlist Z Wexpr l -> Prop)
    (H_EVar : forall x ty, P ty (EVar x ty))
    (H_EConstZ : forall val, P 0%Z (EConstZ val))
    (H_EField : forall addr struct_id field_id, P 0%Z addr -> P 0%Z (EField addr struct_id field_id))
    (H_EFunc : forall f sig args, Q _ args -> P _ (EFunc f sig args))
    (H_dnil : Q _ (Induct.dnil _ _))
    (H_dcons : forall x xs Px Pxs, P x Px -> Q xs Pxs -> Q _ (Induct.dcons _ _ x Px xs Pxs)) :
    forall ty e, P ty e :=
    fix wexpr_ind ty e : P ty e :=
    match e as e0 in Wexpr ty0 return P ty0 e0 with
    | EVar x ty => H_EVar x ty
    | EConstZ val => H_EConstZ val
    | EField addr struct_id field_id =>
        H_EField addr struct_id field_id (wexpr_ind 0%Z addr)
    | EFunc f sig args =>
        H_EFunc f sig args
            ((fix dlist_ind l d : Q l d :=
                match d as d0 in Induct.dlist _ _ l0 return Q l0 d0 with
                | Induct.dnil => H_dnil
                | Induct.dcons x Px xs Pxs => H_dcons x xs Px Pxs (wexpr_ind x Px) (dlist_ind xs Pxs)
                end) _ args)
    end.

Inductive SepAtomTerm : Type :=
| TSepDataAt (addr : Wexpr 0) (ty : Ctype) (val : Wexpr 0)
(* | TSepUndef (addr : Wexpr 0) (ty : Ctype) *)
| TSepFunc (f : Z) (sig : WPredSig) (args : Induct.dlist Z Wexpr (get_pred_sig_args sig))
.

Inductive PropAtomTerm : Type :=
| TPropTrue
| TPropFalse
| TPropNot (p : PropAtomTerm)
| TPropEq ty (e1 : Wexpr ty) (e2 : Wexpr ty)
| TPropAnd (p1 : PropAtomTerm) (p2 : PropAtomTerm)
| TPropOr (p1 : PropAtomTerm) (p2 : PropAtomTerm)
| TPropImply (p1 : PropAtomTerm) (p2 : PropAtomTerm)
| TPropIff (p1 : PropAtomTerm) (p2 : PropAtomTerm)
| TPropFunc (f : Z) (sig : WPredSig) (args : Induct.dlist Z Wexpr (get_pred_sig_args sig))
.

Definition SepTerm : Type := list SepAtomTerm.
Definition PropTerm : Type := list PropAtomTerm.
Definition PSTerm : Type := PropTerm * SepTerm.

Definition VarType : Type := Z * Z.
Definition VarList : Type := list VarType.

Inductive ExistsTerm : Type :=
| TExists (vl : VarList) (t : PSTerm)
.

Inductive ForallTerm : Type :=
| TForall (vl : VarList) (pre : PSTerm) (post : ExistsTerm)
.

Definition ExistsCons (x : VarType) (t : ExistsTerm) :=
    match t with
    | TExists vl t => TExists (x :: vl) t
    end.

Lemma ind_exists :
    forall (t : ExistsTerm),
    forall (P : ExistsTerm -> Prop),
    (forall t', P (TExists nil t')) ->
    (forall x t, P t -> P (ExistsCons x t)) ->
    P t.
    intros.
    destruct t.
    induction vl.
    - apply H.
    - specialize (H0 a (TExists vl t)).
      simpl in H0.
      apply (H0 IHvl).
Qed.

Definition ForallCons (x : VarType) (t : ForallTerm) :=
    match t with
    | TForall vl pre post => TForall (x :: vl) pre post
    end.

Lemma ind_forall :
    forall (t : ForallTerm),
    forall (P : ForallTerm -> Prop),
    (forall pre post, P (TForall nil pre post)) ->
    (forall x t, P t -> P (ForallCons x t)) ->
    P t.
    intros.
    destruct t.
    induction vl.
    - apply H.
    - specialize (H0 a (TForall vl pre post)).
      simpl in H0.
      apply (H0 IHvl).
Qed.

Fixpoint wexpr_denote (ty : Z) (e : Wexpr ty)
                        (ty_env : TypeMapping) (env : @environment ty_env) : tylookup ty_env ty.
    dependent destruction e.
    - exact ((get_tm_env env) x ty).
    - exact val.
    - exact (field_address (wexpr_denote 0%Z e ty_env env) ((get_str_env env) struct_id) ((get_str_env env) field_id)).
    - exact (((get_func_env env) f sig) (Induct.dmap (fun a x => wexpr_denote _ x ty_env env) args)).
Defined.

Definition sep_atom_term_denote (t : SepAtomTerm) ty_env (env : environment _) : expr :=
    match t with
    | TSepDataAt addr ty val =>
      match ty with
      | C8 => (wexpr_denote _ addr _ env # Char |-> wexpr_denote _ val _ env)
      | C32 => (wexpr_denote _ addr _ env # Int |-> wexpr_denote _ val _ env)
      | C64 => (wexpr_denote _ addr _ env # Int64 |-> wexpr_denote _ val _ env)
      | CPtr => (wexpr_denote _ addr _ env # Ptr |-> wexpr_denote _ val _ env)
      end
    | TSepFunc f sig args =>
      ((get_pred_env env) f sig) (Induct.dmap (fun a x => wexpr_denote _ x ty_env env) args)
    end.

Definition sep_term_denote (t : SepTerm) ty_env (env : environment _) : expr :=
    fold_right (fun b a => a ** sep_atom_term_denote b ty_env env) emp t.

Fixpoint prop_atom_term_denote (t : PropAtomTerm) ty_env (env : environment _) : Prop :=
    match t with
    | TPropTrue => True
    | TPropFalse => False
    | TPropEq ty e1 e2 => wexpr_denote _ e1 ty_env env = wexpr_denote _ e2 ty_env env
    | TPropNot p => ~(prop_atom_term_denote p ty_env env)
    | TPropAnd p1 p2 => (prop_atom_term_denote p1 ty_env env) /\ (prop_atom_term_denote p2 ty_env env)
    | TPropOr p1 p2 => (prop_atom_term_denote p1 ty_env env) \/ (prop_atom_term_denote p2 ty_env env)
    | TPropImply p1 p2 => (prop_atom_term_denote p1 ty_env env) -> (prop_atom_term_denote p2 ty_env env)
    | TPropIff p1 p2 => (prop_atom_term_denote p1 ty_env env) <-> (prop_atom_term_denote p2 ty_env env)
    | TPropFunc f sig args => ((get_prop_env env) f sig) (Induct.dmap (fun a x => wexpr_denote _ x ty_env env) args)
    end.

Definition prop_term_denote (t : PropTerm) ty_env (env : environment _) : expr :=
    fold_right (fun b a => a && “ prop_atom_term_denote b ty_env env ”) CRules.truep t.

Definition prop_term_denote' (t : PropTerm) ty_env (env : environment _) : Prop :=
    fold_right (fun b a => a /\ (prop_atom_term_denote b ty_env env)) True t.

Lemma prop_term_denote_equiv :
    forall (p : PropTerm) ty_env env, prop_term_denote p ty_env env --||-- “ prop_term_denote' p ty_env env ”.
    induction p; intros; simpl.
    -   unfold CRules.truep,  CRules.logic_equiv, CRules.derivable1, CRules.coq_prop.
        split; intros; auto.
    -   unfold CRules.truep,  CRules.logic_equiv, CRules.derivable1, CRules.coq_prop, CRules.andp in *.
        specialize (IHp ty_env env).
        destruct IHp.
        split; intros; specialize (H0 m); specialize (H m).
        all: tauto.
Qed.

Definition ps_term_denote (t : PSTerm) ty_env (env : environment _) : expr :=
    match t with
    | (p, s) => prop_term_denote p ty_env env && sep_term_denote s ty_env env
    end.

Fixpoint var_list_exists_denote (vl : VarList) ty_env (env : environment _) cont : expr :=
    match vl with
    | cons (x, ty) vls =>
        EX v : tylookup ty_env ty, var_list_exists_denote vls _ (term_mapping_update_env env x ty v) cont
    | nil => cont ty_env env
    end.

Fixpoint var_list_forall_denote (vl : VarList) ty_env (env : environment _) cont : Prop :=
    match vl with
    | cons (x, ty) vls =>
        forall v : tylookup ty_env ty, var_list_forall_denote vls _ (term_mapping_update_env env x ty v) cont
    | nil => cont ty_env env
    end.

Fixpoint var_list_all_denote (vl : VarList) ty_env (env : environment _) cont : expr :=
    match vl with
    | cons (x, ty) vls =>
        ALL v : (tylookup ty_env ty), var_list_all_denote vls _ (term_mapping_update_env env x ty v) cont
    | nil => cont ty_env env
    end.

Definition exists_term_denote (t : ExistsTerm) ty_env (env : environment ty_env) : expr :=
    match t with
    | TExists vl t => var_list_exists_denote vl _ env
        (fun ty_env env => (ps_term_denote t ty_env env))
    end.

Lemma exists_term_denote_nil :
    forall t ty_env (env : environment ty_env),
        exists_term_denote (TExists nil t) _ env = ps_term_denote t _ env.
    intros; simpl; reflexivity.
Qed.

Lemma exists_term_denote_cons : forall (x ty : Z) (t : ExistsTerm) ty_env (env : environment _),
    exists_term_denote (ExistsCons (x, ty) t) _ env =
    EX v : tylookup ty_env ty, exists_term_denote t _ (term_mapping_update_env env x ty v).
    intros.
    unfold exists_term_denote.
    unfold ExistsCons.
    destruct t.
    simpl.
    reflexivity.
Qed.

Definition forall_term_denote (t : ForallTerm) ty_env (env : environment ty_env) : Prop :=
    match t with
    | TForall vl pre post => var_list_forall_denote vl _ env
        (fun ty_env env => (ps_term_denote pre _ env) |-- (exists_term_denote post _ env))
    end.

Lemma forall_term_denote_nil :
    forall pre post ty_env (env : environment ty_env),
        forall_term_denote (TForall nil pre post) _ env =
        (ps_term_denote pre _ env |-- exists_term_denote post _ env).
    intros; simpl; reflexivity.
Qed.

Lemma forall_term_denote_cons : forall (x ty : Z) (t : ForallTerm) ty_env (env : environment ty_env),
    forall_term_denote (ForallCons (x, ty) t) _ env =
    forall v : tylookup ty_env ty, forall_term_denote t _ (term_mapping_update_env env x ty v).
    intros.
    unfold forall_term_denote.
    unfold ForallCons.
    destruct t.
    simpl.
    reflexivity.
Qed.

Definition Provable (t : ForallTerm) ty_env (env : environment ty_env) : Prop :=
    forall_term_denote t _ env.

Inductive Operation : Type :=
| OAssume (H : PropAtomTerm)
| OLeftSepAdd (H : SepAtomTerm)
| OLeftSepErase (H : SepAtomTerm)
| ORightSepAdd (H : SepAtomTerm)
| ORightSepErase (H : SepAtomTerm)
| OLeftPropAdd (H : PropAtomTerm)
| OLeftPropErase (H : PropAtomTerm)
| ORightPropAdd (H : PropAtomTerm)
| ORightPropErase (H : PropAtomTerm)
| OForallAdd (v : VarType)
| ORightExistsAdd (v : VarType)
.

Definition add_sep (t : SepTerm) (H : SepAtomTerm) :=
    H :: t.

Definition add_prop (t : PropTerm) (H : PropAtomTerm) :=
    H :: t.

Fixpoint wexpr_eqb (ty1 ty2 : Z) (e1 : Wexpr ty1) (e2 : Wexpr ty2) : bool :=
    Z.eqb ty1 ty2 &&
    match e1, e2 with
    | EVar x1 ty1, EVar x2 ty2 => Z.eqb x1 x2
    | EConstZ val1, EConstZ val2 => Z.eqb val1 val2
    | EField addr1 struct_id1 field_id1, EField addr2 struct_id2 field_id2 =>
        Z.eqb struct_id1 struct_id2 && Z.eqb field_id1 field_id2 && wexpr_eqb 0 0 addr1 addr2
    | EFunc f1 sig1 args1, EFunc f2 sig2 args2 =>
        Z.eqb f1 f2 && wfunc_sig_eqb sig1 sig2 &&
        (fix dlist_eqb (l1 l2 : list Z)
                       (dl1 : Induct.dlist Z Wexpr l1) (dl2 : Induct.dlist Z Wexpr l2) : bool :=
            match dl1, dl2 with
            | Induct.dnil, Induct.dnil => true
            | Induct.dcons x Px xs Pxs, Induct.dcons y Py ys Pys =>
                (Z.eqb x y && wexpr_eqb _ _ Px Py && dlist_eqb _ _ Pxs Pys)%bool
            | _, _ => false
            end) _ _ args1 args2
    | _, _ => false
    end.

Lemma wexpr_eqb_refl :
    forall ty (e : Wexpr ty), wexpr_eqb ty ty e e = true.
    intros.
    pose (Q := (fun l1 dl1 => Induct.dlist_eqb l1 l1 Z.eqb wexpr_eqb dl1 dl1 = true)).
    induction e using wexpr_ind with (Q := Q).
    - simpl.
      apply andb_true_iff.
      split.
      + apply Z.eqb_eq; reflexivity.
      + apply Z.eqb_eq; reflexivity.
    - simpl.
      apply Z.eqb_eq; reflexivity.
    - simpl.
      apply andb_true_iff.
      split.
      + apply andb_true_iff.
        split.
        * apply Z.eqb_eq; reflexivity.
        * apply Z.eqb_eq; reflexivity.
      + apply IHe.
    - simpl.
      apply andb_true_iff.
      split.
      + apply Z.eqb_eq.
        reflexivity.
      + apply andb_true_iff.
        split.
        * apply andb_true_iff.
          split.
          -- apply Z.eqb_eq; reflexivity.
          -- apply wfunc_sig_eqb_refl.
        * unfold Q in IHe.
          remember ((fix dlist_eqb
          (l1 l2 : list Z) (dl1 : Induct.dlist Z Wexpr l1) (dl2 : Induct.dlist Z Wexpr l2) {struct dl1} : bool :=
          match dl1 with
          | @Induct.dnil _ _ => match dl2 with
                                | @Induct.dnil _ _ => true
                                | @Induct.dcons _ _ a _ l _ => false
                                end
          | @Induct.dcons _ _ x Px xs Pxs =>
              match dl2 with
              | @Induct.dnil _ _ => false
              | @Induct.dcons _ _ y Py ys Pys => ((x =? y)%Z && wexpr_eqb x y Px Py && dlist_eqb xs ys Pxs Pys)%bool
              end
          end)) as dlist_eqb.
          assert (dlist_eqb = (fun l1 l2 dl1 dl2 => (Induct.dlist_eqb l1 l2 Z.eqb wexpr_eqb dl1 dl2))).
          { clear - Heqdlist_eqb.
            assert (dlist_eqb _ _ (Induct.dnil _ _) (Induct.dnil _ _) = true). {
                rewrite Heqdlist_eqb.
                reflexivity.
            }
            assert (forall x Px xs Pxs, dlist_eqb _ _ (Induct.dnil _ _) (Induct.dcons _ _ x Px xs Pxs) = false). {
                rewrite Heqdlist_eqb.
                reflexivity.
            }
            assert (forall x Px xs Pxs, dlist_eqb _ _ (Induct.dcons _ _ x Px xs Pxs) (Induct.dnil _ _) = false). {
                rewrite Heqdlist_eqb.
                reflexivity.
            }
            assert (forall x Px xs Pxs y Py ys Pys, dlist_eqb _ _ (Induct.dcons _ _ x Px xs Pxs) (Induct.dcons _ _ y Py ys Pys) = ((x =? y)%Z && wexpr_eqb x y Px Py && dlist_eqb xs ys Pxs Pys)%bool). {
                rewrite Heqdlist_eqb.
                reflexivity.
            }
            apply functional_extensionality_dep; intros l1.
            apply functional_extensionality_dep; intros l2.
            apply functional_extensionality; intros dl1.
            apply functional_extensionality; intros dl2.
            generalize dependent dl2.
            generalize dependent l2.
            induction dl1; destruct dl2; intros; [
              rewrite H |
              rewrite H0 |
              rewrite H1 |
              rewrite H2; simpl; rewrite <- IHdl1
            ]; reflexivity.
          }
          rewrite H.
          apply IHe.
    - reflexivity.
    - unfold Q; simpl.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      apply Z.eqb_eq; reflexivity.
      apply IHe.
      apply IHe0.
Qed.

Lemma wexpr_eqb_true :
    forall ty1 ty2 (e1 : Wexpr ty1) (e2 : Wexpr ty2),
        wexpr_eqb ty1 ty2 e1 e2 = true ->
        (forall (pf : ty1 = ty2), eq_rect _ _ e1 _ pf = e2).
    pose (Q := (fun l1 dl1 => forall l2 dl2, Induct.dlist_eqb l1 l2 Z.eqb wexpr_eqb dl1 dl2 = true ->
                              (forall (pf : l1 = l2), eq_rect _ _ dl1 _ pf = dl2))).
    intros ty1 ty2 e1.
    generalize dependent ty2.
    induction e1 using wexpr_ind with (Q := Q).
    - intros.
      destruct e2; simpl in H; try discriminate.
      + apply andb_true_iff in H; destruct H.
        apply Z.eqb_eq in H0.
        subst; reflexivity.
      + apply andb_true_iff in H; destruct H; discriminate.
      + apply andb_true_iff in H; destruct H; discriminate.
      + apply andb_true_iff in H; destruct H; discriminate.
    - intros.
      destruct e2; simpl in H; try discriminate.
      + apply andb_true_iff in H; destruct H; discriminate.
      + apply Z.eqb_eq in H; subst.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq; reflexivity.
      + apply andb_true_iff in H; destruct H; discriminate.
    - intros.
      destruct e2; simpl in H; try discriminate.
      + apply andb_true_iff in H; destruct H; discriminate.
      + apply andb_true_iff in H; destruct H.
        specialize (IHe1 _ _ H0 eq_refl).
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
        apply andb_true_iff in H; destruct H.
        apply Z.eqb_eq in H.
        apply Z.eqb_eq in H1.
        subst.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
        reflexivity.
      + apply andb_true_iff in H; destruct H; discriminate.
    - intros.
      destruct e2; simpl in H; try discriminate.
      + apply andb_true_iff in H; destruct H; discriminate.
      + apply andb_true_iff in H; destruct H; discriminate.
      + apply andb_true_iff in H; destruct H; discriminate.
      + apply andb_true_iff in H; destruct H.
        apply andb_true_iff in H0; destruct H0.
        apply andb_true_iff in H0; destruct H0.
        apply Z.eqb_eq in H0, H.
        apply wfunc_sig_eqb_true in H2.
        subst.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
        unfold Q in IHe1.
        remember ((fix dlist_eqb
        (l1 l2 : list Z) (dl1 : Induct.dlist Z Wexpr l1) (dl2 : Induct.dlist Z Wexpr l2) {struct dl1} : bool :=
        match dl1 with
        | @Induct.dnil _ _ => match dl2 with
                              | @Induct.dnil _ _ => true
                              | @Induct.dcons _ _ a _ l _ => false
                              end
        | @Induct.dcons _ _ x Px xs Pxs =>
            match dl2 with
            | @Induct.dnil _ _ => false
            | @Induct.dcons _ _ y Py ys Pys => ((x =? y)%Z && wexpr_eqb x y Px Py && dlist_eqb xs ys Pxs Pys)%bool
            end
        end)) as dlist_eqb.
        assert (dlist_eqb = (fun l1 l2 dl1 dl2 => (Induct.dlist_eqb l1 l2 Z.eqb wexpr_eqb dl1 dl2))).
        { clear - Heqdlist_eqb.
          assert (dlist_eqb _ _ (Induct.dnil _ _) (Induct.dnil _ _) = true). {
              rewrite Heqdlist_eqb.
              reflexivity.
          }
          assert (forall x Px xs Pxs, dlist_eqb _ _ (Induct.dnil _ _) (Induct.dcons _ _ x Px xs Pxs) = false). {
              rewrite Heqdlist_eqb.
              reflexivity.
          }
          assert (forall x Px xs Pxs, dlist_eqb _ _ (Induct.dcons _ _ x Px xs Pxs) (Induct.dnil _ _) = false). {
              rewrite Heqdlist_eqb.
              reflexivity.
          }
          assert (forall x Px xs Pxs y Py ys Pys, dlist_eqb _ _ (Induct.dcons _ _ x Px xs Pxs) (Induct.dcons _ _ y Py ys Pys) = ((x =? y)%Z && wexpr_eqb x y Px Py && dlist_eqb xs ys Pxs Pys)%bool). {
              rewrite Heqdlist_eqb.
              reflexivity.
          }
          apply functional_extensionality_dep; intros l1.
          apply functional_extensionality_dep; intros l2.
          apply functional_extensionality; intros dl1.
          apply functional_extensionality; intros dl2.
          generalize dependent dl2.
          generalize dependent l2.
          induction dl1; destruct dl2; intros; [
            rewrite H |
            rewrite H0 |
            rewrite H1 |
            rewrite H2; simpl; rewrite <- IHdl1
          ]; reflexivity.
        }
        rewrite H0 in H1.
        specialize (IHe1 _ _ H1 eq_refl).
        rewrite <- IHe1.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
        reflexivity.
    - intros.
      unfold Q; intros.
      destruct dl2; try discriminate.
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
      reflexivity.
    - unfold Q; intros.
      destruct dl2; try discriminate.
      injection pf as ?; subst.
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
      simpl in H.
      apply andb_true_iff in H; destruct H.
      apply andb_true_iff in H; destruct H.
      specialize (IHe1 _ x0 H1 eq_refl).
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq in IHe1.
      subst.
      unfold Q in IHe0.
      specialize (IHe0 _ _ H0 eq_refl).
      rewrite <- Eqdep.EqdepTheory.eq_rect_eq in IHe0.
      subst; reflexivity.
Qed.

Definition ctype_eqb : (Ctype -> Ctype -> bool) :=
    fun ty1 ty2 =>
        match ty1, ty2 with
        | C8, C8 => true
        | C32, C32 => true
        | C64, C64 => true
        | CPtr, CPtr => true
        | _, _ => false
        end.

Lemma ctype_eqb_eq :
    forall ty1 ty2,
        ctype_eqb ty1 ty2 = true <-> ty1 = ty2.
    intros.
    destruct ty1, ty2; simpl; split; intros; try reflexivity; try discriminate.
Qed.

Definition sep_atom_term_eqb (t1 : SepAtomTerm) (t2 : SepAtomTerm) : bool :=
    match t1, t2 with
    | TSepDataAt addr1 ty1 val1, TSepDataAt addr2 ty2 val2 =>
        (wexpr_eqb _ _ addr1 addr2) && (ctype_eqb ty1 ty2) && (wexpr_eqb _ _ val1 val2)
    | TSepFunc f1 sig1 args1, TSepFunc f2 sig2 args2 =>
        (Z.eqb f1 f2) && (wpred_sig_eqb sig1 sig2) &&
        Induct.dlist_eqb _ _ Z.eqb wexpr_eqb args1 args2
    | _, _ => false
    end.

Lemma sep_atom_term_eqb_refl :
    forall t, sep_atom_term_eqb t t = true.
    destruct t.
    pose proof wexpr_eqb_true.
    - simpl.
      apply andb_true_iff; split; try reflexivity.
      apply andb_true_iff; split; try reflexivity.
      apply wexpr_eqb_refl.
      apply ctype_eqb_eq; reflexivity.
      apply wexpr_eqb_refl.
    - simpl.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      apply Z.eqb_eq; reflexivity.
      apply wpred_sig_eqb_refl.
      apply Induct.dlist_eqb_refl.
      apply Z.eqb_refl.
      apply wexpr_eqb_refl.
Qed.

Lemma sep_atom_term_eqb_true :
    forall t1 t2,
        sep_atom_term_eqb t1 t2 = true -> t1 = t2.
    destruct t1, t2; try discriminate; intros.
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply andb_true_iff in H; destruct H.
        apply wexpr_eqb_true with (pf := eq_refl) in H.
        apply wexpr_eqb_true with (pf := eq_refl) in H0.
        apply ctype_eqb_eq in H1.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H, H0.
        subst; reflexivity.
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply andb_true_iff in H; destruct H.
        apply Z.eqb_eq in H.
        apply wpred_sig_eqb_true in H1.
        subst.
        apply Induct.dlist_eqb_true with (pf := eq_refl) in H0.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H0; subst; reflexivity.
        apply Z.eqb_eq.
        intros.
        apply wexpr_eqb_true with (pf := eq_refl) in H.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H.
        apply H.
Qed.

Lemma sep_atom_term_eqb_false :
    forall t1 t2,
        sep_atom_term_eqb t1 t2 = false -> t1 <> t2.
    intros.
    unfold not; intro H1; subst.
    rewrite sep_atom_term_eqb_refl in H; discriminate.
Qed.

Lemma sep_atom_term_eq_dec :
    forall (a b : SepAtomTerm), {a = b} + {a <> b}.
    intros; destruct (sep_atom_term_eqb a b) eqn : H; [
        apply sep_atom_term_eqb_true in H; apply (left H) |
        apply sep_atom_term_eqb_false in H; apply (right H)
    ].
Qed.

Fixpoint prop_atom_term_eqb (t1 : PropAtomTerm) (t2 : PropAtomTerm) : bool :=
    match t1, t2 with
    | TPropTrue, TPropTrue => true
    | TPropFalse, TPropFalse => true
    | TPropNot p1, TPropNot p2 => prop_atom_term_eqb p1 p2
    | TPropEq ty1 e1 e2, TPropEq ty2 e3 e4 => Z.eqb ty1 ty2 && wexpr_eqb ty1 ty2 e1 e3 && wexpr_eqb ty1 ty2 e2 e4
    | TPropAnd p1 p2, TPropAnd p3 p4 => prop_atom_term_eqb p1 p3 && prop_atom_term_eqb p2 p4
    | TPropOr p1 p2, TPropOr p3 p4 => prop_atom_term_eqb p1 p3 && prop_atom_term_eqb p2 p4
    | TPropImply p1 p2, TPropImply p3 p4 => prop_atom_term_eqb p1 p3 && prop_atom_term_eqb p2 p4
    | TPropIff p1 p2, TPropIff p3 p4 => prop_atom_term_eqb p1 p3 && prop_atom_term_eqb p2 p4
    | TPropFunc f1 sig1 args1, TPropFunc f2 sig2 args2 =>
        (Z.eqb f1 f2) && (wpred_sig_eqb sig1 sig2) &&
        Induct.dlist_eqb _ _ Z.eqb wexpr_eqb args1 args2
    | _, _ => false
    end.

Lemma prop_atom_term_eqb_refl :
    forall t, prop_atom_term_eqb t t = true.
    induction t; simpl;
    try discriminate;
    try solve [ reflexivity | apply IHt | rewrite IHt1, IHt2; reflexivity ].
    apply andb_true_iff; split.
    apply andb_true_iff; split.
    apply Z.eqb_refl.
    apply wexpr_eqb_refl.
    apply wexpr_eqb_refl.
    apply andb_true_iff; split.
    apply andb_true_iff; split.
    apply Z.eqb_refl.
    apply wpred_sig_eqb_refl.
    apply Induct.dlist_eqb_refl.
    apply Z.eqb_refl.
    apply wexpr_eqb_refl.
Qed.

Lemma prop_atom_term_eqb_true :
    forall t1 t2,
        prop_atom_term_eqb t1 t2 = true -> t1 = t2.
    induction t1; destruct t2; intros;
    try discriminate;
    try solve [ reflexivity |
                apply IHt1 in H; subst; reflexivity ].
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply andb_true_iff in H; destruct H.
        apply Z.eqb_eq in H; subst.
        apply wexpr_eqb_true with (pf := eq_refl) in H0.
        apply wexpr_eqb_true with (pf := eq_refl) in H1.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H0, H1.
        subst; reflexivity.
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply IHt1_1 in H; apply IHt1_2 in H0.
        subst; reflexivity.
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply IHt1_1 in H; apply IHt1_2 in H0.
        subst; reflexivity.
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply IHt1_1 in H; apply IHt1_2 in H0.
        subst; reflexivity.
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply IHt1_1 in H; apply IHt1_2 in H0.
        subst; reflexivity.
    -
        simpl in H.
        apply andb_true_iff in H; destruct H.
        apply andb_true_iff in H; destruct H.
        apply Z.eqb_eq in H.
        apply wpred_sig_eqb_true in H1.
        subst.
        apply Induct.dlist_eqb_true with (pf := eq_refl) in H0.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H0; subst; reflexivity.
        apply Z.eqb_eq.
        intros.
        apply wexpr_eqb_true with (pf := eq_refl) in H.
        rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H.
        apply H.
Qed.

Lemma prop_atom_term_eqb_false :
    forall t1 t2,
        prop_atom_term_eqb t1 t2 = false -> t1 <> t2.
    intros.
    unfold not; intro H1; subst.
    rewrite prop_atom_term_eqb_refl in H; discriminate.
Qed.

Lemma prop_atom_term_eq_dec :
    forall (a b : PropAtomTerm), {a = b} + {a <> b}.
    intros; destruct (prop_atom_term_eqb a b) eqn : H; [
        apply prop_atom_term_eqb_true in H; apply (left H) |
        apply prop_atom_term_eqb_false in H; apply (right H)
    ].
Qed.

Definition var_type_eqb (x : VarType) (y : VarType) : bool :=
    match x, y with
    | (x1, ty1), (x2, ty2) => Z.eqb x1 x2 && Z.eqb ty1 ty2
    end.

Lemma var_type_eqb_refl :
    forall x, var_type_eqb x x = true.
    intros.
    destruct x.
    simpl.
    apply andb_true_iff; split; apply Z.eqb_refl.
Qed.

Lemma var_type_eqb_eq :
    forall x y,
        var_type_eqb x y = true <-> x = y.
    intros.
    destruct x, y; simpl.
    split; intros.
    -   apply andb_true_iff in H.
        rewrite ! Z.eqb_eq in H.
        destruct H; subst; reflexivity.
    -   apply andb_true_iff;
        rewrite ! Z.eqb_eq.
        injection H as ?; subst; split; reflexivity.
Qed.

Lemma var_type_eqb_neq :
    forall x y,
        var_type_eqb x y = false <-> (fst x) <> (fst y) \/ (snd x) <> (snd y).
    intros.
    destruct x, y; simpl.
    split; intros.
    -   apply andb_false_iff in H.
        rewrite ! Z.eqb_neq in H.
        assumption.
    -   apply andb_false_iff.
        rewrite ! Z.eqb_neq.
        assumption.
Qed.

Fixpoint not_appear_free_expr ty (e : Wexpr ty) (x : VarType) : bool :=
    match e with
    | EVar y ty' => negb (var_type_eqb x (y, ty'))
    | EConstZ _ => true
    | EField addr _ _ => not_appear_free_expr _ addr x
    | EFunc _ _ args =>
        (fix not_appear_free_dlist l (dl : Induct.dlist Z Wexpr l) : bool :=
            match dl with
            | Induct.dnil => true
            | Induct.dcons _ Px xs Pxs => andb (not_appear_free_expr _ Px x) (not_appear_free_dlist _ Pxs)
            end) _ args
    end.

Fixpoint not_appear_free_dlist l (dl : Induct.dlist Z Wexpr l) (x : VarType) : bool :=
    match dl with
    | Induct.dnil => true
    | Induct.dcons _ Px xs Pxs => andb (not_appear_free_expr _ Px x) (not_appear_free_dlist _ Pxs x)
    end.

Lemma not_appear_free_expr_equiv :
    forall ty e x,
        not_appear_free_expr ty e x = true ->
    forall ty_env (env : environment ty_env) v,
        wexpr_denote ty e _ env = wexpr_denote ty e _ (term_mapping_update_env env (fst x) (snd x) v).
    pose (Q := (fun l dl => forall x, not_appear_free_dlist l dl x = true ->
        forall ty_env (env : environment ty_env) v,
            Induct.dmap (fun a Pa => wexpr_denote _ Pa ty_env env) dl =
            Induct.dmap (fun a Pa => wexpr_denote _ Pa ty_env (term_mapping_update_env env (fst x) (snd x) v)) dl)).
    induction e using wexpr_ind with (Q := Q).
    - intros.
      simpl in H.
      apply negb_true_iff in H.
      destruct x0.
      apply var_type_eqb_neq in H; simpl in *.
      destruct env; simpl.
      rewrite term_mapping_update_neq.
      + reflexivity.
      + assumption.
    -   reflexivity.
    -   intros; simpl.
        simpl in H.
        rewrite <- (IHe _ H).
        destruct env; simpl.
        reflexivity.
    -   intros.
        simpl in *.
        remember (fix not_appear_free_dlist (l : list Z) (dl : Induct.dlist Z Wexpr l) {struct dl} : bool :=
        match dl with
        | @Induct.dnil _ _ => true
        | @Induct.dcons _ _ a Px xs Pxs => (not_appear_free_expr a Px x && not_appear_free_dlist xs Pxs)%bool
        end) as fix_not_appear_free_dlist.
        assert (fix_not_appear_free_dlist = (fun l dl => not_appear_free_dlist l dl x)). {
            clear - Heqfix_not_appear_free_dlist.
            assert (fix_not_appear_free_dlist nil (Induct.dnil _ _) = true). {
                rewrite Heqfix_not_appear_free_dlist.
                reflexivity.
            }
            assert (forall a Px xs Pxs, fix_not_appear_free_dlist (a :: xs) (Induct.dcons _ _ a Px xs Pxs) = (not_appear_free_expr a Px x && fix_not_appear_free_dlist xs Pxs)%bool). {
                rewrite Heqfix_not_appear_free_dlist.
                reflexivity.
            }
            apply functional_extensionality_dep; intros l.
            apply functional_extensionality; intros dl.
            induction dl.
            - simpl; rewrite H; reflexivity.
            - simpl.
              rewrite H0.
              rewrite IHdl.
              reflexivity.
        }
        rewrite H0 in H.
        unfold Q in IHe.
        destruct env; simpl.
        f_equal.
        erewrite IHe.
        reflexivity.
        apply H.
    -   unfold Q.
        intros.
        reflexivity.
    -   unfold Q.
        intros.
        simpl.
        rewrite <- IHe.
        f_equal.
        unfold Q in IHe0.
        rewrite <- IHe0.
        reflexivity.
        simpl in H.
        apply andb_true_iff in H.
        destruct H; assumption.
        simpl in H.
        apply andb_true_iff in H.
        destruct H; assumption.
Qed.

Lemma not_appear_free_dlist_equiv :
    forall l dl x,
        not_appear_free_dlist l dl x = true ->
    forall ty_env (env : environment ty_env) v,
        Induct.dmap (fun a Pa => wexpr_denote _ Pa ty_env env) dl =
        Induct.dmap (fun a Pa => wexpr_denote _ Pa ty_env (term_mapping_update_env env (fst x) (snd x) v)) dl.
    induction dl; intros.
    -   reflexivity.
    -   simpl in H.
        apply andb_true_iff in H.
        destruct H.
        simpl.
        erewrite (not_appear_free_expr_equiv _ _ _ H).
        f_equal.
        apply IHdl.
        assumption.
Qed.

Definition not_appear_free_sep_atom (t : SepAtomTerm) (x : VarType) : bool :=
    match t with
    | TSepDataAt addr ty val =>
    (not_appear_free_expr _ addr x && not_appear_free_expr _ val x)%bool
    | TSepFunc _ _ args => not_appear_free_dlist _ args x
    end.

Lemma not_appear_free_sep_atom_equiv :
    forall t x,
        not_appear_free_sep_atom t x = true ->
    forall ty_env env v,
        sep_atom_term_denote t ty_env env --||-- sep_atom_term_denote t ty_env (term_mapping_update_env env (fst x) (snd x) v).
    induction t; intros.
    -   simpl in H.
        apply andb_true_iff in H.
        destruct H.
        eapply not_appear_free_expr_equiv in H, H0.
        simpl.
        rewrite <- H0.
        rewrite <- H.
        reflexivity.
    -   simpl in H.
        eapply not_appear_free_dlist_equiv in H.
        simpl.
        destruct env; simpl.
        rewrite H.
        simpl.
        reflexivity.
Qed.

Definition not_appear_free_sep_term (t : SepTerm) (x : VarType) : bool :=
    fold_right (fun a b => andb (not_appear_free_sep_atom a x) b) true t.

Lemma not_appear_free_sep_term_equiv :
    forall t x,
        not_appear_free_sep_term t x = true ->
    forall ty_env env v,
        sep_term_denote t ty_env env --||-- sep_term_denote t ty_env (term_mapping_update_env env (fst x) (snd x) v).
    induction t; intros.
    -   simpl; reflexivity.
    -   simpl in *.
        apply andb_true_iff in H.
        destruct H.
        eapply not_appear_free_sep_atom_equiv in H.
        eapply IHt in H0.
        rewrite H0.
        rewrite H.
        reflexivity.
Qed.

Lemma not_appear_free_sep_term_app :
    forall t1 t2 x,
        not_appear_free_sep_term (t1 ++ t2) x =
        (not_appear_free_sep_term t1 x && not_appear_free_sep_term t2 x)%bool.
    induction t1; intros.
    -   simpl; reflexivity.
    -   simpl.
        rewrite <- andb_assoc.
        f_equal.
        apply IHt1.
Qed.

Fixpoint not_appear_free_prop_atom (t : PropAtomTerm) (x : VarType) : bool :=
    match t with
    | TPropTrue => true
    | TPropFalse => true
    | TPropEq ty e1 e2 => andb (not_appear_free_expr ty e1 x) (not_appear_free_expr ty e2 x)
    | TPropNot p => not_appear_free_prop_atom p x
    | TPropAnd p1 p2 => andb (not_appear_free_prop_atom p1 x) (not_appear_free_prop_atom p2 x)
    | TPropOr p1 p2 => andb (not_appear_free_prop_atom p1 x) (not_appear_free_prop_atom p2 x)
    | TPropImply p1 p2 => andb (not_appear_free_prop_atom p1 x) (not_appear_free_prop_atom p2 x)
    | TPropIff p1 p2 => andb (not_appear_free_prop_atom p1 x) (not_appear_free_prop_atom p2 x)
    | TPropFunc _ _ args => not_appear_free_dlist _ args x
    end.

Lemma not_appear_free_prop_atom_equiv :
    forall t x,
        not_appear_free_prop_atom t x = true ->
    forall ty_env env v,
        “ prop_atom_term_denote t ty_env env ” --||-- “ prop_atom_term_denote t ty_env (term_mapping_update_env env (fst x) (snd x) v) ”.
    induction t; intros.
    -   simpl; reflexivity.
    -   simpl; reflexivity.
    -   simpl in *.
        specialize (IHt _ H ty_env env v).
        destruct IHt; split; unfold derivable1, coq_prop, not in *; intros; tauto.
    -   simpl in *.
        apply andb_true_iff in H.
        destruct H.
        eapply not_appear_free_expr_equiv in H; rewrite <- H.
        eapply not_appear_free_expr_equiv in H0; rewrite <- H0.
        reflexivity.
    -   simpl in *.
        apply andb_true_iff in H; destruct H.
        specialize (IHt1 _ H ty_env env v).
        specialize (IHt2 _ H0 ty_env env v).
        destruct IHt1;
        destruct IHt2;
        split; unfold derivable1, coq_prop, not in *; intros; tauto.
    -   simpl in *.
        apply andb_true_iff in H; destruct H.
        specialize (IHt1 _ H ty_env env v).
        specialize (IHt2 _ H0 ty_env env v).
        destruct IHt1;
        destruct IHt2;
        split; unfold derivable1, coq_prop, not in *; intros; tauto.
    -   simpl in *.
        apply andb_true_iff in H; destruct H.
        specialize (IHt1 _ H ty_env env v).
        specialize (IHt2 _ H0 ty_env env v).
        destruct IHt1;
        destruct IHt2;
        split; unfold derivable1, coq_prop, not in *; intros; tauto.
    -   simpl in *.
        apply andb_true_iff in H; destruct H.
        specialize (IHt1 _ H ty_env env v).
        specialize (IHt2 _ H0 ty_env env v).
        destruct IHt1;
        destruct IHt2;
        split; unfold derivable1, coq_prop, not in *; intros; tauto.
    -   simpl in H.
        eapply not_appear_free_dlist_equiv in H.
        simpl.
        rewrite H.
        replace (get_prop_env (term_mapping_update_env env (fst x) (snd x) v)) with (get_prop_env env).
        reflexivity.
        destruct env; reflexivity.
Qed.

Definition not_appear_free_prop_term (t : PropTerm) (x : VarType) : bool :=
    fold_right (fun a b => andb (not_appear_free_prop_atom a x) b) true t.

Lemma not_appear_free_prop_term_equiv :
    forall t x,
        not_appear_free_prop_term t x = true ->
    forall ty_env env v,
        prop_term_denote t ty_env env --||-- prop_term_denote t ty_env (term_mapping_update_env env (fst x) (snd x) v).
    induction t; intros.
    -   simpl; reflexivity.
    -   simpl in *.
        apply andb_true_iff in H.
        destruct H.
        eapply not_appear_free_prop_atom_equiv in H.
        eapply IHt in H0.
        rewrite H.
        rewrite H0.
        reflexivity.
Qed.

Lemma not_appear_free_prop_term_app :
    forall t1 t2 x,
        not_appear_free_prop_term (t1 ++ t2) x =
        (not_appear_free_prop_term t1 x && not_appear_free_prop_term t2 x)%bool.
    induction t1; intros.
    -   simpl; reflexivity.
    -   simpl.
        rewrite <- andb_assoc.
        f_equal.
        apply IHt1.
Qed.

Definition not_appear_free_ps_term (t : PSTerm) (x : VarType) : bool :=
    match t with
    | (p, s) => ((not_appear_free_prop_term p x) &&
                (not_appear_free_sep_term s x))%bool
    end.

Definition not_appear_free_ps_term_equiv :
    forall t x,
        not_appear_free_ps_term t x = true ->
    forall ty_env env v,
        ps_term_denote t ty_env env --||-- ps_term_denote t ty_env (term_mapping_update_env env (fst x) (snd x) v).
    intros.
    destruct t.
    simpl in H.
    apply andb_true_iff in H.
    destruct H.
    eapply not_appear_free_prop_term_equiv in H.
    eapply not_appear_free_sep_term_equiv in H0.
    simpl.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.

Definition not_appear_free_var_list (vl : VarList) (x : VarType) : bool :=
    fold_right (fun a b => andb (negb (var_type_eqb x a)) b) true vl.

Lemma not_appear_free_var_list_in :
    forall vl x,
        not_appear_free_var_list vl x = false -> In x vl.
    induction vl; intros.
    -   simpl in H; discriminate.
    -   simpl in H.
        apply andb_false_iff in H.
        destruct H.
        +   apply negb_false_iff in H.
            apply var_type_eqb_eq in H.
            left; apply (eq_sym H).
        +   specialize (IHvl _ H).
            right; assumption.
Qed.

Lemma not_appear_free_var_list_not_in :
    forall l x, not_appear_free_var_list l x = true -> ~ In x l.
    induction l; intros; simpl in *.
    -   auto.
    -   apply andb_true_iff in H; destruct H.
        apply negb_true_iff, var_type_eqb_neq in H.
        destruct a, x; simpl in *.
        unfold not; intros.
        destruct H1.
        inversion H1.
        lia.
        specialize (IHl _ H0); contradiction.
Qed.

Lemma var_list_in_dec : forall x (l : VarList), {In x l} + {~ In x l}.
    intros.
    destruct (not_appear_free_var_list l x) eqn : ?.
    -   right; apply not_appear_free_var_list_not_in; assumption.
    -   left; apply not_appear_free_var_list_in; assumption.
Qed.

Lemma var_list_forall_denote_in :
    forall vl x,
        In x vl ->
    forall ty_env env v cont,
        var_list_forall_denote vl ty_env env cont <-> var_list_forall_denote vl ty_env (term_mapping_update_env env (fst x) (snd x) v) cont.
    induction vl; intros.
    -   simpl in *. contradiction.
    -   destruct a; simpl in *.
        destruct H.
        +   subst; simpl in *.
            destruct env; split; intros; specialize (H v0); simpl in *.
            rewrite term_mapping_update_shallow.
            assumption.
            rewrite term_mapping_update_shallow in H.
            assumption.
        +   specialize (IHvl _ H).
            destruct (var_type_eqb x (z, z0)) eqn : ?; [
                apply var_type_eqb_eq in Heqb |
                apply var_type_eqb_neq in Heqb
            ].
            *   destruct x, env; injection Heqb as ?; subst; simpl.
                split; intros; specialize (H0 v0).
                rewrite term_mapping_update_shallow; assumption.
                rewrite term_mapping_update_shallow in H0; assumption.
            *   destruct x, env; simpl in *.
                split; intros; specialize (H0 v0).
                rewrite term_mapping_update_swap by assumption.
                rewrite IHvl in H0; apply H0.
                rewrite term_mapping_update_swap in H0 by assumption.
                rewrite IHvl; apply H0.
Qed.

Lemma var_list_forall_denote_equiv :
    forall ty_env x cont vl,
        (forall env v, cont ty_env env <-> cont ty_env (term_mapping_update_env env (fst x) (snd x) v)) ->
        (forall env v, var_list_forall_denote vl ty_env env cont <-> var_list_forall_denote vl ty_env (term_mapping_update_env env (fst x) (snd x) v) cont).
    induction vl; intros.
    -   simpl in *. apply H.
    -   simpl.
        destruct a; simpl.
        destruct (var_type_eqb x (z, z0)) eqn : ?; [
            apply var_type_eqb_eq in Heqb |
            apply var_type_eqb_neq in Heqb
        ];
        destruct env; split; intros; specialize (H0 v0); simpl in *.
        +   subst; simpl in *.
            rewrite term_mapping_update_shallow.
            apply H0.
        +   subst; simpl in *.
            rewrite term_mapping_update_shallow in H0.
            apply H0.
        +   rewrite term_mapping_update_swap by assumption.
            rewrite IHvl in H0; simpl in H0.
            apply H0.
            apply H.
        +   rewrite term_mapping_update_swap in H0 by assumption.
            rewrite IHvl.
            apply H0.
            apply H.
Qed.

Lemma var_list_all_denote_in :
    forall vl x,
        In x vl ->
    forall ty_env env v cont,
        var_list_all_denote vl ty_env env cont --||-- var_list_all_denote vl ty_env (term_mapping_update_env env (fst x) (snd x) v) cont.
    induction vl; intros.
    -   simpl in *. contradiction.
    -   destruct a; simpl in *.
        destruct H.
        +   subst; simpl in *.
            destruct env; unfold CRules.allp, CRules.logic_equiv, CRules.derivable1 in *; split; intros; simpl in *.
            rewrite term_mapping_update_shallow.
            apply H.
            specialize (H a).
            rewrite term_mapping_update_shallow in H.
            assumption.
        +   specialize (IHvl _ H).
            destruct (var_type_eqb x (z, z0)) eqn : ?; [
                apply var_type_eqb_eq in Heqb |
                apply var_type_eqb_neq in Heqb
            ].
            *   destruct x, env; injection Heqb as ?; subst; simpl.
                unfold CRules.allp, CRules.logic_equiv, CRules.derivable1 in *; split; intros; simpl in *; specialize (H0 a).
                rewrite term_mapping_update_shallow; assumption.
                rewrite term_mapping_update_shallow in H0; assumption.
            *   destruct x, env; simpl in *.
                unfold CRules.allp, CRules.logic_equiv, CRules.derivable1 in *; split; intros; simpl in *; specialize (H0 a).
                rewrite term_mapping_update_swap by assumption.
                edestruct IHvl.
                apply H1 in H0.
                apply H0.
                edestruct IHvl.
                rewrite term_mapping_update_swap in H0 by assumption.
                apply H2.
                apply H0.
Qed.

Lemma var_list_all_denote_equiv :
    forall vl x ty_env cont,
        (forall env v, cont ty_env env --||-- cont ty_env (term_mapping_update_env env (fst x) (snd x) v)) ->
        (forall env v, var_list_all_denote vl ty_env env cont --||-- var_list_all_denote vl ty_env (term_mapping_update_env env (fst x) (snd x) v) cont).
    induction vl; intros.
    -   simpl in *. apply H.
    -   simpl.
        destruct a; simpl.
        destruct (var_type_eqb ((fst x), (snd x)) (z, z0)) eqn : Heqb; [
            rewrite var_type_eqb_eq in Heqb; injection Heqb as ?|
            rewrite var_type_eqb_neq in Heqb
        ];
        destruct env;
        unfold CRules.allp, CRules.logic_equiv, CRules.derivable1 in *;
        split; intros; simpl in *.
        +   subst z z0.
            rewrite term_mapping_update_shallow.
            apply H2.
        +   subst z z0.
            specialize (H2 a).
            rewrite term_mapping_update_shallow in H2.
            apply H2.
        +   rewrite term_mapping_update_swap by assumption.
            edestruct IHvl.
            apply H.
            specialize (H1 _ (H0 a)).
            simpl in H1.
            apply H1.
        +   specialize (H0 a).
            rewrite term_mapping_update_swap in H0 by assumption.
            edestruct IHvl.
            apply H.
            apply H2.
            apply H0.
Qed.

Definition not_appear_free_exists (t : ExistsTerm) (x : VarType) : bool :=
    match t with
    | TExists vl t' => not_appear_free_var_list vl x && not_appear_free_ps_term t' x
    end.

Definition not_appear_free_exists_cons :
    forall a t x,
        not_appear_free_exists (ExistsCons a t) x =
        (negb (var_type_eqb x a) && not_appear_free_exists t x)%bool.
    intros.
    destruct a; destruct t; unfold not_appear_free_exists.
    simpl.
    destruct x; simpl.
    rewrite andb_assoc.
    reflexivity.
Qed.
    
Definition not_appear_free_exists_equiv :
    forall t x,
        not_appear_free_exists t x = true ->
    forall ty_env env v,
        exists_term_denote t ty_env env --||-- exists_term_denote t ty_env (term_mapping_update_env env (fst x) (snd x) v).
    induction t using ind_exists; intros.
    -   simpl in *.
        apply not_appear_free_ps_term_equiv.
        apply H.
    -   destruct x; simpl in *.
        rewrite ! exists_term_denote_cons.
        rewrite not_appear_free_exists_cons in H.
        apply andb_true_iff in H.
        destruct H.
        apply negb_true_iff in H.
        simpl in H.
        destruct x0; apply var_type_eqb_neq in H; simpl in *.
        split; Intros v0; Exists v0.
        +   rewrite (IHt _ H0 _ _ v).
            destruct env; simpl.
            rewrite term_mapping_update_swap.
            entailer!.
            lia.
        +   rewrite (IHt _ H0 _ (term_mapping_update_env env z z0 v0) v).
            destruct env; simpl.
            rewrite term_mapping_update_swap.
            entailer!.
            lia.
Qed.

Fixpoint erase_sep (t : SepTerm) (H : SepAtomTerm) : option SepTerm :=
    match t with
    | nil => None
    | cons x xs =>
        if sep_atom_term_eqb x H
        then Some xs
        else match erase_sep xs H with
             | Some xs' => Some (x :: xs')
             | None => None
             end
    end.

Fixpoint erase_prop (t : PropTerm) (H : PropAtomTerm) : option PropTerm :=
    match t with
    | nil => None
    | cons x xs =>
        if prop_atom_term_eqb x H
        then Some xs
        else match erase_prop xs H with
             | Some xs' => Some (x :: xs')
             | None => None
             end
    end.

Fixpoint erase_list_sep (t1 : SepTerm) (t2 : SepTerm) : option SepTerm :=
    match t2 with
    | nil => Some t1
    | cons x xs => match erase_list_sep t1 xs with
                  | Some t1' => erase_sep t1' x
                  | None => None
                  end
    end.

Fixpoint erase_list_prop (t1 : PropTerm) (t2 : PropTerm) : option PropTerm :=
    match t2 with
    | nil => Some t1
    | cons x xs => match erase_list_prop t1 xs with
                  | Some t1' => erase_prop t1' x
                  | None => None
                  end
    end.

Definition add_ps_sep (t : PSTerm) (H : SepAtomTerm) :=
    match t with
    | (p, s) => (p, add_sep s H)
    end.

Definition add_ps_prop (t : PSTerm) (H : PropAtomTerm) :=
    match t with
    | (p, s) => (add_prop p H, s)
    end.

Definition erase_ps_sep (t : PSTerm) (H : SepAtomTerm) : option PSTerm :=
    match t with
    | (p, s) =>
        match (erase_sep s H) with
        | Some s' => Some (p, s')
        | None => None
        end
    end.

Definition erase_ps_prop (t : PSTerm) (H : PropAtomTerm) : option PSTerm :=
    match t with
    | (p, s) =>
        match (erase_prop p H) with
        | Some p' => Some (p', s)
        | None => None
        end
    end.

Definition add_exists_sep (t : ExistsTerm) (H : SepAtomTerm) :=
    match t with
    | TExists vl t' => TExists vl (add_ps_sep t' H)
    end.

Definition add_exists_prop (t : ExistsTerm) (H : PropAtomTerm) :=
    match t with
    | TExists vl t' => TExists vl (add_ps_prop t' H)
    end.

Definition erase_exists_sep (t : ExistsTerm) (H : SepAtomTerm) : option ExistsTerm :=
    match t with
    | TExists vl t' =>
        match (erase_ps_sep t' H) with
        | Some s' => Some (TExists vl s')
        | None => None
        end
    end.

Definition erase_exists_prop (t : ExistsTerm) (H : PropAtomTerm) : option ExistsTerm :=
    match t with
    | TExists vl t' =>
        match (erase_ps_prop t' H) with
        | Some p' => Some (TExists vl p')
        | None => None
        end
    end.

Definition left_add_forall_sep (t : ForallTerm) (H : SepAtomTerm) :=
    match t with
    | TForall vl pre post => TForall vl (add_ps_sep pre H) post
    end.

Definition left_add_forall_prop (t : ForallTerm) (H : PropAtomTerm) :=
    match t with
    | TForall vl pre post => TForall vl (add_ps_prop pre H) post
    end.

Definition right_add_forall_sep (t : ForallTerm) (H : SepAtomTerm) :=
    match t with
    | TForall vl pre post => TForall vl pre (add_exists_sep post H)
    end.

Definition right_add_forall_prop (t : ForallTerm) (H : PropAtomTerm) :=
    match t with
    | TForall vl pre post => TForall vl pre (add_exists_prop post H)
    end.

Definition left_erase_forall_sep (t : ForallTerm) (H : SepAtomTerm) : option ForallTerm :=
    match t with
    | TForall vl pre post =>
        match (erase_ps_sep pre H) with
        | Some pre' => Some (TForall vl pre' post)
        | None => None
        end
    end.

Definition left_erase_forall_prop (t : ForallTerm) (H : PropAtomTerm) : option ForallTerm :=
    match t with
    | TForall vl pre post =>
        match (erase_ps_prop pre H) with
        | Some pre' => Some (TForall vl pre' post)
        | None => None
        end
    end.

Definition right_erase_forall_sep (t : ForallTerm) (H : SepAtomTerm) : option ForallTerm :=
    match t with
    | TForall vl pre post =>
        match (erase_exists_sep post H) with
        | Some post' => Some (TForall vl pre post')
        | None => None
        end
    end.

Definition right_erase_forall_prop (t : ForallTerm) (H : PropAtomTerm) : option ForallTerm :=
    match t with
    | TForall vl pre post =>
        match (erase_exists_prop post H) with
        | Some post' => Some (TForall vl pre post')
        | None => None
        end
    end.

Definition right_exists_add_forall (v : VarType) (t : ForallTerm) :=
    match t with
    | TForall vl pre post => TForall vl pre (ExistsCons v post)
    end.

Definition apply_operation (op : Operation) (t : option ForallTerm) : option ForallTerm :=
    match t with
    | Some t =>
        match op with
        | OAssume _ => Some t
        | OLeftSepAdd H => Some (left_add_forall_sep t H)
        | OLeftSepErase H => left_erase_forall_sep t H
        | ORightSepAdd H => Some (right_add_forall_sep t H)
        | ORightSepErase H => right_erase_forall_sep t H
        | OLeftPropAdd H => Some (left_add_forall_prop t H)
        | OLeftPropErase H => left_erase_forall_prop t H
        | ORightPropAdd H => Some (right_add_forall_prop t H)
        | ORightPropErase H => right_erase_forall_prop t H
        | OForallAdd v => Some (ForallCons v t)
        | ORightExistsAdd v => Some (right_exists_add_forall v t)
        end
    | None => None
    end.

Definition apply_operations (t : ForallTerm) (ops : list Operation) : option ForallTerm :=
    fold_right apply_operation (Some t) ops.

Lemma apply_operations_cons :
    forall op ops t,
    apply_operations t (op :: ops) = apply_operation op (apply_operations t ops).
    intros; simpl; reflexivity.
Qed.

Inductive RamificationCondition : Type :=
| RC (fl : VarList) (sc : PropTerm) (p p' q' q : PropTerm) (P P' Q' Q : SepTerm)
.

Inductive SideCondition : Type :=
| SC (pre : PSTerm) (post : PropAtomTerm)
.

Definition var_list_insert (x : VarType) (l : VarList) : VarList :=
    if not_appear_free_var_list l x then cons x l else l.

Lemma var_list_insert_in :
    forall x l, In x (var_list_insert x l).
    intros.
    unfold var_list_insert.
    destruct (not_appear_free_var_list l x) eqn : ?.
    -   left; reflexivity.
    -   apply not_appear_free_var_list_in in Heqb.
        assumption.
Qed.

Lemma var_list_insert_in_equiv :
    forall x a l, In x (var_list_insert a l) <-> a = x \/ In x l.
    split; intros.
    -   unfold var_list_insert in *.
        destruct (not_appear_free_var_list l a) eqn : ?.
        assumption.
        right; assumption.
    -   destruct H.
        subst; apply var_list_insert_in.
        unfold var_list_insert; destruct (not_appear_free_var_list l a) eqn : ?.
        right; assumption.
        assumption.
Qed.

Lemma var_list_insert_not_in_equiv :
    forall x a l, ~ In x (var_list_insert a l) <-> a <> x /\ ~ In x l.
    split; intros.
    -   unfold var_list_insert in *.
        destruct (not_appear_free_var_list l a) eqn : ?.
        +   simpl in H; tauto.
        +   apply not_appear_free_var_list_in in Heqb.
            split; [ unfold not; intros; subst; contradiction | assumption ].
    -   unfold var_list_insert in *.
        destruct (not_appear_free_var_list l a) eqn : ?.
        +   simpl; tauto.
        +   tauto.
Qed.

Definition var_list_merge (l1 : VarList) (l2 : VarList) : VarList :=
    fold_left (fun a b => var_list_insert b a) l2 l1.

Lemma var_list_merge_in :
    forall x l1 l2,
        In x (var_list_merge l1 l2) -> In x l1 \/ In x l2.
    intros; generalize dependent l1; induction l2; intros; simpl in *.
    -   left; assumption.
    -   apply IHl2 in H.
        destruct H.
        +   apply var_list_insert_in_equiv in H.
            tauto.
        +   tauto.
Qed.

Lemma var_list_merge_not_in :
    forall x l1 l2,
        ~ In x (var_list_merge l1 l2) -> ~ In x l1 /\ ~ In x l2.
    intros; generalize dependent l1; induction l2; intros; simpl in *.
    -   split; tauto.
    -   apply IHl2 in H.
        destruct H.
        apply var_list_insert_not_in_equiv in H.
        tauto.
Qed.

Lemma var_list_merge_in_left :
    forall x l1 l2, In x l1 -> In x (var_list_merge l1 l2).
    intros; generalize dependent l1; induction l2; intros; simpl in *.
    -   assumption.
    -   apply IHl2.
        apply var_list_insert_in_equiv.
        right; assumption.
Qed.

Lemma var_list_merge_in_right :
    forall x l1 l2, In x l2 -> In x (var_list_merge l1 l2).
    intros; generalize dependent l1; induction l2; intros; simpl in *.
    -   contradiction.
    -   destruct H.
        + apply var_list_merge_in_left.
          apply var_list_insert_in_equiv.
          left; assumption.
        + apply IHl2; assumption.
Qed.

Fixpoint get_var_list_expr ty (e : Wexpr ty) : VarList :=
    match e with
    | EVar x ty => cons (x, ty) nil
    | EConstZ val => nil
    | EField addr _ _ => get_var_list_expr _ addr
    | EFunc _ _ args =>
        (fix get_var_list_dlist l (dl : Induct.dlist Z Wexpr l) : VarList :=
            match dl with
            | Induct.dnil => nil
            | Induct.dcons _ Px xs Pxs => var_list_merge (get_var_list_expr _ Px) (get_var_list_dlist _ Pxs)
            end) _ args
    end.

Fixpoint get_var_list_dlist l (dl : Induct.dlist Z Wexpr l) : VarList :=
    match dl with
    | Induct.dnil => nil
    | Induct.dcons _ Px xs Pxs => var_list_merge (get_var_list_expr _ Px) (get_var_list_dlist _ Pxs)
    end.

Lemma get_var_list_not_appear_free_true_expr :
    forall ty (e : Wexpr ty) x,
        not_appear_free_expr ty e x = true ->
        ~ In x (get_var_list_expr ty e).
    pose (Q := (fun l dl =>
        forall x,
            not_appear_free_dlist l dl x = true ->
            ~ In x (get_var_list_dlist l dl))).
    induction e using wexpr_ind with (Q := Q); intros.
    -   simpl in *.
        apply negb_true_iff in H.
        apply var_type_eqb_neq in H.
        destruct x0; simpl in *.
        unfold not in *; intros.
        destruct H0; try assumption.
        inversion H0.
        destruct H; apply H; lia.
    -   simpl in *.
        auto.
    -   simpl in *.
        apply IHe; assumption.
    -   simpl in *.
        remember (fix not_appear_free_dlist (l : list Z) (dl : Induct.dlist Z Wexpr l) {struct dl} : bool :=
        match dl with
        | @Induct.dnil _ _ => true
        | @Induct.dcons _ _ a Px xs Pxs => (not_appear_free_expr a Px x && not_appear_free_dlist xs Pxs)%bool
        end) as fix_not_appear_free_dlist.
        assert (fix_not_appear_free_dlist = (fun l dl => not_appear_free_dlist l dl x)). {
            clear - Heqfix_not_appear_free_dlist.
            assert (fix_not_appear_free_dlist nil (Induct.dnil _ _) = true). {
                rewrite Heqfix_not_appear_free_dlist.
                reflexivity.
            }
            assert (forall a Px xs Pxs, fix_not_appear_free_dlist (a :: xs) (Induct.dcons _ _ a Px xs Pxs) = (not_appear_free_expr a Px x && fix_not_appear_free_dlist xs Pxs)%bool). {
                rewrite Heqfix_not_appear_free_dlist.
                reflexivity.
            }
            apply functional_extensionality_dep; intros l.
            apply functional_extensionality; intros dl.
            induction dl.
            - simpl; rewrite H; reflexivity.
            - simpl.
              rewrite H0.
              rewrite IHdl.
              reflexivity.
        }
        subst; rewrite H0 in *; clear H0.
        remember ((fix get_var_list_dlist (l : list Z) (dl : Induct.dlist Z Wexpr l) {struct dl} : VarList :=
        match dl with
        | @Induct.dnil _ _ => nil
        | @Induct.dcons _ _ a Px xs Pxs => var_list_merge (get_var_list_expr a Px) (get_var_list_dlist xs Pxs)
        end)) as fix_get_var_list_dlist.
        assert (fix_get_var_list_dlist = (fun l dl => get_var_list_dlist l dl)). {
            clear - Heqfix_get_var_list_dlist.
            assert (fix_get_var_list_dlist nil (Induct.dnil _ _) = nil). {
                rewrite Heqfix_get_var_list_dlist.
                reflexivity.
            }
            assert (forall a Px xs Pxs, fix_get_var_list_dlist (a :: xs) (Induct.dcons _ _ a Px xs Pxs) = var_list_merge (get_var_list_expr a Px) (fix_get_var_list_dlist xs Pxs)). {
                rewrite Heqfix_get_var_list_dlist.
                reflexivity.
            }
            apply functional_extensionality_dep; intros l.
            apply functional_extensionality; intros dl.
            induction dl.
            - simpl; rewrite H; reflexivity.
            - simpl.
              rewrite H0.
              rewrite IHdl.
              reflexivity.
        }
        subst; rewrite H0 in *; clear H0.
        unfold Q in IHe.
        apply IHe; assumption.
    -   unfold Q; intros; simpl in *; auto.
    -   unfold Q in *; intros; simpl in *.
        apply andb_true_iff in H.
        destruct H.
        unfold not; intros.
        apply var_list_merge_in in H1.
        destruct H1.
        +   apply (IHe _ H H1).
        +   apply (IHe0 _ H0 H1).
Qed.

Lemma get_var_list_not_appear_free_false_expr:
    forall ty (e : Wexpr ty) x,
        not_appear_free_expr ty e x = false ->
        In x (get_var_list_expr ty e).
    pose (Q := (fun l dl =>
        forall x,
            not_appear_free_dlist l dl x = false ->
            In x (get_var_list_dlist l dl))).
    induction e using wexpr_ind with (Q := Q); intros.
    -   simpl in *.
        apply negb_false_iff in H.
        apply var_type_eqb_eq in H; subst.
        left; reflexivity.
    -   simpl in *.
        discriminate.
    -   simpl in *.
        apply IHe; assumption.
    -   simpl in *.
        remember (fix not_appear_free_dlist (l : list Z) (dl : Induct.dlist Z Wexpr l) {struct dl} : bool :=
        match dl with
        | @Induct.dnil _ _ => true
        | @Induct.dcons _ _ a Px xs Pxs => (not_appear_free_expr a Px x && not_appear_free_dlist xs Pxs)%bool
        end) as fix_not_appear_free_dlist.
        assert (fix_not_appear_free_dlist = (fun l dl => not_appear_free_dlist l dl x)). {
            clear - Heqfix_not_appear_free_dlist.
            assert (fix_not_appear_free_dlist nil (Induct.dnil _ _) = true). {
                rewrite Heqfix_not_appear_free_dlist.
                reflexivity.
            }
            assert (forall a Px xs Pxs, fix_not_appear_free_dlist (a :: xs) (Induct.dcons _ _ a Px xs Pxs) = (not_appear_free_expr a Px x && fix_not_appear_free_dlist xs Pxs)%bool). {
                rewrite Heqfix_not_appear_free_dlist.
                reflexivity.
            }
            apply functional_extensionality_dep; intros l.
            apply functional_extensionality; intros dl.
            induction dl.
            - simpl; rewrite H; reflexivity.
            - simpl.
              rewrite H0.
              rewrite IHdl.
              reflexivity.
        }
        subst; rewrite H0 in *; clear H0.
        remember ((fix get_var_list_dlist (l : list Z) (dl : Induct.dlist Z Wexpr l) {struct dl} : VarList :=
        match dl with
        | @Induct.dnil _ _ => nil
        | @Induct.dcons _ _ a Px xs Pxs => var_list_merge (get_var_list_expr a Px) (get_var_list_dlist xs Pxs)
        end)) as fix_get_var_list_dlist.
        assert (fix_get_var_list_dlist = (fun l dl => get_var_list_dlist l dl)). {
            clear - Heqfix_get_var_list_dlist.
            assert (fix_get_var_list_dlist nil (Induct.dnil _ _) = nil). {
                rewrite Heqfix_get_var_list_dlist.
                reflexivity.
            }
            assert (forall a Px xs Pxs, fix_get_var_list_dlist (a :: xs) (Induct.dcons _ _ a Px xs Pxs) = var_list_merge (get_var_list_expr a Px) (fix_get_var_list_dlist xs Pxs)). {
                rewrite Heqfix_get_var_list_dlist.
                reflexivity.
            }
            apply functional_extensionality_dep; intros l.
            apply functional_extensionality; intros dl.
            induction dl.
            - simpl; rewrite H; reflexivity.
            - simpl.
              rewrite H0.
              rewrite IHdl.
              reflexivity.
        }
        subst; rewrite H0 in *; clear H0.
        unfold Q in IHe.
        apply IHe; assumption.
    -   unfold Q; simpl in *; discriminate.
    -   unfold Q in *; simpl in *; intros.
        apply andb_false_iff in H; destruct H.
        apply (var_list_merge_in_left _ _ _ (IHe _ H)).
        apply (var_list_merge_in_right _ _ _ (IHe0 _ H)).
Qed.

Lemma get_var_list_not_appear_free_true_dlist :
    forall l (dl : Induct.dlist Z Wexpr l) x,
        not_appear_free_dlist l dl x = true ->
        ~ In x (get_var_list_dlist l dl).
    induction dl; intros.
    -   simpl; auto.
    -   simpl in H.
        apply andb_true_iff in H.
        destruct H.
        simpl.
        specialize (IHdl _ H0).
        apply get_var_list_not_appear_free_true_expr in H.
        unfold not; intros.
        apply var_list_merge_in in H1.
        destruct H1; contradiction.
Qed.

Lemma get_var_list_not_appear_free_false_dlist :
    forall l (dl : Induct.dlist Z Wexpr l) x,
        not_appear_free_dlist l dl x = false ->
        In x (get_var_list_dlist l dl).
    induction dl; intros.
    -   simpl; discriminate.
    -   simpl in H.
        apply andb_false_iff in H.
        destruct H; simpl.
        +   apply get_var_list_not_appear_free_false_expr in H.
            apply var_list_merge_in_left; assumption.
        +   apply IHdl in H.
            apply var_list_merge_in_right; assumption.
Qed.

Definition get_var_list_sep_atom (H : SepAtomTerm) : VarList :=
    match H with
    | TSepDataAt addr ty val =>
        var_list_merge (get_var_list_expr _ addr) (get_var_list_expr _ val)
    | TSepFunc _ _ args => get_var_list_dlist _ args
    end.

Lemma get_var_list_not_appear_free_true_sep_atom :
    forall H x,
        not_appear_free_sep_atom H x = true ->
        ~ In x (get_var_list_sep_atom H).
    intros.
    destruct H; simpl in *.
    -   apply andb_true_iff in H0.
        destruct H0.
        eapply get_var_list_not_appear_free_true_expr in H.
        eapply get_var_list_not_appear_free_true_expr in H0.
        unfold not; intros.
        apply var_list_merge_in in H1.
        destruct H1; contradiction.
    -   apply get_var_list_not_appear_free_true_dlist in H0.
        assumption.
Qed.

Lemma get_var_list_not_appear_free_false_sep_atom :
    forall H x,
        not_appear_free_sep_atom H x = false ->
        In x (get_var_list_sep_atom H).
    intros.
    destruct H; simpl in *.
    -   apply andb_false_iff in H0; destruct H0.
        +   apply get_var_list_not_appear_free_false_expr in H.
            apply var_list_merge_in_left; assumption.
        +   apply get_var_list_not_appear_free_false_expr in H.
            apply var_list_merge_in_right; assumption.
    -   apply get_var_list_not_appear_free_false_dlist in H0.
        assumption.
Qed.

Definition get_var_list_sep_term (l : SepTerm) : VarList :=
    fold_right (fun a b => var_list_merge (get_var_list_sep_atom a) b) nil l.

Lemma get_var_list_not_appear_free_true_sep :
    forall l x,
        not_appear_free_sep_term l x = true ->
        ~ In x (get_var_list_sep_term l).
    induction l; intros.
    -   simpl; auto.
    -   simpl in H.
        apply andb_true_iff in H.
        destruct H.
        specialize (IHl _ H0).
        apply get_var_list_not_appear_free_true_sep_atom in H.
        unfold not; intros.
        apply var_list_merge_in in H1.
        destruct H1; contradiction.
Qed.

Lemma get_var_list_not_appear_free_false_sep :
    forall l x,
        not_appear_free_sep_term l x = false ->
        In x (get_var_list_sep_term l).
    induction l; intros.
    -   simpl; discriminate.
    -   simpl in H.
        apply andb_false_iff in H.
        destruct H.
        apply get_var_list_not_appear_free_false_sep_atom in H.
        apply var_list_merge_in_left; assumption.
        apply IHl in H.
        apply var_list_merge_in_right; assumption.
Qed.

Fixpoint get_var_list_prop_atom (H : PropAtomTerm) : VarList :=
    match H with
    | TPropTrue => nil
    | TPropFalse => nil
    | TPropNot p => get_var_list_prop_atom p
    | TPropEq ty e1 e2 => var_list_merge (get_var_list_expr _ e1) (get_var_list_expr _ e2)
    | TPropAnd p1 p2 => var_list_merge (get_var_list_prop_atom p1) (get_var_list_prop_atom p2)
    | TPropOr p1 p2 => var_list_merge (get_var_list_prop_atom p1) (get_var_list_prop_atom p2)
    | TPropImply p1 p2 => var_list_merge (get_var_list_prop_atom p1) (get_var_list_prop_atom p2)
    | TPropIff p1 p2 => var_list_merge (get_var_list_prop_atom p1) (get_var_list_prop_atom p2)
    | TPropFunc _ _ args => get_var_list_dlist _ args
    end.

Lemma get_var_list_not_appear_free_true_prop_atom :
    forall t x,
        not_appear_free_prop_atom t x = true ->
        ~ In x (get_var_list_prop_atom t).
    induction t; intros; simpl in *; auto.
    -   apply andb_true_iff in H; destruct H.
        eapply get_var_list_not_appear_free_true_expr in H.
        eapply get_var_list_not_appear_free_true_expr in H0.
        unfold not; intros.
        apply var_list_merge_in in H1.
        destruct H1; contradiction.
    -   apply andb_true_iff in H; destruct H.
        unfold not; intros H1; apply var_list_merge_in in H1.
        specialize (IHt1 _ H); specialize (IHt2 _ H0).
        tauto.
    -   apply andb_true_iff in H; destruct H.
        unfold not; intros H1; apply var_list_merge_in in H1.
        specialize (IHt1 _ H); specialize (IHt2 _ H0).
        tauto.
    -   apply andb_true_iff in H; destruct H.
        unfold not; intros H1; apply var_list_merge_in in H1.
        specialize (IHt1 _ H); specialize (IHt2 _ H0).
        tauto.
    -   apply andb_true_iff in H; destruct H.
        unfold not; intros H1; apply var_list_merge_in in H1.
        specialize (IHt1 _ H); specialize (IHt2 _ H0).
        tauto.
    -   apply get_var_list_not_appear_free_true_dlist in H.
        assumption.
Qed.

Lemma get_var_list_not_appear_free_false_prop_atom :
    forall t x,
        not_appear_free_prop_atom t x = false ->
        In x (get_var_list_prop_atom t).
    induction t; intros; simpl in *; try discriminate.
    -   apply IHt; apply H.
    -   apply andb_false_iff in H; destruct H.
        + apply get_var_list_not_appear_free_false_expr in H.
          apply var_list_merge_in_left; apply H.
        + apply get_var_list_not_appear_free_false_expr in H.
          apply var_list_merge_in_right; apply H.
    -   apply andb_false_iff in H; destruct H.
        apply var_list_merge_in_left; apply IHt1; apply H.
        apply var_list_merge_in_right; apply IHt2; apply H.
    -   apply andb_false_iff in H; destruct H.
        apply var_list_merge_in_left; apply IHt1; apply H.
        apply var_list_merge_in_right; apply IHt2; apply H.
    -   apply andb_false_iff in H; destruct H.
        apply var_list_merge_in_left; apply IHt1; apply H.
        apply var_list_merge_in_right; apply IHt2; apply H.
    -   apply andb_false_iff in H; destruct H.
        apply var_list_merge_in_left; apply IHt1; apply H.
        apply var_list_merge_in_right; apply IHt2; apply H.
    -   apply get_var_list_not_appear_free_false_dlist in H.
        assumption.
Qed.

Definition get_var_list_prop_term (l : PropTerm) : VarList :=
    fold_right (fun a b => var_list_merge (get_var_list_prop_atom a) b) nil l.

Lemma get_var_list_not_appear_free_true_prop :
    forall l x,
        not_appear_free_prop_term l x = true ->
        ~ In x (get_var_list_prop_term l).
    induction l; intros; simpl in *.
    -   auto.
    -   apply andb_true_iff in H.
        destruct H.
        specialize (IHl _ H0).
        apply get_var_list_not_appear_free_true_prop_atom in H.
        unfold not; intros.
        apply var_list_merge_in in H1.
        tauto.
Qed.

Lemma get_var_list_not_appear_free_false_prop :
    forall l x,
        not_appear_free_prop_term l x = false ->
        In x (get_var_list_prop_term l).
    induction l; intros; simpl in *.
    -   discriminate.
    -   apply andb_false_iff in H.
        destruct H.
        apply get_var_list_not_appear_free_false_prop_atom in H.
        apply var_list_merge_in_left; assumption.
        apply IHl in H.
        apply var_list_merge_in_right; assumption.
Qed.

Definition get_var_list_ps_term (t : PSTerm) : VarList :=
    match t with
    | (p, s) => var_list_merge (get_var_list_prop_term p) (get_var_list_sep_term s)
    end.

Lemma get_var_list_not_appear_free_true_ps :
    forall l x,
        not_appear_free_ps_term l x = true ->
        ~ In x (get_var_list_ps_term l).
    destruct l; intros; simpl.
    simpl in H; apply andb_true_iff in H.
    destruct H.
    apply get_var_list_not_appear_free_true_prop in H.
    apply get_var_list_not_appear_free_true_sep in H0.
    unfold not in *; intros; apply var_list_merge_in in H1.
    tauto.
Qed.

Lemma get_var_list_not_appear_free_false_ps :
    forall l x,
        not_appear_free_ps_term l x = false ->
        In x (get_var_list_ps_term l).
    destruct l; intros; simpl.
    simpl in H; apply andb_false_iff in H.
    destruct H.
    apply get_var_list_not_appear_free_false_prop in H.
    apply var_list_merge_in_left; assumption.
    apply get_var_list_not_appear_free_false_sep in H.
    apply var_list_merge_in_right; assumption.
Qed.

(* Definition get_var_list_rc (r : RamificationCondition) : VarList :=
    match r with
    | RC sc p p' q' q P P' Q' Q =>
        var_list_merge (get_var_list_sep_term (P ++ P' ++ Q' ++ Q))
                       (get_var_list_prop_term (sc ++ p ++ p' ++ q' ++ q))
    end. *)

Definition rc_denote_post_atom q' Q' q Q ty_env (env : environment ty_env) : expr :=
    ps_term_denote (q', Q') _ env -* ps_term_denote (q, Q) _ env.

Lemma rc_denote_post_atom_equiv :
    forall q' Q' q Q x,
        not_appear_free_ps_term (q ++ q', Q ++ Q') x = true ->
    forall ty_env env v,
        rc_denote_post_atom q' Q' q Q ty_env env --||-- rc_denote_post_atom q' Q' q Q _ (term_mapping_update_env env (fst x) (snd x) v).
    intros; unfold rc_denote_post_atom, ps_term_denote.
    unfold not_appear_free_ps_term in H; simpl in H; apply andb_true_iff in H as [? ?].
    simpl in *.
    rewrite not_appear_free_sep_term_app in H0; apply andb_true_iff in H0 as [? ?].
    rewrite not_appear_free_prop_term_app in H; apply andb_true_iff in H as [? ?].
    eapply not_appear_free_sep_term_equiv in H0, H1.
    eapply not_appear_free_prop_term_equiv in H, H2.
    unfold rc_denote_post_atom.
    apply wand_equiv.
    rewrite <- H1, H2. reflexivity.
    rewrite <- H0, H. reflexivity.
Qed.

Definition var_list_intersec (l1 l2 : VarList) : VarList :=
    filter (fun x => negb (not_appear_free_var_list l2 x)) l1.

Lemma var_list_intersec_in :
    forall l1 l2 x,
        In x (var_list_intersec l1 l2) -> In x l1 /\ In x l2.
    induction l1; intros.
    -   simpl in H; contradiction.
    -   simpl in H.
        destruct (not_appear_free_var_list l2 a) eqn : ?.
        +   apply IHl1 in H.
            destruct H.
            split; [ right; assumption | assumption ].
        +   simpl in H.
            destruct H.
            *   apply not_appear_free_var_list_in in Heqb.
                subst.
                split; [ left; reflexivity | assumption ].
            *   apply IHl1 in H.
                destruct H.
                split; [ right; assumption | assumption ].
Qed.

Definition var_list_minus (l1 l2 : VarList) : VarList :=
    filter (fun x => not_appear_free_var_list l2 x) l1.

Lemma var_list_minus_in :
    forall x l1 l2,
        In x (var_list_minus l1 l2) <-> In x l1 /\ ~ In x l2.
    split; generalize dependent l2; induction l1; intros.
    -   contradiction.
    -   simpl in H.
        destruct (not_appear_free_var_list l2 a) eqn : ?; [
            apply not_appear_free_var_list_not_in in Heqb |
            apply not_appear_free_var_list_in in Heqb
        ].
        +   simpl in *.
            destruct H.
            *   subst; tauto.
            *   apply IHl1 in H.
                tauto.
        +   apply IHl1 in H.
            simpl.
            tauto.
    -   destruct H.
        simpl in H; contradiction.
    -   simpl.
        destruct H.
        destruct (not_appear_free_var_list l2 a) eqn : ?; [
            apply not_appear_free_var_list_not_in in Heqb |
            apply not_appear_free_var_list_in in Heqb
        ].
        +   simpl in *.
            destruct H.
            *   subst; tauto.
            *   right; apply IHl1; tauto.
        +   simpl in *.
            apply IHl1.
            destruct H.
            *   subst; contradiction.
            *   split; assumption.
Qed.

Inductive unqvl : VarList -> Prop :=
| unqvl_nil : unqvl nil
| unqvl_cons : forall x l, ~ In x l -> unqvl l -> unqvl (x :: l)
.

Lemma var_list_merge_preserse_unqvl :
    forall l1 l2,
        unqvl l1 ->
        unqvl l2 ->
        unqvl (var_list_merge l1 l2).
    intros; generalize dependent l1; induction l2; intros.
    - apply H.
    - simpl in *.
      inversion H0; subst.
      specialize (IHl2 H4).
      unfold var_list_insert.
      destruct (not_appear_free_var_list l1 a) eqn : ?.
      + apply IHl2.
        constructor.
        apply not_appear_free_var_list_not_in in Heqb.
        assumption.
        assumption.
      + apply IHl2.
        assumption.
Qed.

Lemma perm_unqvl :
    forall l1 l2,
        Permutation l1 l2 ->
        unqvl l1 -> unqvl l2.
    intros.
    induction H.
    - constructor.
    - inversion H0; subst.
      constructor; auto.
      rewrite <- H.
      assumption.
    - inversion H0; subst.
      inversion H3; subst.
      repeat (constructor; auto).
      all: simpl in *; try tauto.
      unfold not; intros.
      destruct H.
      symmetry in H; tauto.
      tauto.
    - auto.
Qed.

Lemma get_var_list_expr_unqvl :
    forall ty (e : Wexpr ty),
        unqvl (get_var_list_expr ty e).
    pose (Q := (fun l dl => unqvl (get_var_list_dlist l dl))).
    intros.
    induction e using wexpr_ind with (Q := Q).
    -   simpl.
        constructor; [ | constructor ].
        tauto.
    -   constructor.
    -   apply IHe.
    -   apply IHe.
    -   unfold Q; simpl.
        constructor.
    -   unfold Q; simpl.
        apply var_list_merge_preserse_unqvl.
        apply IHe.
        apply IHe0.
Qed.

Lemma get_var_list_dlist_unqvl :
    forall l dl, unqvl (get_var_list_dlist l dl).
    induction dl.
    - simpl; constructor.
    - simpl.
      apply var_list_merge_preserse_unqvl.
      apply get_var_list_expr_unqvl.
      apply IHdl.
Qed.

Lemma get_var_list_prop_atom_unqvl :
    forall p, unqvl (get_var_list_prop_atom p).
    induction p;
    try constructor;
    try assumption;
    try (apply var_list_merge_preserse_unqvl; apply get_var_list_expr_unqvl);
    try (apply var_list_merge_preserse_unqvl; assumption);
    try apply get_var_list_dlist_unqvl.
Qed.

Lemma get_var_list_prop_unqvl :
    forall p, unqvl (get_var_list_prop_term p).
    induction p; simpl.
    - constructor.
    - apply var_list_merge_preserse_unqvl.
      apply get_var_list_prop_atom_unqvl.
      apply IHp.
Qed.

Lemma get_var_list_sep_atom_unqvl :
    forall s, unqvl (get_var_list_sep_atom s).
    destruct s.
    - apply var_list_merge_preserse_unqvl; apply get_var_list_expr_unqvl.
    - apply get_var_list_dlist_unqvl.
Qed.

Lemma get_var_list_sep_unqvl :
    forall s, unqvl (get_var_list_sep_term s).
    induction s; simpl.
    - constructor.
    - apply var_list_merge_preserse_unqvl.
      apply get_var_list_sep_atom_unqvl.
      assumption.
Qed.

Lemma get_var_list_ps_unqvl :
    forall ps, unqvl (get_var_list_ps_term ps).
    intros; destruct ps; simpl.
    apply var_list_merge_preserse_unqvl; [
        apply get_var_list_prop_unqvl |
        apply get_var_list_sep_unqvl
    ].
Qed.

Lemma var_list_merge_minus_permutation:
    forall l1 l2,
        unqvl l1 -> unqvl l2 ->
        Permutation (var_list_merge l1 l2) (l1 ++ (var_list_minus l2 l1)).
    intros; generalize dependent l1; induction l2; intros.
    - simpl.
      rewrite app_nil_r.
      reflexivity.
    - simpl.
      unfold var_list_insert.
      destruct (not_appear_free_var_list l1 a) eqn : ?.
      + destruct (not_appear_free_var_list l2 a) eqn : ?.
        * apply not_appear_free_var_list_not_in in Heqb0.
          rewrite IHl2.
          assert (forall a l1 l2, ~ In a l2 -> var_list_minus l2 (a :: l1) = var_list_minus l2 l1). {
            clear.
            intros; generalize dependent a; revert l1; induction l2; intros.
            - reflexivity.
            - simpl.
              destruct (not_appear_free_var_list l1 a) eqn : ?;
              destruct (negb (var_type_eqb a a0)) eqn : ?; simpl.
              + rewrite IHl2.
                reflexivity.
                simpl in H.
                tauto.
              + apply negb_false_iff in Heqb0.
                apply var_type_eqb_eq in Heqb0.
                simpl in H; subst; tauto.
              + apply IHl2.
                simpl in H; tauto.
              + apply negb_false_iff in Heqb0.
                apply var_type_eqb_eq in Heqb0.
                simpl in H; subst; tauto.
          }
          rewrite (H1 _ _ _ Heqb0).
          apply Permutation_middle.
          inversion H0; subst.
          assumption.
          apply not_appear_free_var_list_not_in in Heqb.
          constructor; assumption.
        * apply not_appear_free_var_list_in in Heqb0.
          apply not_appear_free_var_list_not_in in Heqb.
          inversion H0; subst.
          contradiction.
      + apply IHl2.
        inversion H0; subst.
        assumption.
        assumption.
Qed.

Lemma var_list_minus_not_in :
    forall x l1 l2,
        ~ In x (var_list_minus l1 l2) <-> ~ In x l1 \/ In x l2.
    split; intros.
    -   destruct (var_list_in_dec x l1); [ | left; assumption ].
        destruct (var_list_in_dec x l2); [ right; assumption | ].
        exfalso; apply H; apply var_list_minus_in; split; assumption.
    -   unfold not; intros H0; apply var_list_minus_in in H0; tauto.
Qed.

Definition rc_denote_post q' Q' q Q vl ty_env (env : environment ty_env) : expr :=
    var_list_all_denote
        (var_list_minus (get_var_list_ps_term (q ++ q', Q ++ Q')) vl)
        _ env (rc_denote_post_atom q' Q' q Q).

Lemma rc_denote_post_equiv :
    forall vl q' Q' q Q ty_env env x v,
        ~ In x vl ->
        rc_denote_post q' Q' q Q vl ty_env env --||-- rc_denote_post q' Q' q Q vl _ (term_mapping_update_env env (fst x) (snd x) v).
    intros; unfold rc_denote_post.
    destruct (not_appear_free_var_list (get_var_list_ps_term (q ++ q', Q ++ Q')) x) eqn : ?; [
        apply not_appear_free_var_list_not_in in Heqb |
        apply not_appear_free_var_list_in in Heqb
    ].
    -   apply var_list_all_denote_equiv; intros.
        apply rc_denote_post_atom_equiv.
        destruct (not_appear_free_ps_term (q ++ q', Q ++ Q') x) eqn : Heqb0.
        reflexivity.
        apply get_var_list_not_appear_free_false_ps in Heqb0; contradiction.
    -   pose proof (conj Heqb H).
        rewrite <- var_list_minus_in in H0.
        apply var_list_all_denote_in.
        assumption.
Qed.

Definition rc_denote_pre_atom fl p P p' P' cont ty_env (env : environment ty_env) : Prop :=
    ps_term_denote (p, P) _ env |--
        var_list_exists_denote fl ty_env env
        (fun ty_env env => ps_term_denote (p', P') _ env ** (cont ty_env env)).
        
(* Lemma rc_denote_pre_atom_equiv :
    forall p P p' P' x,
        not_appear_free_ps_term (p ++ p', P ++ P') x = true ->
    forall ty_env cont,
        (forall (env : environment ty_env) v,
            cont ty_env env --||-- cont ty_env (term_mapping_update_env env (fst x) (snd x) v)) ->
        forall (env : environment ty_env) v,
        rc_denote_pre_atom p P p' P' cont ty_env env <->
        rc_denote_pre_atom p P p' P' cont
        ty_env (term_mapping_update_env env (fst x) (snd x) v).
    intros.
    simpl in *.
    apply andb_true_iff in H as [? ?].
    rewrite not_appear_free_sep_term_app in H1; apply andb_true_iff in H1 as [? ?].
    rewrite not_appear_free_prop_term_app in H; apply andb_true_iff in H as [? ?].
    apply not_appear_free_sep_term_equiv with (ty_env := ty_env) (env := env) (v := v) in H1, H2.
    apply not_appear_free_prop_term_equiv with (ty_env := ty_env) (env := env) (v := v) in H, H3.
    unfold rc_denote_pre_atom.
    simpl.
    split ;  rewrite <- H, H2, <- H0, H3, H1 ; auto.
Qed. *)

Definition rc_denote_pre fl p P p' P' ty_env (env : environment ty_env) cont : Prop :=
    let vl := get_var_list_ps_term (p ++ p', P ++ P') in
        var_list_forall_denote (var_list_minus vl fl) _ env
            (rc_denote_pre_atom fl p P p' P' (cont (var_list_merge vl fl))).

(* Lemma rc_denote_pre_equiv :
    forall p P p' P' ty_env cont x,
    (forall (env : environment ty_env) vl v,
        ~ In x vl ->
        cont vl ty_env env --||-- cont vl ty_env (term_mapping_update_env env (fst x) (snd x) v)) ->
    forall (env : environment ty_env) v,
        rc_denote_pre p P p' P' ty_env env cont <->
        rc_denote_pre p P p' P' ty_env (term_mapping_update_env env (fst x) (snd x) v) cont.
    intros; unfold rc_denote_pre.
    remember (get_var_list_ps_term (p ++ p', P ++ P')) as vl.
    destruct (var_list_in_dec x vl).
    -   apply var_list_forall_denote_in.
        apply i.
    -   apply var_list_forall_denote_equiv.
        intros; apply rc_denote_pre_atom_equiv.
        destruct (not_appear_free_ps_term (p ++ p', P ++ P') x) eqn : ?.
        reflexivity.
        apply get_var_list_not_appear_free_false_ps in Heqb.
        subst vl; contradiction.
        intros; apply H.
        apply n.
Qed. *)

Definition rc_denote (r : RamificationCondition) ty_env (env : environment ty_env) : Prop :=
    match r with
    | RC fl sc p p' q' q P P' Q' Q =>
        rc_denote_pre fl (sc ++ p) P p' P' _ env (rc_denote_post q' Q' q Q)
    end.

(* Lemma rc_denote_equiv :
    forall r ty_env env x v,
        rc_denote r ty_env env <->
        rc_denote r ty_env (term_mapping_update_env env (fst x) (snd x) v).
    intros; destruct r; unfold rc_denote; simpl.
    apply rc_denote_pre_equiv.
    intros.
    apply rc_denote_post_equiv.
    apply H.
Qed. *)

Lemma var_list_forall_denote_permutation :
    forall l1 l2,
        Permutation l1 l2 ->
    forall ty_env env cont,
        var_list_forall_denote l1 ty_env env cont <->
        var_list_forall_denote l2 ty_env env cont.
    intros l1 l2 H; induction H; intros.
    - reflexivity.
    - simpl. destruct x; split; intros.
      + rewrite <- IHPermutation. apply H0.
      + rewrite IHPermutation. apply H0.
    - destruct (var_type_eqb x y) eqn : ?; [
        apply var_type_eqb_eq in Heqb |
        apply var_type_eqb_neq in Heqb
      ];
      split; intros; destruct x, y; simpl; intros.
      + injection Heqb as ?; subst.
        simpl in H.
        apply H.
      + injection Heqb as ?; subst.
        simpl in H.
        apply H.
      + simpl in *.
        destruct env; simpl in *.
        rewrite term_mapping_update_swap by apply Heqb.
        apply H.
      + simpl in *.
        destruct env; simpl in *.
        rewrite term_mapping_update_swap by lia.
        apply H.
    - rewrite IHPermutation1, IHPermutation2.
      reflexivity.
Qed.

Lemma var_list_insert_eq :
    forall a l,
        In a l -> var_list_insert a l = l.
    unfold var_list_insert; intros.
    destruct (not_appear_free_var_list l a) eqn : ?.
    apply not_appear_free_var_list_not_in in Heqb; contradiction.
    reflexivity.
Qed.

Lemma var_list_insert_neq :
    forall a l,
        ~ In a l -> var_list_insert a l = a :: l.
    unfold var_list_insert; intros.
    destruct (not_appear_free_var_list l a) eqn : ?.
    reflexivity.
    apply not_appear_free_var_list_in in Heqb; contradiction.
Qed.

Lemma var_list_merge_cons_l :
    forall l1 l2 x,
        unqvl (x :: l1) ->
        unqvl l2 ->
        ~ In x l2 ->
        Permutation (var_list_merge (x :: l1) l2) (x :: var_list_merge l1 l2).
    intros l1 l2; revert l1; induction l2; intros.
    - reflexivity.
    - simpl.
      inversion H0; subst; clear H0.
      unfold var_list_insert.
      destruct (not_appear_free_var_list (x :: l1) a) eqn : ?;
      destruct (not_appear_free_var_list l1 a) eqn : ?.
      + apply not_appear_free_var_list_not_in in Heqb.
        apply not_appear_free_var_list_not_in in Heqb0.
        rewrite ! IHl2; try assumption.
        apply perm_swap.
        constructor; auto.
        inversion H; subst; assumption.
        simpl in H1; tauto.
        constructor; auto.
      + apply not_appear_free_var_list_not_in in Heqb.
        apply not_appear_free_var_list_in in Heqb0.
        simpl in Heqb; tauto.
      + apply not_appear_free_var_list_in in Heqb.
        apply not_appear_free_var_list_not_in in Heqb0.
        simpl in *.
        assert (x = a) by tauto; subst.
        tauto.
      + apply not_appear_free_var_list_in in Heqb.
        apply not_appear_free_var_list_in in Heqb0.
        apply IHl2; try assumption.
        simpl in H1; tauto.
Qed.

Lemma var_list_merge_cons_le :
    forall l1 l2 x,
        unqvl (x :: l1) ->
        unqvl l2 ->
        In x l2 ->
        Permutation (var_list_merge (x :: l1) l2) (var_list_merge l1 l2).
    intros l1 l2; revert l1; induction l2; intros.
    - simpl in *; contradiction.
    - simpl in *.
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      unfold var_list_insert.
      destruct (not_appear_free_var_list (x :: l1) a) eqn : ?;
      destruct (not_appear_free_var_list l1 a) eqn : ?.
      + apply not_appear_free_var_list_not_in in Heqb.
        apply not_appear_free_var_list_not_in in Heqb0.
        rewrite var_list_merge_cons_l; try auto; try (repeat (constructor; auto)).
        rewrite var_list_merge_cons_l with (x := a); try auto; try (repeat (constructor; auto)).
        apply IHl2; try auto; try (repeat (constructor; auto)).
        simpl in Heqb; destruct H1; [ subst; tauto | assumption ].
      + apply not_appear_free_var_list_not_in in Heqb.
        apply not_appear_free_var_list_in in Heqb0.
        simpl in Heqb; tauto.
      + apply not_appear_free_var_list_in in Heqb.
        apply not_appear_free_var_list_not_in in Heqb0.
        simpl in *.
        assert (x = a) by tauto; subst.
        reflexivity.
      + apply not_appear_free_var_list_in in Heqb.
        apply not_appear_free_var_list_in in Heqb0.
        apply IHl2; try auto; try (repeat (constructor; auto)).
        destruct H1; try assumption.
        subst; contradiction.
Qed.

Lemma var_list_merge_nil_r :
    forall l,
        unqvl l ->
        Permutation (var_list_merge nil l) l.
    induction l.
    - reflexivity.
    - intros; simpl in *.
      unfold var_list_insert; simpl.
      inversion H; subst.
      rewrite var_list_merge_cons_l; try auto; try solve [repeat (constructor; auto)].
Qed.

Lemma var_list_merge_left_perm :
    forall l1 l2 l3,
        unqvl l1 ->
        unqvl l2 ->
        unqvl l3 ->
        Permutation l1 l2 ->
        Permutation (var_list_merge l1 l3) (var_list_merge l2 l3).
    intros.
    induction H2.
    - reflexivity.
    - destruct (var_list_in_dec x l3).
      + rewrite ! var_list_merge_cons_le; try auto; try solve [repeat (constructor; auto)].
        apply IHPermutation; try solve [repeat (constructor; auto)].
        all: inversion H; inversion H0; subst; assumption.
      + rewrite ! var_list_merge_cons_l; try auto; try solve [repeat (constructor; auto)].
        rewrite IHPermutation.
        reflexivity.
        all: inversion H; inversion H0; subst; assumption.
    - inversion H; inversion H0; subst.
      inversion H5; inversion H9; subst.
      simpl in H4, H8.
      destruct (var_list_in_dec x l3);
      destruct (var_list_in_dec y l3).
      + rewrite ! var_list_merge_cons_le; try auto; try solve [repeat (constructor; auto)].
      + rewrite ! var_list_merge_cons_le with (x := x); try auto; try solve [repeat (constructor; auto)].
        rewrite ! var_list_merge_cons_l with (x := y); try auto; try solve [repeat (constructor; auto)].
        rewrite ! var_list_merge_cons_le with (x := x); try auto; try solve [repeat (constructor; auto)].
      + rewrite ! var_list_merge_cons_l with (x := x); try auto; try solve [repeat (constructor; auto)].
        rewrite ! var_list_merge_cons_le with (x := y); try auto; try solve [repeat (constructor; auto)].
        rewrite ! var_list_merge_cons_l with (x := x); try auto; try solve [repeat (constructor; auto)].
      + rewrite ! var_list_merge_cons_l; try auto; try solve [repeat (constructor; auto)].
    - rewrite IHPermutation1, IHPermutation2.
      reflexivity.
      all: try assumption.
      all: apply perm_unqvl with (l1 := l); assumption.
Qed.

Lemma var_list_merge_comm :
    forall l1 l2,
        unqvl l1 ->
        unqvl l2 ->
        Permutation (var_list_merge l1 l2) (var_list_merge l2 l1).
    induction l1; intros.
    - simpl.
      rewrite var_list_merge_nil_r.
      reflexivity.
      auto.
    - destruct (var_list_in_dec a l2).
      + rewrite var_list_merge_cons_le; try auto; try solve [repeat (constructor; auto)].
        simpl; rewrite var_list_insert_eq; try assumption.
        apply IHl1; try auto; try solve [repeat (constructor; auto)].
        inversion H; auto.
      + rewrite var_list_merge_cons_l; try auto; try solve [repeat (constructor; auto)]. 
        simpl; rewrite var_list_insert_neq; try assumption.
        rewrite var_list_merge_cons_l; try auto; try solve [repeat (constructor; auto)].
        rewrite IHl1.
        reflexivity.
        all: inversion H; subst; auto.
Qed.

Lemma var_list_merge_right_perm :
    forall l1 l2 l3,
        unqvl l1 ->
        unqvl l2 ->
        unqvl l3 ->
        Permutation l2 l3 ->
        Permutation (var_list_merge l1 l2) (var_list_merge l1 l3).
    intros.
    rewrite var_list_merge_comm; try assumption.
    rewrite var_list_merge_comm with (l1 := l1); try assumption.
    apply var_list_merge_left_perm; assumption.
Qed.

Lemma var_list_merge_assoc :
    forall l1 l2 l3,
        unqvl l1 ->
        unqvl l2 ->
        unqvl l3 ->
        Permutation (var_list_merge l1 (var_list_merge l2 l3))
                    (var_list_merge (var_list_merge l1 l2) l3).
    intros l1 l2 l3; revert l1 l2; induction l3; intros.
    - simpl; reflexivity.
    - inversion H1; subst.
      simpl.
      destruct (var_list_in_dec a l2);
      destruct (var_list_in_dec a l1).
      + rewrite var_list_insert_eq by assumption.
        rewrite var_list_insert_eq.
        2: apply var_list_merge_in_left; assumption.
        apply IHl3; assumption.
      + rewrite var_list_insert_eq by assumption.
        rewrite var_list_insert_eq.
        2: apply var_list_merge_in_right; assumption.
        apply IHl3; assumption.
      + rewrite var_list_insert_neq by assumption.
        rewrite var_list_merge_right_perm with (l3 := (a :: (var_list_merge l2 l3))).
        5: apply var_list_merge_cons_l.
        all: try auto; try (constructor; auto).
        all: try apply var_list_merge_preserse_unqvl; try auto; try (constructor; auto).
        simpl.
        rewrite var_list_insert_eq by assumption.
        rewrite var_list_insert_eq.
        apply IHl3.
        all: try assumption.
        apply var_list_merge_in_left; assumption.
        unfold not; intros.
        apply var_list_merge_in in H2.
        tauto.
      + rewrite var_list_insert_neq by assumption.
        rewrite var_list_merge_right_perm with (l3 := (a :: (var_list_merge l2 l3))).
        5: apply var_list_merge_cons_l.
        all: try auto; try (constructor; auto).
        all: try apply var_list_merge_preserse_unqvl; try auto; try (constructor; auto).
        simpl; rewrite var_list_insert_neq by assumption.
        rewrite var_list_merge_cons_l.
        rewrite var_list_insert_neq.
        rewrite var_list_merge_cons_l.
        apply perm_skip.
        apply IHl3.
        all: try auto; try (repeat (constructor; auto));
             try (apply var_list_merge_preserse_unqvl; auto).
        all: unfold not; intros H10; apply var_list_merge_in in H10; tauto.
Qed.

Definition ProvableRC (r : RamificationCondition) ty_env env : Prop := rc_denote r ty_env env.

Definition sc_denote (sc : PropTerm) (context : PSTerm) ty_env (env : environment ty_env) : Prop :=
    var_list_forall_denote 
        (var_list_merge (get_var_list_prop_term sc) (get_var_list_ps_term context))
        _ env (fun ty_env env => ps_term_denote context _ env |-- prop_term_denote sc _ env).

Lemma sc_denote_equiv :
    forall sc context ty_env env x v,
        sc_denote sc context ty_env env <->
        sc_denote sc context ty_env (term_mapping_update_env env (fst x) (snd x) v).
    intros; unfold sc_denote.
    remember (get_var_list_prop_term sc) as l1.
    remember (get_var_list_ps_term context) as l2.
    destruct (var_list_in_dec x (var_list_merge l1 l2)).
    +   apply var_list_forall_denote_in.
        apply i.
    +   apply var_list_forall_denote_equiv; intros.
        apply var_list_merge_not_in in n as [? ?].
        pose proof not_appear_free_ps_term_equiv context x.
        split ; rewrite <- H1 ; try (rewrite <- not_appear_free_prop_term_equiv) ; auto ; try (
        destruct (not_appear_free_prop_term sc x) eqn : ?; try reflexivity;
        apply get_var_list_not_appear_free_false_prop in Heqb;
        subst; contradiction) ; try (
        destruct (not_appear_free_ps_term context x) eqn : ?; try reflexivity;
        apply get_var_list_not_appear_free_false_ps in Heqb; subst; contradiction).
Qed.

Definition ProvableSC (sc : PropTerm) (context : PSTerm) ty_env env : Prop :=
    sc_denote sc context ty_env env.

Fixpoint sep_atom_term_inb (t : SepAtomTerm) (l : SepTerm) : bool :=
    match l with
    | nil => false
    | cons x xs => (sep_atom_term_eqb t x || sep_atom_term_inb t xs)%bool
    end.

Fixpoint prop_atom_term_inb (t : PropAtomTerm) (l : PropTerm) : bool :=
    match l with
    | nil => false
    | cons x xs => (prop_atom_term_eqb t x || prop_atom_term_inb t xs)%bool
    end.

Lemma sep_atom_term_inb_in :
    forall t l,
    sep_atom_term_inb t l = true <-> In t l.
    intros; split; generalize dependent t.
    - induction l; intros.
      + simpl in H; discriminate.
      + simpl in H.
        apply orb_true_iff in H.
        destruct H.
        * apply sep_atom_term_eqb_true in H; subst; left; reflexivity.
        * right; apply IHl; assumption.
    - induction l; intros.
      + destruct H.
      + simpl.
        destruct H; apply orb_true_iff.
        * left; subst; apply sep_atom_term_eqb_refl.
        * right; apply IHl; assumption.
Qed.

Lemma prop_atom_term_inb_in :
    forall t l,
    prop_atom_term_inb t l = true <-> In t l.
    intros; split; generalize dependent t.
    - induction l; intros.
      + simpl in H; discriminate.
      + simpl in H.
        apply orb_true_iff in H.
        destruct H.
        * apply prop_atom_term_eqb_true in H; subst; left; reflexivity.
        * right; apply IHl; assumption.
    - induction l; intros.
      + destruct H.
      + simpl.
        destruct H; apply orb_true_iff.
        * left; subst; apply prop_atom_term_eqb_refl.
        * right; apply IHl; assumption.
Qed.

Lemma sep_atom_term_inb_in_false :
    forall t l,
        sep_atom_term_inb t l = false -> ~ In t l.
    intros; unfold not; intro H1.
    pose proof sep_atom_term_inb_in; edestruct H0.
    apply H3 in H1.
    rewrite H1 in H; discriminate.
Qed.

Lemma prop_atom_term_inb_in_false :
    forall t l,
        prop_atom_term_inb t l = false -> ~ In t l.
    intros; unfold not; intro H1.
    pose proof prop_atom_term_inb_in; edestruct H0.
    apply H3 in H1.
    rewrite H1 in H; discriminate.
Qed.

Fixpoint sep_atom_term_remove (t : SepAtomTerm) (l : SepTerm) : SepTerm :=
    match l with
    | nil => nil
    | cons x xs => if (sep_atom_term_eqb x t) then xs else cons x (sep_atom_term_remove t xs)
    end.

Fixpoint prop_atom_term_remove (t : PropAtomTerm) (l : PropTerm) : PropTerm :=
    match l with
    | nil => nil
    | cons x xs => if (prop_atom_term_eqb x t) then xs else cons x (prop_atom_term_remove t xs)
    end.

Lemma sep_atom_term_remove_eq :
    forall a l, sep_atom_term_remove a (a :: l) = l.
    intros; simpl.
    pose proof (sep_atom_term_eqb_refl).
    rewrite H.
    reflexivity.
Qed.

Lemma prop_atom_term_remove_eq :
    forall a l, prop_atom_term_remove a (a :: l) = l.
    intros; simpl.
    pose proof (prop_atom_term_eqb_refl).
    rewrite H.
    reflexivity.
Qed.

Lemma sep_atom_term_remove_neq :
    forall a b l, a <> b -> sep_atom_term_remove a (b :: l) = b :: sep_atom_term_remove a l.
    intros; simpl.
    destruct (sep_atom_term_eqb b a) eqn : ?.
    - apply sep_atom_term_eqb_true in Heqb0.
      symmetry in Heqb0; contradiction.
    - reflexivity.
Qed.

Lemma prop_atom_term_remove_neq :
    forall a b l, a <> b -> prop_atom_term_remove a (b :: l) = b :: prop_atom_term_remove a l.
    intros; simpl.
    destruct (prop_atom_term_eqb b a) eqn : ?.
    - apply prop_atom_term_eqb_true in Heqb0.
      symmetry in Heqb0; contradiction.
    - reflexivity.
Qed.

Lemma sep_atom_term_remove_split :
    forall a l1 l2,
        In a l1 ->
        sep_atom_term_remove a l1 = l2 ->
        exists l2a l2b, l2 = l2a ++ l2b /\ l1 = l2a ++ a :: l2b.
    induction l1.
    - intros.
      simpl in *; exfalso; apply H.
    - intros.
      simpl in H.
      destruct (sep_atom_term_eq_dec a a0).
      * subst a0; rewrite sep_atom_term_remove_eq in H0.
        exists nil, l1; rewrite H0; simpl; split; reflexivity.
      * destruct H; [ symmetry in H; contradiction | ].
        rewrite sep_atom_term_remove_neq in H0 by assumption.
        destruct l2; [ discriminate H0 | ].
        injection H0 as ?; subst s.
        specialize (IHl1 _ H H1).
        destruct IHl1 as [l2a [l2b ?]].
        exists (a0 :: l2a), l2b.
        destruct H0; subst.
        simpl; split; reflexivity.
Qed.

Lemma prop_atom_term_remove_split :
    forall a l1 l2,
        In a l1 ->
        prop_atom_term_remove a l1 = l2 ->
        exists l2a l2b, l2 = l2a ++ l2b /\ l1 = l2a ++ a :: l2b.
    induction l1.
    - intros.
      simpl in *; exfalso; apply H.
    - intros.
      simpl in H.
      destruct (prop_atom_term_eq_dec a a0).
      * subst a0; rewrite prop_atom_term_remove_eq in H0.
        exists nil, l1; rewrite H0; simpl; split; reflexivity.
      * destruct H; [ symmetry in H; contradiction | ].
        rewrite prop_atom_term_remove_neq in H0 by assumption.
        destruct l2; [ discriminate H0 | ].
        injection H0 as ?; subst p.
        specialize (IHl1 _ H H1).
        destruct IHl1 as [l2a [l2b ?]].
        exists (a0 :: l2a), l2b.
        destruct H0; subst.
        simpl; split; reflexivity.
Qed.

Lemma permutation_equiv_sep :
    forall t1 t2 ty_env (env : environment ty_env),
        Permutation t1 t2 ->
        sep_term_denote t1 _ env --||-- sep_term_denote t2 _ env.
    intros; generalize dependent env.
    induction H; intros.
    - apply logic_equiv_refl.
    - simpl; split; destruct (IHPermutation env).
      + sep_apply H0; apply derivable1_refl.
      + sep_apply H1; apply derivable1_refl.
    - simpl; split; entailer!.
    - apply (logic_equiv_trans _ _ _ (IHPermutation1 env) (IHPermutation2 env)).
Qed.

Lemma permutation_equiv_prop :
    forall t1 t2 ty_env (env : environment ty_env),
        Permutation t1 t2 ->
        prop_term_denote t1 _ env --||-- prop_term_denote t2 _ env.
    intros; generalize dependent env.
    induction H; intros.
    - apply logic_equiv_refl.
    - simpl; split; destruct (IHPermutation env).
      all: unfold derivable1, coq_prop, CRules.andp in *; intros;
        specialize (H0 m); specialize (H1 m); tauto.
    - simpl; split.
      all: unfold derivable1, coq_prop, CRules.andp in *; tauto.
    - specialize (IHPermutation1 env); specialize (IHPermutation2 env).
      unfold logic_equiv, derivable1 in *; split; intros;
      destruct IHPermutation1; destruct IHPermutation2.
      all: specialize (H2 m);
      specialize (H3 m);
      specialize (H4 m);
      specialize (H5 m);
      tauto.
Qed.

Lemma erase_sep_permutation :
    forall P H Q,
        erase_sep P H = Some Q ->
        Permutation P (cons H Q).
    induction P; intros.
    - simpl in H0; discriminate.
    - simpl in *.
      destruct (sep_atom_term_eqb a H) eqn : ?.
      + apply sep_atom_term_eqb_true in Heqb; subst a.
        injection H0 as ?; subst; apply Permutation_refl.
      + destruct (erase_sep P H) eqn : ?; [ | discriminate H0 ].
        apply IHP in Heqo.
        injection H0 as ?; subst.
        rewrite perm_swap.
        apply Permutation_cons; [ apply eq_refl | apply Heqo ].
Qed.

Lemma erase_prop_permutation :
    forall P H Q,
        erase_prop P H = Some Q ->
        Permutation P (cons H Q).
    induction P; intros.
    - simpl in H0; discriminate.
    - simpl in *.
      destruct (prop_atom_term_eqb a H) eqn : ?.
      + apply prop_atom_term_eqb_true in Heqb; subst a.
        injection H0 as ?; subst; apply Permutation_refl.
      + destruct (erase_prop P H) eqn : ?; [ | discriminate H0 ].
        apply IHP in Heqo.
        injection H0 as ?; subst.
        rewrite perm_swap.
        apply Permutation_cons; [ apply eq_refl | apply Heqo ].
Qed.

Lemma in_erase_sep :
    forall P H,
        In H P ->
        exists Q, erase_sep P H = Some Q.
    induction P; intros.
    - simpl in *; exfalso; apply H0.
    - simpl in *; destruct (sep_atom_term_eqb a H) eqn : ?.
      + apply sep_atom_term_eqb_true in Heqb; subst a.
        exists P; reflexivity.
      + apply sep_atom_term_eqb_false in Heqb.
        destruct H0; [ contradiction | ].
        destruct (IHP _ H0) as [Q ?].
        rewrite H1.
        exists (a :: Q); reflexivity.
Qed.

Lemma in_erase_prop :
    forall P H,
        In H P ->
        exists Q, erase_prop P H = Some Q.
    induction P; intros.
    - simpl in *; exfalso; apply H0.
    - simpl in *; destruct (prop_atom_term_eqb a H) eqn : ?.
      + apply prop_atom_term_eqb_true in Heqb; subst a.
        exists P; reflexivity.
      + apply prop_atom_term_eqb_false in Heqb.
        destruct H0; [ contradiction | ].
        destruct (IHP _ H0) as [Q ?].
        rewrite H1.
        exists (a :: Q); reflexivity.
Qed.

Definition update_rc (op : Operation) (r : RamificationCondition) : RamificationCondition :=
    match r with
    | RC fl sc p p' q' q P P' Q' Q =>
        match op with
        | OAssume H => RC fl (cons H sc) p p' q' q P P' Q' Q
        | OLeftPropErase H => if prop_atom_term_inb H p'
                              then RC fl sc p (prop_atom_term_remove H p') q' q P P' Q' Q
                              else RC fl sc (cons H p) p' q' q P P' Q' Q
        | OLeftPropAdd H => RC fl sc p (cons H p') q' q P P' Q' Q
        | ORightPropAdd H => RC fl sc p p' (cons H q') q P P' Q' Q
        | ORightPropErase H => if prop_atom_term_inb H q'
                               then RC fl sc p p' (prop_atom_term_remove H q') q P P' Q' Q
                               else RC fl sc p p' q' (cons H q) P P' Q' Q
        | OLeftSepErase H => if sep_atom_term_inb H P'
                          then RC fl sc p p' q' q P (sep_atom_term_remove H P') Q' Q
                          else RC fl sc p p' q' q (cons H P) P' Q' Q
        | OLeftSepAdd H => RC fl sc p p' q' q P (cons H P') Q' Q
        | ORightSepAdd H => RC fl sc p p' q' q P P' (cons H Q') Q
        | ORightSepErase H => if sep_atom_term_inb H Q'
                           then RC fl sc p p' q' q P P' (sep_atom_term_remove H Q') Q
                           else RC fl sc p p' q' q P P' Q' (cons H Q)
        | OForallAdd x => RC (cons x fl) sc p p' q' q P P' Q' Q
        | _ => r
        end
    end.

Definition gen_rc (ops : list Operation) : RamificationCondition :=
    fold_right update_rc (RC nil nil nil nil nil nil nil nil nil nil) ops.

Lemma gen_rc_cons :
    forall op ops,
    gen_rc (op :: ops) = update_rc op (gen_rc ops).
    intros; simpl; reflexivity.
Qed.

Definition get_prop_exists (t : ExistsTerm) : PropTerm :=
    match t with
    | TExists vl t => fst t
    end.

Definition get_sep_exists (t : ExistsTerm) : SepTerm :=
    match t with
    | TExists vl t => snd t
    end.

Definition get_pre_prop_forall (t : ForallTerm) : PropTerm :=
    match t with
    | TForall vl pre post => fst pre
    end.

Definition get_pre_sep_forall (t : ForallTerm) : SepTerm :=
    match t with
    | TForall vl pre post => snd pre
    end.

Definition get_pre_forall (t : ForallTerm) : PSTerm :=
    match t with
    | TForall vl pre post => pre
    end.

Definition get_post_prop_forall (t : ForallTerm) : PropTerm :=
    match t with
    | TForall vl pre post => get_prop_exists post
    end.

Definition get_post_sep_forall (t : ForallTerm) : SepTerm :=
    match t with
    | TForall vl pre post => get_sep_exists post
    end.

(* Lemma soundness_helper0 : forall ops sc a b c d A B C D T1 T2,
    apply_operations T1 ops = Some T2 ->
    gen_rc ops = RC sc a b c d A B C D ->
    exists cp cq CP CQ,
    Permutation (get_pre_sep_forall T1) (A ++ CP) /\
    Permutation (get_pre_sep_forall T2) (B ++ CP) /\
    Permutation (get_post_sep_forall T2) (C ++ CQ) /\
    Permutation (get_post_sep_forall T1) (D ++ CQ) /\
    Permutation (get_pre_prop_forall T1) (a ++ cp) /\
    Permutation (get_pre_prop_forall T2) (b ++ cp) /\
    Permutation (get_post_prop_forall T2) (c ++ cq) /\
    Permutation (get_post_prop_forall T1) (d ++ cq).
    induction ops.
    - intros.
      simpl in H; injection H as ?.
      simpl in H0; injection H0 as ?; subst.
      destruct T2 as [a [p P] [b [q Q]]].
      exists p, q, P, Q.
      simpl; repeat split; apply Permutation_refl.
    - intros.
      rewrite gen_rc_cons in H0;
      rewrite apply_operations_cons in H;
      remember (apply_operations T1 ops) as T1';
      remember (gen_rc ops) as r';
      destruct T1' as [ T1' | ], r'; [ | simpl in H; discriminate ].
      destruct a; simpl in *.
      + eapply IHops.
        * injection H as ?; subst.
          apply (eq_sym HeqT1').
        * destruct sc; inversion H0.
          subst.
          reflexivity.
      + destruct B; injection H0 as ?; [ discriminate | ]; subst.
        specialize (IHops _ _ _ _ _ _ _ _ _ _ _ (eq_sym HeqT1') eq_refl).
        destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
        destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]]; simpl in *.
        injection H as ?; subst; simpl in *.
        exists cp, cq, CP, CQ.
        repeat split; try assumption.
        unfold add_sep.
        apply Permutation_cons; [ apply eq_refl | assumption ].
      + destruct (sep_atom_term_inb H1 P') eqn : Heqb; [
          rewrite sep_atom_term_inb_in in Heqb |
          apply sep_atom_term_inb_in_false in Heqb
        ].
        * symmetry in HeqT1'.
          injection H0 as ?.
          pose proof (sep_atom_term_remove_split _ _ _ Heqb H7).
          destruct H10 as [B_ls [B_rs ?]]; destruct H10.
          subst P Q' Q P' B.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_sep P1 H1) eqn : ? ; [ | discriminate H ].
          injection H as ?; subst; rewrite H10.
          exists cp, cq, CP, CQ.
          repeat split; try assumption.
          apply erase_sep_permutation in Heqo.
          rewrite Heqo in H7.
          rewrite (Permutation_app_comm B_ls _) in H7.
          simpl in H7.
          apply Permutation_cons_inv in H7.
          rewrite (Permutation_app_comm B_rs _) in H7.
          apply H7.
        * destruct A; injection H0 as ?; [ discriminate | ]; subst.
          symmetry in HeqT1'.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_sep P1 s) eqn : ?; [ | discriminate H ].
          injection H as ?; subst.
          apply erase_sep_permutation in Heqo.
          assert (In s CP). {
            assert (In s (s :: P2)) by (simpl; left; reflexivity).
            rewrite <- Heqo in H.
            rewrite -> H1 in H.
            apply in_app_iff in H.
            destruct H; [ contradiction | assumption ].
          }
          destruct (in_erase_sep _ _ H) as [CP' ?].
          apply erase_sep_permutation in H8.
          exists cp, cq, CP', CQ; repeat split; try assumption.
          -- rewrite H8 in H0.
             rewrite <- Permutation_middle in H0.
             apply H0.
          -- rewrite H8 in H1.
             rewrite Heqo in H1.
             rewrite <- Permutation_middle in H1.
             apply Permutation_cons_inv in H1.
             apply H1.
      + destruct C; injection H0 as ?; [ discriminate | ]; subst.
        specialize (IHops _ _ _ _ _ _ _ _ _ _ _ (eq_sym HeqT1') eq_refl).
        destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
        destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]]; simpl in *.
        injection H as ?; subst; simpl in *.
        exists cp, cq, CP, CQ.
        repeat split; try assumption.
        unfold add_sep.
        apply Permutation_cons; [ apply eq_refl | assumption ].
      + destruct (sep_atom_term_inb H1 Q') eqn : Heqb; [
          rewrite sep_atom_term_inb_in in Heqb |
          apply sep_atom_term_inb_in_false in Heqb
        ].
        * symmetry in HeqT1'.
          injection H0 as ?.
          pose proof (sep_atom_term_remove_split _ _ _ Heqb H8).
          destruct H10 as [C_ls [C_rs ?]]; destruct H10.
          subst P Q' Q P' C.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_sep Q1 H1) eqn : ? ; [ | discriminate H ].
          injection H as ?; subst; rewrite H10.
          exists cp, cq, CP, CQ.
          repeat split; try assumption.
          apply erase_sep_permutation in Heqo.
          rewrite Heqo in H8.
          rewrite (Permutation_app_comm C_ls _) in H8.
          simpl in H8.
          apply Permutation_cons_inv in H8.
          rewrite (Permutation_app_comm C_rs _) in H8.
          apply H8.
        * destruct D; injection H0 as ?; [ discriminate | ]; subst.
          symmetry in HeqT1'.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_sep Q1 s) eqn : ?; [ | discriminate H ].
          injection H as ?; subst.
          apply erase_sep_permutation in Heqo.
          assert (In s CQ). {
            assert (In s (s :: Q2)) by (simpl; left; reflexivity).
            rewrite <- Heqo in H.
            rewrite -> H2 in H.
            apply in_app_iff in H.
            destruct H; [ contradiction | assumption ].
          }
          destruct (in_erase_sep _ _ H) as [CQ' ?].
          apply erase_sep_permutation in H8.
          exists cp, cq, CP, CQ'; repeat split; try assumption.
          -- rewrite H8 in H2.
             rewrite Heqo in H2.
             rewrite <- Permutation_middle in H2.
             apply Permutation_cons_inv in H2.
             apply H2.
          -- rewrite H8 in H3.
             rewrite <- Permutation_middle in H3.
             apply H3.
      + destruct b; injection H0 as ?; [ discriminate | ]; subst.
        specialize (IHops _ _ _ _ _ _ _ _ _ _ _ (eq_sym HeqT1') eq_refl).
        destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
        destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]]; simpl in *.
        injection H as ?; subst; simpl in *.
        exists cp, cq, CP, CQ.
        repeat split; try assumption.
        unfold add_prop.
        apply Permutation_cons; [ apply eq_refl | assumption ].
      + destruct (prop_atom_term_inb H1 p') eqn : Heqb; [
          rewrite prop_atom_term_inb_in in Heqb |
          apply prop_atom_term_inb_in_false in Heqb
        ].
        * symmetry in HeqT1'.
          injection H0 as ?.
          pose proof (prop_atom_term_remove_split _ _ _ Heqb H3).
          destruct H10 as [b_ls [b_rs ?]]; destruct H10.
          subst p q' q p' b.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_prop p1 H1) eqn : ? ; [ | discriminate H ].
          injection H as ?; subst; rewrite H10.
          exists cp, cq, CP, CQ.
          repeat split; try assumption.
          apply erase_prop_permutation in Heqo.
          rewrite Heqo in H12.
          rewrite (Permutation_app_comm b_ls _) in H12.
          simpl in H12.
          apply Permutation_cons_inv in H12.
          rewrite (Permutation_app_comm b_rs _) in H12.
          apply H12.
        * destruct a0; injection H0 as ?; [ discriminate | ]; subst.
          symmetry in HeqT1'.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_prop p1 p0) eqn : ?; [ | discriminate H ].
          injection H as ?; subst.
          apply erase_prop_permutation in Heqo.
          assert (In p0 cp). {
            assert (In p0 (p0 :: p2)) by (simpl; left; reflexivity).
            rewrite <- Heqo in H.
            rewrite -> H5 in H.
            apply in_app_iff in H.
            destruct H; [ contradiction | assumption ].
          }
          destruct (in_erase_prop _ _ H) as [cp' ?].
          apply erase_prop_permutation in H8.
          exists cp', cq, CP, CQ; repeat split; try assumption.
          -- rewrite H8 in H4.
             rewrite <- Permutation_middle in H4.
             apply H4.
          -- rewrite H8 in H5.
             rewrite Heqo in H5.
             rewrite <- Permutation_middle in H5.
             apply Permutation_cons_inv in H5.
             apply H5.
      + destruct c; injection H0 as ?; [ discriminate | ]; subst.
        specialize (IHops _ _ _ _ _ _ _ _ _ _ _ (eq_sym HeqT1') eq_refl).
        destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
        destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]]; simpl in *.
        injection H as ?; subst; simpl in *.
        exists cp, cq, CP, CQ.
        repeat split; try assumption.
        unfold add_prop.
        apply Permutation_cons; [ apply eq_refl | assumption ].
      + destruct (prop_atom_term_inb H1 q') eqn : Heqb; [
          rewrite prop_atom_term_inb_in in Heqb |
          apply prop_atom_term_inb_in_false in Heqb
        ].
        * symmetry in HeqT1'.
          injection H0 as ?.
          pose proof (prop_atom_term_remove_split _ _ _ Heqb H4).
          destruct H10 as [c_ls [c_rs ?]]; destruct H10.
          subst p q' q p' c.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_prop q1 H1) eqn : ? ; [ | discriminate H ].
          injection H as ?; subst; rewrite H10.
          exists cp, cq, CP, CQ.
          repeat split; try assumption.
          apply erase_prop_permutation in Heqo.
          rewrite Heqo in H13.
          rewrite (Permutation_app_comm c_ls _) in H13.
          simpl in H13.
          apply Permutation_cons_inv in H13.
          rewrite (Permutation_app_comm c_rs _) in H13.
          apply H13.
        * destruct d; injection H0 as ?; [ discriminate | ]; subst.
          symmetry in HeqT1'.
          specialize (IHops _ _ _ _ _ _ _ _ _ _ _ HeqT1' eq_refl).
          destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
          destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
          destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
          simpl in *.
          destruct (erase_prop q1 p0) eqn : ?; [ | discriminate H ].
          injection H as ?; subst.
          apply erase_prop_permutation in Heqo.
          assert (In p0 cq). {
            assert (In p0 (p0 :: q2)) by (simpl; left; reflexivity).
            rewrite <- Heqo in H.
            rewrite -> H6 in H.
            apply in_app_iff in H.
            destruct H; [ contradiction | assumption ].
          }
          destruct (in_erase_prop _ _ H) as [cq' ?].
          apply erase_prop_permutation in H8.
          exists cp, cq', CP, CQ; repeat split; try assumption.
          -- rewrite H8 in H6.
             rewrite Heqo in H6.
             rewrite <- Permutation_middle in H6.
             apply Permutation_cons_inv in H6.
             apply H6.
          -- rewrite H8 in H7.
             rewrite <- Permutation_middle in H7.
             apply H7.
      + specialize (IHops _ _ _ _ _ _ _ _ _ _ _ (eq_sym HeqT1') eq_refl).
        destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
        destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
        destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
        destruct v; simpl in *.
        injection H as ?; injection H0 as ?; subst.
        exists cp, cq, CP, CQ.
        repeat split; try assumption.
      + specialize (IHops _ _ _ _ _ _ _ _ _ _ _ (eq_sym HeqT1') eq_refl).
        destruct IHops as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
        destruct T1' as [a1 [p1 P1] [b1 [q1 Q1]]];
        destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
        destruct v; simpl in *.
        injection H as ?; injection H0 as ?; subst.
        exists cp, cq, CP, CQ.
        repeat split; try assumption.
Qed. *)

Lemma sep_term_denote_app : forall a b ty_env (env : environment ty_env),
    sep_term_denote (a ++ b) _ env --||-- sep_term_denote a _ env ** sep_term_denote b _ env.
    induction a; intros; simpl.
    - split; entailer!.
    - destruct (IHa b _ env).
      split; entailer!.
Qed.

Lemma prop_term_denote_app : forall a b ty_env (env : environment ty_env),
    prop_term_denote (a ++ b) _ env --||-- prop_term_denote a _ env && prop_term_denote b _ env.
    induction a; intros; simpl.
    - split; unfold CRules.andp, logic_equiv, derivable1, CRules.truep; intros; tauto.
    - destruct (IHa b _ env).
      split; unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.coq_prop in *; intros.
      all: specialize (H m); specialize (H0 m); tauto.
Qed.

(* Lemma soundness_helper1 : forall ops sc a b c d A B C D T1 T2,
    apply_operations T1 ops = Some T2 ->
    gen_rc ops = RC sc a b c d A B C D ->
    exists cp cq CP CQ,
    (forall ty_env (env : environment ty_env),
        prop_term_denote (get_pre_prop_forall T1) _ env && sep_term_denote (get_pre_sep_forall T1) _ env --||--
        prop_term_denote (a ++ cp) _ env && sep_term_denote (A ++ CP) _ env) /\
    (forall ty_env (env : environment ty_env),
        prop_term_denote (get_pre_prop_forall T2) _ env && sep_term_denote (get_pre_sep_forall T2) _ env --||--
        prop_term_denote (b ++ cp) _ env && sep_term_denote (B ++ CP) _ env) /\
    (forall ty_env (env : environment ty_env),
        prop_term_denote (get_post_prop_forall T2) _ env && sep_term_denote (get_post_sep_forall T2) _ env --||--
        prop_term_denote (c ++ cq) _ env && sep_term_denote (C ++ CQ) _ env) /\
    (forall ty_env (env : environment ty_env),
        prop_term_denote (get_post_prop_forall T1) _ env && sep_term_denote (get_post_sep_forall T1) _ env --||--
        prop_term_denote (d ++ cq) _ env && sep_term_denote (D ++ CQ) _ env).
    intros.
    pose proof soundness_helper0 as H1.
    destruct (H1 _ _ _ _ _ _ _ _ _ _ _ _ H H0) as [cp [cq [CP [CQ [? [? [? [? [? [? [? ?]]]]]]]]]]].
    exists cp, cq, CP, CQ; split; [ | split; [ | split ]]; intros;
    apply (permutation_equiv_sep _ _ _ env) in H2, H3, H4, H5;
    apply (permutation_equiv_prop _ _ _ env) in H6, H7, H8, H9.
    rewrite <- H2, H6; reflexivity.
    rewrite <- H3, H7; reflexivity.
    rewrite <- H4, H8; reflexivity.
    rewrite <- H5, H9; reflexivity.
Qed. *)

Definition get_var_list_forall (T : ForallTerm) :=
    match T with
    | TForall a _ _ => a
    end.

Definition get_post_var_list (T : ForallTerm) :=
    match T with
    | TForall _ _ (TExists a _) => a
    end.

Definition get_post_forall (T : ForallTerm) :=
    match T with
    | TForall _ _ post => post
    end.

Fixpoint check_right_exists_add (T : ExistsTerm) (ops : list Operation) : bool :=
    match ops with
    | nil => true
    | op :: opxs =>
        match op with
        | ORightExistsAdd x => not_appear_free_exists T x && check_right_exists_add T opxs
        | _ => check_right_exists_add T opxs
        end
    end.

Lemma apply_operation_keep_var_list :
    forall op T1 T2,
        apply_operation op (Some T1) = Some T2 ->
        exists a' b', 
        a' ++ get_var_list_forall T1 = get_var_list_forall T2 /\
        b' ++ get_post_var_list T1 = get_post_var_list T2.
    intros; destruct op;
    destruct T1 as [a1 [p1 P1] [b1 [q1 Q1]]];
    destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
    simpl in *.
    - injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - destruct (erase_sep P1 H0); try discriminate; injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - destruct (erase_sep Q1 H0); try discriminate; injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - destruct (erase_prop p1 H0); try discriminate; injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - destruct (erase_prop q1 H0); try discriminate; injection H as ?; subst.
      exists nil, nil; repeat split; reflexivity.
    - injection H as ?; subst.
      exists (cons v nil), nil; repeat split; reflexivity.
    - injection H as ?; subst.
      exists nil, (cons v nil); repeat split; reflexivity.
Qed.

Lemma apply_operations_keep_var_list :
    forall ops T1 T2,
        apply_operations T1 ops = Some T2 ->
        exists a' b',
        a' ++ get_var_list_forall T1 = get_var_list_forall T2 /\
        b' ++ get_post_var_list T1 = get_post_var_list T2.
    induction ops.
    - intros; simpl in H.
      injection H as ?; subst; exists nil, nil; repeat split; reflexivity.
    - intros.
      rewrite apply_operations_cons in H.
      destruct (apply_operations T1 ops) eqn : ?; [ | discriminate H ].
      pose proof apply_operation_keep_var_list.
      specialize (IHops _ _ Heqo).
      specialize (H0 _ _ _ H).
      destruct IHops as [a' [b' [B C]]];
      destruct H0 as [a'' [b'' [E F]]].
      exists (a'' ++ a'), (b'' ++ b').
      rewrite <- ! app_assoc.
      rewrite B, C, E, F.
      split; reflexivity.
Qed.

Lemma right_exists_add_not_appear_free :
    forall ops T1 T2,
        check_right_exists_add (get_post_forall T1) ops = true ->
        apply_operations T1 ops = Some T2 ->
        exists b', b' ++ get_post_var_list T1 = get_post_var_list T2 /\
                   forallb (not_appear_free_exists (get_post_forall T1)) b' = true.
    induction ops.
    -   intros.
        simpl in *.
        injection H0 as ?; subst.
        exists nil; simpl; tauto.
    -   intros.
        specialize (IHops T1).
        destruct a;
        destruct T1 as [a1 [p1 P1] [b1 [q1 Q1]]];
        destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]];
        simpl in *;
        destruct (apply_operations (TForall a1 (p1, P1) (TExists b1 (q1, Q1))) ops);
        try discriminate;
        destruct f as [af [pf Pf] [bf [qf Qf]]].
        +   injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   simpl in H0.
            destruct (erase_sep Pf H1); try discriminate.
            injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   simpl in H0.
            destruct (erase_sep Qf H1); try discriminate.
            injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   simpl in H0.
            destruct (erase_prop pf H1); try discriminate.
            injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   simpl in H0.
            destruct (erase_prop qf H1); try discriminate.
            injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   injection H0 as ?; subst.
            specialize (IHops _ H eq_refl).
            destruct IHops as [b' ?].
            exists b'; apply H0.
        +   injection H0 as ?; subst.
            apply andb_true_iff in H; destruct H.
            specialize (IHops _ H0 eq_refl).
            destruct IHops as [b' ?].
            simpl in H1; destruct H1.
            exists (v :: b'); split.
            simpl; rewrite H1; reflexivity.
            simpl; rewrite H2, H; reflexivity.
Qed.

Lemma var_list_forall_denote_entail :
    forall vl ty_env (env : environment ty_env) cont,
        var_list_forall_denote vl _ env cont -> cont _ env.
    induction vl.
    - intros; simpl in H. apply H.
    - intros.
      simpl in H.
      destruct a, env; simpl in *.
      apply IHvl.
      specialize (H (tm_env z z0)).
      rewrite term_mapping_update_lookup in H.
      apply H.
Qed.

Lemma var_list_all_denote_entail :
    forall vl ty_env (env : environment ty_env) cont,
        var_list_all_denote vl _ env cont |-- cont _ env.
    induction vl.
    - intros; simpl; entailer!.
    - intros; simpl.
      destruct a; simpl in *.
      unfold CRules.derivable1, CRules.allp in *; intros.
      apply IHvl.
      destruct env.
      specialize (H (tm_env z z0)); simpl in H.
      rewrite term_mapping_update_lookup in H.
      apply H.
Qed.
    
(* Lemma rc_denote_entail :
    forall sc a b c d A B C D ty_env (env : environment ty_env),
        rc_denote (RC sc a b c d A B C D) _ env ->
        ps_term_denote (sc ++ a, A) _ env |-- ps_term_denote (b, B) _ env **
        rc_denote_post c C d D (get_var_list_ps_term ((sc ++ a) ++ b, A ++ B)) _ env.
    intros; unfold rc_denote in *.
    apply var_list_forall_denote_entail in H.
    unfold rc_denote_pre_atom in H.
    apply H.
Qed. *)

Lemma soundness_helper2 :
    forall ops a0 a1 pre1 post1 b pre2 post2,
        apply_operations (TForall (cons a0 a1) pre1 post1) ops =
        Some (TForall b pre2 post2) ->
    exists bl br,
        b = bl ++ (cons a0 br) /\
        apply_operations (TForall a1 pre1 post1) ops =
        Some (TForall (bl ++ br) pre2 post2).
    induction ops; intros; simpl in *.
    -   injection H as ?.
        exists nil, a1; subst.
        split; reflexivity.
    -   destruct a; destruct (apply_operations (TForall (a0 :: a1) pre1 post1) ops) eqn : ?; try discriminate.
        +   simpl in H; rewrite H in Heqo.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H2; simpl; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            destruct (erase_ps_sep pre H0) eqn : ?; try discriminate.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; rewrite Heqo0; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            destruct (erase_exists_sep post H0) eqn : ?; try discriminate.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; rewrite Heqo0; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            destruct (erase_ps_prop pre H0) eqn : ?; try discriminate.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; rewrite Heqo0; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            destruct (erase_exists_prop post H0) eqn : ?; try discriminate.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H1; simpl; rewrite Heqo0; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists (v :: bl), br; split; try assumption.
            rewrite H; simpl; reflexivity.
            rewrite H0; simpl; reflexivity.
        +   simpl in H; destruct f; simpl in *.
            injection H as ?; subst.
            specialize (IHops _ _ _ _ _ _ _ Heqo).
            destruct IHops as [bl [br [? ?]]].
            exists bl, br; split; try assumption.
            rewrite H0; simpl; reflexivity.
Qed.

Lemma forall_term_denote_split :
    forall l x r pre post ty_env (env : environment ty_env),
        forall_term_denote (TForall (l ++ x :: r) pre post) _ env ->
        forall v, forall_term_denote (TForall (l ++ r) pre post) _ (term_mapping_update_env env (fst x) (snd x) v).
    induction l; intros.
    -   destruct x; simpl in *; destruct env.
        specialize (H v); simpl in *.
        assumption.
    -   destruct a; simpl.
        simpl in H.
        intros v0; specialize (H v0).
        destruct (var_type_eqb (z, z0) x) eqn : ?.
        +   rewrite var_type_eqb_eq in Heqb; inversion Heqb; subst; simpl in *.
            specialize (IHl _ _ _ _ _ _ H v0).
            destruct env; simpl in *; rewrite term_mapping_update_shallow in *.
            apply IHl.
        +   rewrite var_type_eqb_neq in Heqb; simpl in Heqb.
            specialize (IHl _ _ _ _ _ _ H v).
            destruct env; simpl in *; rewrite term_mapping_update_swap.
            apply IHl.
            lia.
Qed.

Lemma sc_denote_add :
    forall sc p P post ty_env env,
        sc_denote sc (p, P) ty_env env ->
        forall_term_denote (TForall nil (sc ++ p, P) post) ty_env env ->
        forall_term_denote (TForall nil (p, P) post) ty_env env.
    intros.
    simpl in *.
    rewrite prop_term_denote_app in H0.
    unfold sc_denote in H.
    apply var_list_forall_denote_entail in H.
    simpl in *.
    rewrite ! prop_term_denote_equiv in *.
    unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.coq_prop, CRules.sepcon in *.
    intros; specialize (H m); specialize (H0 m).
    tauto.
Qed.

Lemma soundness : forall ops fl sc a b c d A B C D T1 T2 ty_env (env : environment ty_env),
    check_right_exists_add (get_post_forall T1) ops = true ->
    forallb (not_appear_free_ps_term ((sc ++ a) ++ b, A ++ B)) (get_post_var_list T2) = true ->
    apply_operations T1 ops = Some T2 ->
    gen_rc ops = RC fl sc a b c d A B C D ->
    ProvableRC (RC fl sc a b c d A B C D) _ env ->
    ProvableSC sc (get_pre_forall T1) _ env ->
    Provable T2 _ env ->
    Provable T1 _ env.
Admitted.
    (* unfold Provable, ProvableRC, ProvableSC in *.
    intros ops sc a b c d A B C D T1.
    apply (ind_forall T1).
    - intros pre post T2 ty_env env H H15 H0 H1 H2 H3 H4.
      pose proof soundness_helper1.
      destruct (H5 _ _ _ _ _ _ _ _ _ _ _ _ H0 H1) as [cp [cq [CP [CQ [? [? [? ?]]]]]]]; clear H5.
      pose proof right_exists_add_not_appear_free.
      destruct (H5 _ _ _ H H0) as [b' [? ?]]; clear H5 H H1.
      destruct pre as [p P];
      destruct post as [q Q];
      destruct T2 as [a' [p' P'] [q' Q']].
      simpl in H3.
      apply sc_denote_add with (sc := sc).
      assumption.
      apply apply_operations_keep_var_list in H0; simpl in H0, H6, H7, H8, H9, H10, H11.
      destruct H0 as [? [? [? _]]].
      rewrite app_nil_r in H; subst a' q'.
      rewrite forall_term_denote_nil in *.
      simpl ps_term_denote.
      rewrite prop_term_denote_app.
      pose proof rc_denote_entail.
      specialize (H _ _ _ _ _ _ _ _ _ _ _ H2).
      rewrite logic_equiv_andp_assoc.
      rewrite H6.
      apply derivable1_trans with (y :=
        (prop_term_denote (sc ++ a) ty_env env && sep_term_denote A ty_env env) **
        (prop_term_denote cp ty_env env && sep_term_denote CP ty_env env)
      ). {
        clear.
        rewrite ! prop_term_denote_app, sep_term_denote_app, ! prop_term_denote_equiv.
        unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.sepcon, CRules.coq_prop.
        intros; simpl.
        my_destruct H.
        exists x, x0.
        tauto.
      }
      rewrite H.
      apply var_list_forall_denote_entail in H4.
      simpl ps_term_denote in H4.
      rewrite H7 in H4.
      rewrite sep_term_denote_app, prop_term_denote_app in H4.
      apply derivable1_trans with (y :=
        (prop_term_denote b ty_env env && prop_term_denote cp ty_env env &&
        sep_term_denote B ty_env env ** sep_term_denote CP ty_env env) ** (rc_denote_post c C d D (get_var_list_ps_term ((sc ++ a) ++ b, A ++ B)) ty_env env)
      ). {
        clear.
        simpl ps_term_denote.
        rewrite ! prop_term_denote_equiv.
        unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.sepcon, CRules.coq_prop.
        intros; simpl.
        my_destruct H.
        apply mem_join_comm in H0.
        pose proof mem_join_assoc2.
        specialize (H6 _ _ _ _ _ H0 H).
        destruct H6 as [x23 [? ?]].
        apply mem_join_comm in H7.
        exists x23, x2; repeat split; try tauto.
        exists x1, x0; tauto.
      }
      rewrite H4.
      destruct Q', Q.
      simpl in H8, H9.
      assert (forall ty_env env,
                (prop_term_denote (c ++ cq) ty_env env && sep_term_denote (C ++ CQ) ty_env env) **
                rc_denote_post c C d D (get_var_list_ps_term ((sc ++ a) ++ b, A ++ B)) ty_env env |--
                prop_term_denote (d ++ cq) ty_env env && sep_term_denote (D ++ CQ) ty_env env). {
        clear; intros.
        apply derivable1_trans with (y :=
          prop_term_denote (c ++ cq) ty_env env && sep_term_denote (C ++ CQ) ty_env env **
          rc_denote_post c C d D (get_var_list_ps_term ((sc ++ a) ++ b, A ++ B)) ty_env env
        ). {
            rewrite ! prop_term_denote_equiv.
            unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.sepcon, CRules.coq_prop.
            intros; my_destruct H.
            repeat split; try tauto.
            exists x, x0; tauto.
        }
        rewrite ! prop_term_denote_app, ! sep_term_denote_app.
        unfold rc_denote_post; rewrite var_list_all_denote_entail.
        apply derivable1_trans with (y :=
          ((prop_term_denote c ty_env env && sep_term_denote C ty_env env) **
          rc_denote_post_atom c C d D ty_env env) **
          (prop_term_denote cq ty_env env && sep_term_denote CQ ty_env env)
        ). {
          clear.
          rewrite ! prop_term_denote_equiv.
          unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.sepcon, CRules.coq_prop.
          intros; simpl.
          my_destruct H.
          apply mem_join_comm in H2.
          pose proof mem_join_assoc2.
          specialize (H6 _ _ _ _ _ H2 H0).
          destruct H6 as [x23 [? ?]].
          apply mem_join_comm in H7.
          exists x23, x2; repeat split; try tauto.
          exists x1, x0; tauto.
        }
        unfold rc_denote_post_atom.
        simpl ps_term_denote.
        sep_apply wand_elim.
        rewrite ! prop_term_denote_equiv.
        unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.coq_prop, CRules.sepcon.
        intros.
        my_destruct H.
        repeat split; try tauto.
        exists x, x0; tauto.
      }
      assert (forall ty_env env,
                (prop_term_denote p0 ty_env env && sep_term_denote s ty_env env) ** rc_denote_post c C d D (get_var_list_ps_term ((sc ++ a) ++ b, A ++ B)) ty_env env
                |-- prop_term_denote p1 ty_env env && sep_term_denote s0 ty_env env). {
        intros.
        rewrite H8, H9.
        apply H0.
      }
      assert (forall l ty_env env,
                forallb (not_appear_free_ps_term ((sc ++ a) ++ b, A ++ B)) l = true ->
                exists_term_denote (TExists l (p0, s)) ty_env env ** rc_denote_post c C d D (get_var_list_ps_term ((sc ++ a) ++ b, A ++ B)) ty_env env
                |-- exists_term_denote (TExists l (p1, s0)) ty_env env). {
        clear - H1 H15.
        induction l; intros.
        - simpl in *.
          apply H1.
        - destruct a0; simpl.
          Intros v; Exists v.
          rewrite forallb_forall in H.
          pose proof rc_denote_post_equiv.
          rewrite H0 with (x := (z, z0)) (v := v).
          apply IHl.
          apply forallb_forall.
          intros.
          apply H.
          right; apply H2.
          pose proof get_var_list_not_appear_free_true_ps.
          specialize (H2 ((sc ++ a) ++ b, A ++ B) (z, z0)).
          apply H2.
          apply H.
          left; reflexivity.
      }
      sep_apply H5.
      2: apply H15.
      clear - H11.
      generalize dependent ty_env.
      induction b'; intros.
      + reflexivity.
      + simpl in H11.
        apply andb_true_iff in H11.
        destruct H11.
        pose proof not_appear_free_exists_equiv.
        specialize (H1 (TExists q (p1, s0)) a H).
        destruct a; simpl in *.
        Intros v.
        rewrite IHb' by assumption.
        rewrite <- H1.
        reflexivity.
    - intros x t H T2 ty_env env H0 H15 H1 H2 H3 H4 H5.
      destruct x.
      rewrite forall_term_denote_cons.
      destruct t, T2.
      simpl in H1.
      apply soundness_helper2 in H1.
      destruct H1 as [bl [br [? ?]]].
      intros.
      rewrite rc_denote_equiv with (x := (z, z0)) (v := v) in H3.
      rewrite sc_denote_equiv with (x := (z, z0)) (v := v) in H4.
      simpl in H0.
      simpl check_right_exists_add in H.
      destruct post0.
      specialize (H (TForall (bl ++ br) pre0 (TExists vl1 t)) _ _ H0 H15 H6 H2 H3 H4); clear H6 H2 H3 H4; subst.
      eapply forall_term_denote_split in H5; simpl in *.
      apply H in H5.
      apply H5.
Qed. *)

Fixpoint instantiate_wexpr ty (e : Wexpr ty) (x ty' : Z) (v : Wexpr ty') : Wexpr ty :=
    match e as e0 in Wexpr ty0 return Wexpr ty0 with
    | EVar a ty'' => match Z.eq_dec a x with
                     | left _ => 
                       match Z.eq_dec ty' ty'' with
                       | left H => eq_rect _ _ v _ H
                       | right _ => EVar a ty''
                       end
                     | right _ => EVar a ty''
                     end
    | EConstZ val => EConstZ val
    | EField e' a b => EField (instantiate_wexpr _ e' x ty' v) a b
    | EFunc f sig args =>
        EFunc f sig ((fix instantiate_dlist l (dl : Induct.dlist Z Wexpr l) (x ty' : Z) (v : Wexpr ty') : Induct.dlist Z Wexpr l :=
            match dl as dl0 in Induct.dlist _ _ l0 return Induct.dlist Z Wexpr l0 with
            | Induct.dnil => Induct.dnil _ _
            | Induct.dcons a Pa b Pb  => Induct.dcons _ _ _ (instantiate_wexpr a Pa x ty' v) _ (instantiate_dlist b Pb x ty' v)
            end) _ args x ty' v)
    end.

Fixpoint instantiate_dlist l (dl : Induct.dlist Z Wexpr l) (x ty : Z) (v : Wexpr ty) : Induct.dlist Z Wexpr l :=
    match dl as dl0 in Induct.dlist _ _ l0 return Induct.dlist Z Wexpr l0 with
    | Induct.dnil => Induct.dnil _ _
    | Induct.dcons a Pa b Pb => Induct.dcons _ _ _ (instantiate_wexpr a Pa x ty v) _ (instantiate_dlist b Pb x ty v)
    end.

Lemma wexpr_denote_instantiate_equiv :
    forall ty (e : Wexpr ty) x ty' v ty_env env,
        wexpr_denote _ (instantiate_wexpr _ e x ty' v) ty_env env = 
        wexpr_denote _ e _ (term_mapping_update_env env x ty' (wexpr_denote _ v ty_env env)).
    pose (Q := (fun l (dl : Induct.dlist _ _ l) => forall x ty' v ty_env env,
        Induct.dmap (fun ty e => wexpr_denote ty e ty_env env) (instantiate_dlist _ dl x ty' v) =
        Induct.dmap (fun ty e => wexpr_denote ty e _ (term_mapping_update_env env x ty' (wexpr_denote _ v ty_env env))) dl)).
    induction e using wexpr_ind with (Q := Q); intros.
    - simpl.
      destruct (Z.eq_dec x x0); subst.
      destruct (Z.eq_dec ty' ty); subst.
      + rewrite <- Eqdep.EqdepTheory.eq_rect_eq.
        destruct env; simpl.
        rewrite term_mapping_update_eq.
        reflexivity.
      + simpl.
        destruct env.
        simpl.
        rewrite term_mapping_update_neq by lia.
        reflexivity.
      + simpl.
        destruct env.
        simpl.
        rewrite term_mapping_update_neq by lia.
        reflexivity.
    - reflexivity.
    - simpl.
      rewrite IHe.
      destruct env; reflexivity.
    - simpl.
      rewrite IHe.
      destruct env; reflexivity.
    - unfold Q.
      reflexivity.
    - unfold Q in *.
      intros; simpl.
      rewrite IHe, IHe0.
      reflexivity.
Qed.

Lemma wexpr_dlist_instantiate_equiv :
    forall l (dl : Induct.dlist Z Wexpr l) x ty v ty_env env,
        Induct.dmap (fun ty e => wexpr_denote ty e ty_env env) (instantiate_dlist _ dl x ty v) =
        Induct.dmap (fun ty' e => wexpr_denote ty' e _ (term_mapping_update_env env x ty (wexpr_denote _ v ty_env env))) dl.
    induction dl.
    - reflexivity.
    - simpl; intros.
      rewrite wexpr_denote_instantiate_equiv.
      rewrite IHdl.
      reflexivity.
Qed.

Fixpoint instantiate_prop_atom (t : PropAtomTerm) (x ty : Z) (v : Wexpr ty) : PropAtomTerm :=
    match t with
    | TPropTrue => TPropTrue
    | TPropFalse => TPropFalse
    | TPropNot p => TPropNot (instantiate_prop_atom p x ty v)
    | TPropEq ty' e1 e2 => TPropEq ty' (instantiate_wexpr _ e1 x ty v) (instantiate_wexpr _ e2 x ty v)
    | TPropAnd p1 p2 => TPropAnd (instantiate_prop_atom p1 x ty v) (instantiate_prop_atom p2 x ty v)
    | TPropOr p1 p2 => TPropOr (instantiate_prop_atom p1 x ty v) (instantiate_prop_atom p2 x ty v)
    | TPropImply p1 p2 => TPropImply (instantiate_prop_atom p1 x ty v) (instantiate_prop_atom p2 x ty v)
    | TPropIff p1 p2 => TPropIff (instantiate_prop_atom p1 x ty v) (instantiate_prop_atom p2 x ty v)
    | TPropFunc f sig args => TPropFunc f sig (instantiate_dlist _ args x ty v)
    end.

Lemma prop_atom_instantiate_equiv :
    forall t x ty v ty_env env,
        prop_atom_term_denote (instantiate_prop_atom t x ty v) ty_env env <->
        prop_atom_term_denote t _ (term_mapping_update_env env x ty (wexpr_denote _ v ty_env env)).
    induction t; intros; simpl; try tauto.
    - rewrite IHt; tauto.
    - rewrite ! wexpr_denote_instantiate_equiv.
      reflexivity.
    - rewrite IHt1, IHt2; tauto.
    - rewrite IHt1, IHt2; tauto.
    - rewrite IHt1, IHt2; tauto.
    - rewrite IHt1, IHt2; tauto.
    - rewrite wexpr_dlist_instantiate_equiv.
      destruct env; reflexivity.
Qed.

Definition instantiate_prop (t : PropTerm) (x ty : Z) (v : Wexpr ty) : PropTerm :=
    map (fun t => instantiate_prop_atom t x ty v) t.

Lemma prop_instantiate_equiv :
    forall t x ty v ty_env env,
        prop_term_denote (instantiate_prop t x ty v) ty_env env --||--
        prop_term_denote t _ (term_mapping_update_env env x ty (wexpr_denote _ v ty_env env)).
    induction t; intros; simpl; try tauto.
    - reflexivity.
    - rewrite IHt.
      unfold CRules.andp, logic_equiv, derivable1, CRules.truep, CRules.coq_prop.
      split; intros.
      + destruct H.
        rewrite prop_atom_instantiate_equiv in H0.
        tauto.
      + destruct H.
        rewrite <- prop_atom_instantiate_equiv in H0.
        tauto.
Qed.

Definition instantiate_sep_atom (t : SepAtomTerm) (x ty : Z) (v : Wexpr ty) : SepAtomTerm :=
    match t with
    | TSepDataAt addr ty' val => TSepDataAt (instantiate_wexpr _ addr x ty v) ty' (instantiate_wexpr _ val x ty v)
    | TSepFunc f sig args => TSepFunc f sig (instantiate_dlist _ args x ty v)
    end.

Lemma sep_atom_instantiate_equiv :
    forall t x ty v ty_env env,
        sep_atom_term_denote (instantiate_sep_atom t x ty v) ty_env env --||--
        sep_atom_term_denote t _ (term_mapping_update_env env x ty (wexpr_denote _ v ty_env env)).
    destruct t; simpl; intros; try tauto.
    - rewrite ! wexpr_denote_instantiate_equiv.
      reflexivity.
    - rewrite wexpr_dlist_instantiate_equiv.
      destruct env; reflexivity.
Qed.

Definition instantiate_sep (t : SepTerm) (x ty : Z) (v : Wexpr ty) : SepTerm :=
    map (fun t => instantiate_sep_atom t x ty v) t.

Lemma sep_instantiate_equiv :
    forall t x ty v ty_env env,
        sep_term_denote (instantiate_sep t x ty v) ty_env env --||--
        sep_term_denote t _ (term_mapping_update_env env x ty (wexpr_denote _ v ty_env env)).
    induction t; intros; simpl; try tauto.
    - reflexivity.
    - rewrite IHt, sep_atom_instantiate_equiv.
      reflexivity.
Qed.

Definition instantiate_ps (t : PSTerm) (x ty : Z) (v : Wexpr ty) : PSTerm :=
    match t with
    | (p, s) => (instantiate_prop p x ty v, instantiate_sep s x ty v)
    end.

Fixpoint var_list_erase (x : VarType) (vl : VarList) : VarList :=
    match vl with
    | nil => nil
    | a :: vl' => if var_type_eqb a x then vl' else a :: var_list_erase x vl'
    end.

Definition instantiate_exists (t : ExistsTerm) (x ty : Z) (v : Wexpr ty) : option ExistsTerm :=
    match t with
    | TExists vl t' =>
        if not_appear_free_var_list vl (x, ty) then None else
        Some (TExists (var_list_erase (x, ty) vl) (instantiate_ps t' x ty v))
    end.

Definition instantiate_forall (t : ForallTerm) (x ty : Z) (v : Wexpr ty) : option ForallTerm :=
    match t with
    | TForall vl pre post => match (instantiate_exists post x ty v) with
                             | Some post' => Some (TForall vl pre post')
                             | None => None
                             end
    end.

Lemma var_list_erase_split :
    forall a l,
        In a l ->
        exists l1 l2, l = l1 ++ a :: l2 /\ var_list_erase a l = l1 ++ l2.
    induction l.
    - intros; inversion H.
    - intros.
      destruct H.
      + subst.
        exists nil, l; simpl.
        rewrite var_type_eqb_refl; split; reflexivity.
      + specialize (IHl H).
        destruct IHl as [l1 [l2 [? ?]]].
        simpl.
        destruct (var_type_eqb a0 a) eqn : ?; [
            apply var_type_eqb_eq in Heqb |
            apply var_type_eqb_neq in Heqb
        ].
        * exists nil, l; subst; simpl.
          split; reflexivity.
        * exists (a0 :: l1), l2; simpl; subst.
          rewrite H1; split; reflexivity.
Qed.

Lemma exists_term_denote_app :
    forall l1 x y ps1 ps2,
        (forall ty_env env, exists_term_denote (TExists x ps1) ty_env env |-- exists_term_denote (TExists y ps2) ty_env env) ->
        (forall ty_env env, exists_term_denote (TExists (l1 ++ x) ps1) ty_env env |-- exists_term_denote (TExists (l1 ++ y) ps2) ty_env env).
    induction l1; intros.
    - simpl; apply H.
    - simpl; destruct a.
      Intros v; Exists v.
      apply IHl1.
      apply H.
Qed.

Lemma exists_term_denote_perm :
    forall l1 l2 ps ty_env env,
        Permutation l1 l2 ->
        exists_term_denote (TExists l1 ps) ty_env env |--
        exists_term_denote (TExists l2 ps) ty_env env.
    intros.
    generalize dependent ty_env.
    induction H.
    - reflexivity.
    - intros; destruct x; simpl in *.
      Intros v; Exists v.
      apply IHPermutation.
    - intros; destruct x; destruct y; destruct env; simpl.
      destruct (Z.eq_dec z1 z); subst.
      2:{ 
        Intros v1 v2;
        Exists v2 v1;
        rewrite term_mapping_update_swap; [ reflexivity | left; assumption].
      }
      destruct (Z.eq_dec z2 z0); subst.
      Intros v v0;
      Exists v v0.
      rewrite ! term_mapping_update_shallow.
      reflexivity.
      Intros v1 v2;
      Exists v2 v1;
      rewrite term_mapping_update_swap; [ reflexivity | right; assumption].
    - intros; sep_apply IHPermutation1; apply IHPermutation2.
Qed.

Lemma instantiate_sound :
    forall T1 T2 x ty v ty_env env,
        instantiate_forall T1 x ty v = Some T2 ->
        Provable T2 ty_env env ->
        Provable T1 ty_env env.
    intros T1.
    apply (ind_forall T1); intros; unfold Provable in *.
    - destruct pre as [p1 P1];
      destruct post as [b1 [q1 Q1]];
      destruct T2 as [a2 [p2 P2] [b2 [q2 Q2]]].
      simpl in H.
      destruct (not_appear_free_var_list b1 (x, ty)) eqn : ?; try discriminate.
      injection H as ?.
      subst.
      rewrite forall_term_denote_nil in *.
      sep_apply H0.
      apply not_appear_free_var_list_in in Heqb.
      apply var_list_erase_split in Heqb.
      destruct Heqb as [l1 [l2 [? ?]]].
      rewrite H1, H.
      apply derivable1_trans with (y := exists_term_denote (TExists (l1 ++ l2 ++ cons (x, ty) nil) (q1, Q1)) ty_env env).
      2:{
        apply exists_term_denote_app; intros.
        apply exists_term_denote_perm.
        apply Permutation_app_comm.
      }
      rewrite app_assoc.
      rewrite <- app_nil_r with (l := l1 ++ l2).
      rewrite <- app_assoc with (l := (l1 ++ l2)).
      apply exists_term_denote_app; intros; simpl.
      rewrite prop_instantiate_equiv.
      rewrite sep_instantiate_equiv.
      Exists (wexpr_denote ty v ty_env0 env0).
      reflexivity.
    - destruct x as [x' ty']; rewrite forall_term_denote_cons; intros.
      destruct t as [a1 [p1 P1] [b1 [q1 Q1]]].
      simpl instantiate_forall in H0.
      destruct (not_appear_free_var_list b1 (x0, ty)) eqn : ?; try discriminate.
      injection H0 as ?; subst T2.
      eapply H with (x := x0) (ty := ty) (v := v).
      2: {
        assert (
            forall_term_denote
            (ForallCons (x', ty') (TForall a1 (p1, P1) (TExists (var_list_erase (x0, ty) b1)
            (instantiate_prop q1 x0 ty v,
            instantiate_sep Q1 x0 ty v)))) ty_env env
        ) by apply H1; clear H1.
        rewrite forall_term_denote_cons in H0.
        apply H0.
      }
      simpl.
      rewrite Heqb.
      reflexivity.
Qed.