From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.
Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.

Module Induct.

    Inductive dlist (A: Type) (P: A -> Type): list A -> Type :=
    | dnil: dlist A P nil
    | dcons (a: A) (x: P a) (l: list A) (L: dlist A P l): dlist A P (cons a l).
    
    Fixpoint dlist_eqb {A : Type} {P : A -> Type} (l1 l2 : list A)
                    (eqA : A -> A -> bool) (eqP : forall A B, P A -> P B -> bool)
                    (dl1 : dlist A P l1) (dl2 : dlist A P l2) : bool :=
        match dl1, dl2 with
        | dnil _ _, dnil _ _ => true
        | dcons _ _ x Px xs Pxs, dcons _ _ y Py ys Pys =>
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
