Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.ShallowQuantifierLogic.Syntax.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Morphisms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class ShallowExistsDeduction (L : Language) {expL : ShallowExistsLanguage L} (GammaD1 : Derivable1 L) := {
  derivable1s_exp_r : forall (A : Type) (P : expr) (Q : A -> expr) (x : A),
    P |-- (Q x) -> P |-- (exp Q);
  derivable1s_exp_l : forall (A : Type) (P : A -> expr) (Q : expr),
    (forall x, (P x) |-- Q) -> (exp P) |-- Q;
}.

Class ShallowForallDeduction (L : Language) {allpL : ShallowForallLanguage L} (GammaD1 : Derivable1 L) := {
  derivable1s_allp_r : forall (A : Type) (P : expr) (Q : A -> expr),
    (forall x, P |-- (Q x)) -> P |-- (allp Q);
  derivable1s_allp_l : forall (A : Type) (P : A -> expr) (Q : expr) (x : A),
    P x |-- Q -> (allp P) |-- Q;
}.

Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.

Section ExistsAllDeductionRules.

Context {L: Language}
        {expL: ShallowExistsLanguage L}
        {allpL: ShallowForallLanguage L}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {expD: ShallowExistsDeduction L GammaD1}
        {allpD: ShallowForallDeduction L GammaD1}.

Lemma derivable1s_ex_l_unfold: forall (A: Type)(P: A -> expr) Q,
  (exists x, P x |-- Q) -> allp P |-- Q.
Proof. 
  intros. destruct H. eapply derivable1s_allp_l; eauto.
Qed.

Lemma derivable1_allp_allp_swap: forall (A B: Type) (P: A -> B -> expr), allp (fun x => allp (fun y => P x y)) |-- allp (fun y => allp (fun x => P x y)).
Proof. 
  intros. apply derivable1s_allp_r. intros. apply derivable1s_allp_r. intros.
  eapply (derivable1s_allp_l _ _ _ x0). eapply (derivable1s_allp_l _ _ _ x). apply derivable1_refl.
Qed.

Lemma derivable1_exp_allp_swap: forall (A B: Type) (P: A -> B -> expr), exp (fun x => allp (fun y => P x y)) |-- allp (fun y => exp (fun x => P x y)).
Proof.
  intros. apply derivable1s_exp_l. intros. apply derivable1s_allp_r. intros. eapply (derivable1s_exp_r _ _ _ x); eauto. eapply (derivable1s_allp_l _ _ _ x0); eauto. apply derivable1_refl.
Qed. 

End ExistsAllDeductionRules.

Section ExistsDeductionRulesAnd.

Context {L : Language}
        {minL : MinimumLanguage L}
        {andpL : AndLanguage L}
        {expL : ShallowExistsLanguage L}
        {GammaD1 : Derivable1 L}
        {andpD : AndDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}
        {expD : ShallowExistsDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        .
        
Lemma aux_ex_and0 : forall {A : Type} (P Q : A -> expr),
  exp (fun a => (P a) && (Q a)) |-- (exp P) && (exp Q).
Proof. 
  intros.
  apply derivable1s_truep_intros.
  + apply derivable1s_exp_l. intros. 
    eapply derivable1_trans; [apply derivable1_andp_elim1 | ].
    eapply derivable1s_exp_r. apply derivable1_refl.
  + apply derivable1s_exp_l. intros.
    eapply derivable1_trans; [apply derivable1_andp_elim2 | ].
    eapply derivable1s_exp_r. apply derivable1_refl.
Qed.

Lemma aux_ex_and1' : forall {A : Type} (P : A -> expr) (Q : expr),
  exp (fun x => (P x && Q)) |-- ((exp P) && Q).
Proof. 
  intros. apply derivable1s_truep_intros.
  + apply derivable1s_exp_l. intros.
    eapply derivable1_trans; [apply derivable1_andp_elim1 | ].
    eapply derivable1s_exp_r. apply derivable1_refl.
  + apply derivable1s_exp_l. intros. 
    apply derivable1_andp_elim2.
Qed.

Lemma aux_ex_and2' : forall {A : Type} (P : expr) (Q : A -> expr),
  exp (fun x => (P && Q x)) |-- (P && (exp Q)).
Proof.
  intros. apply derivable1s_truep_intros.
  + apply derivable1s_exp_l. intros.
    apply derivable1_andp_elim1.
  + apply derivable1s_exp_l. intros.
    eapply derivable1_trans; [apply derivable1_andp_elim2 | ].
    eapply derivable1s_exp_r. apply derivable1_refl.
Qed.

Lemma aux_ex_and1_ : forall (A : Type) (P : A -> expr) (Q : expr), 
  ((exp P) && Q) |-- exp (fun x => (P x && Q)).
Proof. 
  intros.
  rewrite <- derivable1s_impp_andp_adjoint.
  apply derivable1s_exp_l. intros. rewrite derivable1s_impp_andp_adjoint.
  eapply derivable1s_exp_r.
  apply derivable1s_truep_intros; [| apply derivable1_andp_elim2].
  eapply derivable1_trans; [apply derivable1_andp_elim1 | apply derivable1_refl].
Qed.

Lemma aux_ex_and2_ : forall (A : Type) (P : expr) (Q : A -> expr),
  (P && (exp Q)) |-- exp (fun x => (P && Q x)).
Proof. 
  intros.
  eapply derivable1_trans; [apply derivable1_andp_comm |].
  rewrite <- derivable1s_impp_andp_adjoint.
  apply derivable1s_exp_l. intros. rewrite derivable1s_impp_andp_adjoint.
  eapply derivable1s_exp_r.
  apply derivable1s_truep_intros; [apply derivable1_andp_elim2 |].
  eapply derivable1_trans; [apply derivable1_andp_elim1 | apply derivable1_refl]. 
Qed.

Class deduction_exp_and := {
  derivable1_exp_andp_l : forall (A : Type) (P : A -> expr) (Q : expr), 
  ((exp P) && Q) |-- exp (fun x => (P x && Q));
  derivable1_andp_exp_l : forall (A : Type) (P : expr) (Q : A -> expr),
  (P && (exp Q)) |-- exp (fun x => (P && Q x));
}.

Lemma ExpDeduction2ExsitsAnd : deduction_exp_and.
Proof. 
  constructor.
  + apply aux_ex_and1_.
  + apply aux_ex_and2_.
Qed.

Lemma logic_equiv_exp_andp
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}: 
  forall (A: Type) (P: A -> expr) (Q: expr),
  ((exp P) && Q) --||-- exp (fun x => (P x && Q)).
Proof. 
  intros; rewrite __logic_equiv_derivable1. split.
  -apply ExpDeduction2ExsitsAnd.
  -apply derivable1s_truep_intros. 
  --apply derivable1s_exp_l. intros. eapply (derivable1s_exp_r _ _ _ x). apply derivable1_andp_elim1.
  --apply derivable1s_exp_l. intros. apply derivable1_andp_elim2.
Qed.

End ExistsDeductionRulesAnd.

Section ExistsDeductionRulesSepcon.

Context {L : Language}
        {sepconL : SepconLanguage L}
        {wandL : WandLanguage L}
        {expL : ShallowExistsLanguage L}
        {GammaD1 : Derivable1 L}
        {sepconD : SepconDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}
        {expD : ShallowExistsDeduction L GammaD1}
        {wandD : WandDeduction L GammaD1}
        .

Lemma __derivable1_exp_sepcon_l : forall (A : Type) (P : A -> expr) (Q : expr),
  ((exp P) * Q) |-- exp (fun x => (P x * Q)).
Proof. 
  intros.
  rewrite derivable1s_wand_sepcon_adjoint.
  apply derivable1s_exp_l. intros. rewrite <- derivable1s_wand_sepcon_adjoint.
  eapply derivable1s_exp_r.
  apply derivable1_sepcon_mono; apply derivable1_refl.
Qed.

Lemma __derivable1_sepcon_exp_l : forall (A : Type) (P : expr) (Q : A -> expr),
  (P * (exp Q)) |-- exp (fun x => (P * Q x)).
Proof.
  intros.
  eapply derivable1_trans; [apply derivable1_sepcon_comm |].
  rewrite derivable1s_wand_sepcon_adjoint.
  apply derivable1s_exp_l. intros. rewrite <- derivable1s_wand_sepcon_adjoint.
  eapply derivable1s_exp_r.
  eapply derivable1_trans; [apply derivable1_sepcon_comm |].
  apply derivable1_sepcon_mono; apply derivable1_refl.
Qed.

Class deduction_exp_sepcon := {
  derivable1_exp_sepcon_l : forall (A : Type) (P : A -> expr) (Q : expr),
  ((exp P) * Q) |-- exp (fun x => (P x * Q));
  derivable1_sepcon_exp_l : forall (A : Type) (P : expr) (Q : A -> expr),
  (P * (exp Q)) |-- exp (fun x => (P * Q x));
}.

Lemma ExpDeduction2ExsitsSepcon : deduction_exp_sepcon.
Proof. 
  constructor.
  + apply __derivable1_exp_sepcon_l.
  + apply __derivable1_sepcon_exp_l.
Qed.

Lemma logic_equiv_exp_sepcon
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}:
  forall (A: Type) (P: A -> expr) (Q: expr),
  ((exp P) * Q) --||-- exp (fun x => (P x * Q)).
Proof. 
  intros. rewrite __logic_equiv_derivable1. split.
  -apply ExpDeduction2ExsitsSepcon.
  -apply derivable1s_exp_l. intros. apply derivable1_sepcon_mono. 
  apply (derivable1s_exp_r _ _ _ x). apply derivable1_refl.
  apply derivable1_refl.
Qed. 

End ExistsDeductionRulesSepcon.

Section IterSepconDerivedRules.

Context {L : Language}
        {sepconL : SepconLanguage L}
        {empL : EmpLanguage L}
        {itersepconL : IterSepconLanguage L}
        {GammaD1 : Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {sepconD : SepconDeduction L GammaD1}
        {empD : EmpDeduction L GammaD1}
        {itersepconD : IterSepconDeduction_left L GammaD1}
        .


Lemma fold_left_prop : forall {A : Type} (f : A -> A -> A) a b l ,
  (forall x y z, f (f x y) z = f x (f y z)) ->
  fold_left f l (f a b) = f a (fold_left f l b).
Proof. 
  intros. revert a b. induction l as [| a' l'].
  + simpl. reflexivity.
  + intros. simpl. rewrite <- IHl'. rewrite H. reflexivity.
Qed.

Lemma fold_left_sepcon_cong : forall l a b,
  a |-- b ->  
  fold_left sepcon l a |-- fold_left sepcon l b.
Proof.
  intros. revert a b H. induction l as [| a' l'].
  + simpl. tauto.
  + simpl. intros. apply IHl'.
    apply derivable1_sepcon_mono; [apply H | apply derivable1_refl].
Qed. 

Lemma derivable1_sepcon_assoc2 : forall a b c, 
  a * b * c |-- a * (b * c).
Proof.
  intros. 
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_sepcon_assoc1.  
  rewrite <- (derivable1_sepcon_comm (b * c) a).
  rewrite <- (derivable1_sepcon_assoc1 b c a).
  rewrite <- (derivable1_sepcon_comm (c * a) b).
  apply derivable1_refl.
Qed.

Lemma fold_left_prop_sepcon1 : forall a b l, 
  fold_left sepcon l (a * b) |-- a * fold_left sepcon l b.
Proof.
  intros. revert a b. induction l as [| a' l'].
  + intros. simpl. reflexivity.
  + intros. simpl. rewrite <- IHl'.
    apply fold_left_sepcon_cong.
    apply derivable1_sepcon_assoc2.
Qed. 

Lemma fold_left_prop_sepcon2 : forall a b l,
  a * fold_left sepcon l b |-- fold_left sepcon l (a * b).
Proof. 
  intros. revert a b. induction l as [| a' l'].
  + intros. simpl. reflexivity.
  + intros. simpl. rewrite IHl'.
    apply fold_left_sepcon_cong.
    apply derivable1_sepcon_assoc1.
Qed.

Lemma itersepcon_cons : forall (a : expr) (l : list expr),
  iter_sepcon (a :: l) |-- a * iter_sepcon l /\
  a * iter_sepcon l |-- iter_sepcon (a :: l).
Proof. 
  intros. split. 
  + rewrite derivable1_iter_sepcon_l. simpl.
    rewrite <- derivable1_iter_sepcon_r. simpl.
    apply (derivable1_trans _ (fold_left sepcon l (a * emp))).
    { apply fold_left_sepcon_cong. apply derivable1_sepcon_comm. }
    rewrite fold_left_prop_sepcon1.
    apply derivable1_refl.
  + rewrite derivable1_iter_sepcon_l. simpl.
    rewrite <- derivable1_iter_sepcon_r. simpl.
    apply (derivable1_trans _ (fold_left sepcon l (a * emp))).
    2:{ apply fold_left_sepcon_cong. apply derivable1_sepcon_comm. }
    rewrite fold_left_prop_sepcon2.
    apply derivable1_refl.
Qed.

Definition itersepcon_cons1 := fun a l => proj1 (itersepcon_cons a l).
Definition itersepcon_cons2 := fun a l => proj2 (itersepcon_cons a l).

Lemma itersepcon_app : forall l1 l2,
  iter_sepcon l1 * iter_sepcon l2 |-- iter_sepcon (l1 ++ l2) /\
  iter_sepcon (l1 ++ l2) |-- iter_sepcon l1 * iter_sepcon l2.
Proof. 
  intros l1. induction l1 as [|a1 l1']; intros.
  + simpl. split. 
    - apply (derivable1_trans _ (emp * iter_sepcon l2)).
      { apply derivable1_sepcon_mono; [| apply derivable1_refl].
        rewrite derivable1_iter_sepcon_l. simpl. apply derivable1_refl. }
      rewrite derivable1_sepcon_comm. apply derivable1_sepcon_emp_l.
    - apply (derivable1_trans _ (emp * iter_sepcon l2)).
      { rewrite <- (derivable1_sepcon_comm (iter_sepcon l2) emp).
        apply derivable1_sepcon_emp_r. }
      apply derivable1_sepcon_mono; [| apply derivable1_refl].
      rewrite <- derivable1_iter_sepcon_r. simpl. apply derivable1_refl.
  + simpl. split.
    - rewrite itersepcon_cons1.
      rewrite <- itersepcon_cons2.
      rewrite derivable1_sepcon_assoc2.
      apply derivable1_sepcon_mono; [apply derivable1_refl |].
      apply (proj1 (IHl1' _)).
    - rewrite itersepcon_cons1.
      rewrite <- itersepcon_cons2.
      rewrite <- derivable1_sepcon_assoc1.
      apply derivable1_sepcon_mono; [apply derivable1_refl |].
      apply (proj2 (IHl1' _)).
Qed.

Definition itersepcon_app1 := fun l1 l2 => proj1 (itersepcon_app l1 l2).
Definition itersepcon_app2 := fun l1 l2 => proj2 (itersepcon_app l1 l2).

Theorem itersepcon_flatten_ : forall xs1 xs2 xs3,
  iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)) |--
  iter_sepcon (xs1 ++ xs2 ++ xs3).
Proof. 
  intros.
  induction xs1 as [| a1' xs1']; simpl.
  + rewrite itersepcon_cons1.
    apply itersepcon_app1.
  + rewrite itersepcon_cons1.
    rewrite <- itersepcon_cons2.
    apply derivable1_sepcon_mono; [apply derivable1_refl |].
    apply IHxs1'.
Qed.

Class IterSepconFlatten := {
  derivable1_iter_sepcon_flatten : forall xs1 xs2 xs3,
    iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)) |--
    iter_sepcon (xs1 ++ xs2 ++ xs3);
}.

Lemma DeductionSepconFlatten : IterSepconFlatten.
Proof. constructor. intros. apply itersepcon_flatten_. Qed.

Context {expL : ShallowExistsLanguage L}
        {expD : ShallowExistsDeduction L GammaD1}
        {exp_sepcon : deduction_exp_sepcon}
        .

Theorem itersepcon_ex {A : Type} : forall 
  (xs1 : list expr) (x : A -> expr) (xs3 : list expr), 
  iter_sepcon (xs1 ++ (exp x :: xs3)) |-- 
  exp (fun a => iter_sepcon (xs1 ++ (x a) :: xs3)).
Proof. 
  intros.
  rewrite itersepcon_app2.
  rewrite itersepcon_cons1.
  rewrite derivable1_sepcon_assoc1.
  rewrite derivable1_sepcon_exp_l.
  rewrite derivable1_exp_sepcon_l.
  apply derivable1s_exp_l. intros.
  eapply derivable1s_exp_r.
  rewrite <- itersepcon_app1.
  rewrite <- itersepcon_cons2.
  rewrite <- derivable1_sepcon_assoc2.
  apply derivable1_refl.
Qed.

Context {truepL : TrueLanguage L}
        {truepD : TrueDeduction L GammaD1}
        {coq_prop_L : CoqPropLanguage L}
        {coq_prop_D : CoqPropDeduction L GammaD1}
        {minL : MinimumLanguage L}
        {andpL : AndLanguage L}
        {andpD : AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {wandL : WandLanguage L}
        {wandD : WandDeduction L GammaD1}
        .

Lemma aux_derivable1_sepcon_coq_prop_andp_l : forall P Q R,
  P * (coq_prop Q && R) |-- (coq_prop Q) && (P * R).
Proof. 
  intros. 
  apply derivable1s_truep_intros.
  + rewrite derivable1_sepcon_comm. 
    rewrite derivable1s_wand_sepcon_adjoint.
    rewrite <- derivable1s_impp_andp_adjoint.
    apply derivable1s_coq_prop_l. intros.
    rewrite derivable1s_impp_andp_adjoint.
    rewrite <- derivable1s_wand_sepcon_adjoint.
    apply derivable1s_coq_prop_r. apply H.
  + apply derivable1_sepcon_mono; [apply derivable1_refl|].
    apply derivable1_andp_elim2.
Qed.

Lemma aux_derivable1_sepcon_coq_prop_andp_r : forall P Q R,
  (coq_prop Q) && (P * R) |-- P * (coq_prop Q && R).
Proof. 
  intros.
  rewrite <- derivable1s_impp_andp_adjoint.
  apply derivable1s_coq_prop_l. intros.
  rewrite derivable1s_impp_andp_adjoint.
  rewrite derivable1_andp_elim2.
  apply derivable1_sepcon_mono; [apply derivable1_refl |].
  apply derivable1s_truep_intros; [| apply derivable1_refl].
  apply derivable1s_coq_prop_r. apply H.
Qed.

Class sepcon_andp_prop := {
  derivable1_sepcon_coq_prop_andp_l : forall P Q R,
    P * (coq_prop Q && R) |-- (coq_prop Q) && (P * R);
  derivable1_sepcon_coq_prop_andp_r : forall P Q R,
    (coq_prop Q) && (P * R) |-- P * (coq_prop Q && R)
}.

Lemma aux_derivable1_sepcon_andp_coq_prop_l {SAP : sepcon_andp_prop} : 
  forall P Q R,
    P * (Q && coq_prop R) |-- (coq_prop R) && (P * Q).
Proof. 
  intros. 
  rewrite derivable1_andp_comm.
  apply derivable1_sepcon_coq_prop_andp_l.
Qed.

Lemma aux_derivable1_sepcon_andp_coq_prop_r {SAP : sepcon_andp_prop} :
  forall P Q R,
    (coq_prop R) && (P * Q) |-- P * (Q && coq_prop R).
Proof.
  intros.
  rewrite derivable1_sepcon_coq_prop_andp_r.
  rewrite derivable1_andp_comm.
  apply derivable1_refl.
Qed.

Lemma aux_derivable1_coq_prop_andp_sepcon_l {SAP : sepcon_andp_prop} :
  forall P Q R,
    (coq_prop P && Q) * R |-- (coq_prop P) && (Q * R).
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_sepcon_coq_prop_andp_l.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Lemma aux_derivable1_coq_prop_andp_sepcon_r {SAP : sepcon_andp_prop} :
  forall P Q R,
    (coq_prop P) && (Q * R) |-- (coq_prop P && Q) * R.
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_sepcon_coq_prop_andp_r.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Lemma aux_derivable1_andp_coq_prop_sepcon_l {SAP : sepcon_andp_prop} : 
  forall P Q R,
    (P && (coq_prop Q)) * R |-- (coq_prop Q) && (P * R).
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_andp_comm.
  rewrite derivable1_sepcon_coq_prop_andp_l.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Lemma aux_derivable1_andp_coq_prop_sepcon_r {SAP : sepcon_andp_prop} :
  forall P Q R,
  (coq_prop Q) && (P * R) |-- (P && (coq_prop Q)) * R.
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_sepcon_coq_prop_andp_r.
  rewrite derivable1_andp_comm.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Class sepcon_andp_prop_ext := {
  derivable1_sepcon_andp_coq_prop_l : forall P Q R,
    P * (Q && coq_prop R) |-- (coq_prop R) && (P * Q);
  derivable1_sepcon_andp_coq_prop_r : forall P Q R,
    (coq_prop R) && (P * Q) |-- P * (Q && coq_prop R);
  derivable1_coq_prop_andp_sepcon_l : forall P Q R,
    (coq_prop P && Q) * R |-- (coq_prop P) && (Q * R);
  derivable1_coq_prop_andp_sepcon_r : forall P Q R,
    (coq_prop P) && (Q * R) |-- (coq_prop P && Q) * R;
  derivable1_andp_coq_prop_sepcon_l : forall P Q R,
    (P && (coq_prop Q)) * R |-- (coq_prop Q) && (P * R);
  derivable1_andp_coq_prop_sepcon_r : forall P Q R,
    (coq_prop Q) && (P * R) |-- (P && (coq_prop Q)) * R;
}.

Lemma logic_equiv_sepcon_coq_prop_andp
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sap: sepcon_andp_prop}
  {sap_ext: sepcon_andp_prop_ext}:
 forall P Q R, P * (coq_prop Q && R) --||-- coq_prop Q && P * R.
Proof.
  intros; rewrite __logic_equiv_derivable1; split.
  -rewrite derivable1_sepcon_coq_prop_andp_l. rewrite derivable1_andp_coq_prop_sepcon_r. apply derivable1_sepcon_mono. apply derivable1_andp_comm. apply derivable1_refl.
  -rewrite <- derivable1_sepcon_coq_prop_andp_r. apply derivable1_coq_prop_andp_sepcon_l.
Qed.

Lemma logic_equiv_coq_prop_andp_sepcon
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sap: sepcon_andp_prop}
  {sap_ext: sepcon_andp_prop_ext}:
 forall P Q R, (coq_prop P && Q) * R --||-- coq_prop P && (Q * R).
Proof.
  intros; rewrite __logic_equiv_derivable1; split.
  -apply derivable1_coq_prop_andp_sepcon_l.
  -apply derivable1_coq_prop_andp_sepcon_r.
Qed.

Lemma logic_equiv_coq_prop_andp_sepcon_truep
  {GammaE: LogicEquiv L}
  {GammaED1: EquivDerivable1 L GammaD1 GammaE}
  {sap: sepcon_andp_prop}
  {sap_ext: sepcon_andp_prop_ext}:
  forall P Q, P * (coq_prop Q) --||-- coq_prop Q && P * TT.
Proof. 
  intros. pose proof logic_equiv_sepcon_coq_prop_andp P Q TT.
  rewrite __logic_equiv_derivable1 in *. destruct H; split.
  -eapply derivable1_trans; eauto. eapply derivable1_sepcon_mono; eauto.
  apply derivable1_refl. apply derivable1s_truep_intros.
  apply derivable1_refl. apply derivable1_truep_intros.
  -eapply derivable1_trans; eauto. eapply derivable1_sepcon_mono; eauto.
  apply derivable1_refl. apply derivable1_andp_elim1.
Qed. 

Lemma Derived_sepcon_andp_prop : sepcon_andp_prop.
Proof. 
  constructor.
  + apply aux_derivable1_sepcon_coq_prop_andp_l.
  + apply aux_derivable1_sepcon_coq_prop_andp_r.
Qed. 

Lemma Derived_sepcon_andp_prop_ext {SAP : sepcon_andp_prop} : sepcon_andp_prop_ext. 
Proof.
  constructor.
  + apply aux_derivable1_sepcon_andp_coq_prop_l.
  + apply aux_derivable1_sepcon_andp_coq_prop_r.
  + apply aux_derivable1_coq_prop_andp_sepcon_l.
  + apply aux_derivable1_coq_prop_andp_sepcon_r.
  + apply aux_derivable1_andp_coq_prop_sepcon_l.
  + apply aux_derivable1_andp_coq_prop_sepcon_r.
Qed.

Lemma derivable1_iter_sepcon_coq_prop_andp_l_ : forall xs1 P x2 xs3,
  iter_sepcon (xs1 ++ ((coq_prop P && x2) :: xs3)) |--
  (coq_prop P) && iter_sepcon (xs1 ++ (x2 ::xs3)).
Proof. 
  intros.
  rewrite itersepcon_app2.
  rewrite <- itersepcon_app1.
  rewrite itersepcon_cons1.
  assert (forall P Q R, (coq_prop P && Q) * R |-- (coq_prop P) && (Q * R)).
  { intros.
    rewrite derivable1_sepcon_comm.
    rewrite aux_derivable1_sepcon_coq_prop_andp_l.
    rewrite derivable1_sepcon_comm.
    apply derivable1_refl. }
  rewrite H.
  rewrite aux_derivable1_sepcon_coq_prop_andp_l.
  rewrite <- itersepcon_cons2.
  apply derivable1_refl.
Qed.

Class Iter_sepcon_andp_prop := {
  derivable1_iter_sepcon_coq_prop_andp_l : forall xs1 P x2 xs3,
  iter_sepcon (xs1 ++ ((coq_prop P && x2) :: xs3)) |--
  (coq_prop P) && iter_sepcon (xs1 ++ (x2 ::xs3))
}.

Lemma Derived_derivable1_iter_sepcon_coq_prop_andp_l :
  Iter_sepcon_andp_prop.
Proof.
  intros. 
  constructor.
  apply derivable1_iter_sepcon_coq_prop_andp_l_.
Qed.

End IterSepconDerivedRules.


