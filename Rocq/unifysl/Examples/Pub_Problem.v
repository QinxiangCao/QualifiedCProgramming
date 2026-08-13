Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.


Module ModalLogic_Pub.

Inductive L_Pub : Type :=
  |atomp : nat -> L_Pub
  |falsep : L_Pub
  |impp : L_Pub -> L_Pub -> L_Pub
  |boxa : L_Pub -> L_Pub
  |boxb : L_Pub -> L_Pub
  |boxc : L_Pub -> L_Pub
  |A0 : L_Pub
  |B0 : L_Pub
  |C0 : L_Pub.

Definition negp (l : L_Pub) :=
  impp l falsep.
Definition orp (l1 l2 : L_Pub) :=
  impp (negp l1) l2.
Definition andp (l1 l2 : L_Pub) :=
  negp (orp (negp l1) (negp l2)).
Definition iffp (l1 l2 : L_Pub) :=
  andp (impp l1 l2)(impp l2 l1).
Definition truep := negp falsep.
Definition diamonda (l : L_Pub) :=
  negp (boxa (negp l)).
Definition diamondb (l : L_Pub) :=
  negp (boxb (negp l)).
Definition diamondc (l : L_Pub) :=
  negp (boxc (negp l)).

Notation "~~ x" := (negp x) (at level 35).
Notation "x --> y" := (impp x y)(at level 55, right associativity).
Notation "x || y" := (orp x y)(at level 50, left associativity).
Notation "x && y" := (andp x y)(at level 40, left associativity).
Notation "x <--> y" := (iffp x y) (at level 60, no associativity).
Reserved Notation "|-- P " (at level 71, no associativity).

Inductive T_Pub : L_Pub -> Prop:=
  | A_P1: forall p q, |-- (p --> (q --> p))
  | A_P2: forall p q r, |-- ((p --> q --> r) --> (p --> q) --> (p --> r))
  | A_P3: forall p q, |-- (~~p --> q) --> ((~~p --> ~~q) --> p)
  (*代入规则在Coq中总是被承认的*)
  | MP: forall a b, |-- (a --> b) -> |--a -> |-- b

  | K_AXIOM_A: forall p q, |-- boxa (p --> q) --> (boxa p --> boxa q)
  | T_AXIOM_A: forall p, |-- (boxa p) --> p
  | N_RULE_A: forall a, |-- a -> |-- boxa a
  | PUB_ASSERT_A: |-- boxa A0 || boxa (~~A0)

  | K_AXIOM_B: forall p q, |-- boxb (p --> q) --> (boxb p --> boxb q)
  | T_AXIOM_B: forall p, |-- (boxb p) --> p
  | N_RULE_B: forall a, |-- a -> |-- boxb a
  | PUB_ASSERT_B: |-- boxb B0 || boxb (~~B0)

  | K_AXIOM_C: forall p q, |-- boxc (p --> q) --> (boxc p --> boxc q)
  | T_AXIOM_C: forall p, |-- (boxc p) --> p
  | N_RULE_C: forall a, |-- a -> |-- boxc a
  | PUB_ASSERT_C: |-- boxc C0 || boxc (~~C0)
where "|-- P" := (T_Pub P).
(* in this Module, we always try to use a/b/c... when talking 
abort rule, and use p/q/r... when talking abort axiom or lemma*)

Instance MLPubL: Language := {|
  expr := ModalLogic_Pub.L_Pub
|}.

Instance MLPubminL: MinimumLanguage MLPubL := {|
  Logic.MinimumLogic.Syntax.impp := ModalLogic_Pub.impp
|}.

Instance MLPubpL: PropositionalLanguage MLPubL := {|
  Logic.PropositionalLogic.Syntax.andp := ModalLogic_Pub.andp;
  Logic.PropositionalLogic.Syntax.orp := ModalLogic_Pub.orp;
  Logic.PropositionalLogic.Syntax.falsep := ModalLogic_Pub.falsep
|}.

Instance MLPubGamma: Provable MLPubL := {|
  provable := ModalLogic_Pub.T_Pub
|}.

Instance MLPubminAX: MinimumAxiomatization MLPubL MLPubGamma.
Proof.
  constructor.
  + apply ModalLogic_Pub.MP.
  + apply ModalLogic_Pub.A_P1.
  + apply ModalLogic_Pub.A_P2.
Qed.

Instance T_Pub_impp_rewrite: RewriteRelation (fun x y => |-- x --> y).
Qed.
Instance T_Pub_impp_refl : Reflexive (fun x y => |-- impp x y).
Proof.
  pose proof provable_impp_refl_instance.
  apply H.
Qed.
Instance T_Pub_proper_impp : Proper ((fun x y => |-- impp x y) ==> Basics.impl) T_Pub.
Proof.
  pose proof provable_proper_impp.
  apply H.
Qed.
Instance provables_impp_proper_impp : Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) impp.
Proof.
  pose proof provables_impp_proper_impp.
  apply H.
Qed.


Lemma RG : forall a b, |-- a -> |-- b --> a.
Proof.
  intros.
  pose proof A_P1 a b.
  pose proof MP _ _ H0 H.
  apply H1. Qed.

Lemma impp_refl: forall (p: L_Pub), |-- p --> p.
Proof.
  intros.
  pose proof provable_impp_refl p.
  apply H.
  Qed.

Lemma impp_substitute: forall p q, |-- p --> (p --> q) --> q.
Proof.
  intros.
  pose proof aux_minimun_theorem02 p q.
  apply H. Qed.

Lemma impp_trans: forall (p q r: L_Pub), |--  (q --> r) --> (p --> q) --> (p --> r).
Proof.
  intros.
  pose proof aux_minimun_theorem00 p q r.
  apply H. Qed.

Lemma RS_pre: forall (a b c: L_Pub), |-- (b --> c) -> |-- (a --> b) --> (a --> c).
Proof.
  intros a b c.
  pose proof aux_minimun_rule01 b c a.
  apply H. Qed.

Lemma RS: forall (a b c: L_Pub), |-- (b --> c) -> |-- (a --> b) -> |--(a --> c).
Proof.
  intros.
  pose proof RS_pre a b c H.
  pose proof MP _ _ H1 H0.
  apply H2. Qed.

Lemma impp_trans_infer1: forall p q r s, |-- (r --> s) --> (p --> q --> r) --> (p --> q --> s).
Proof.
  intros.
  pose proof impp_trans q r s.
  pose proof impp_trans p (q --> r) (q --> s).
  pose proof RS _ _ _ H0 H.
  apply H1. Qed.

Lemma RS_infer1: forall a b c d, |-- c --> d -> |-- a --> b --> c -> |-- a --> b --> d.
Proof.
  intros.
  pose proof impp_trans_infer1 a b c d.
  pose proof MP _ _ H1 H.
  pose proof MP _ _ H2 H0.
  apply H3. Qed.


Lemma impp_switch: forall p q r, |-- (p --> (q --> r)) --> (q --> (p --> r)).
Proof.
  intros.
  pose proof provable_impp_arg_switch p q r.
  apply H. Qed.

Lemma RIS: forall a b c, |-- a --> b --> c -> |-- b --> a --> c.
Proof.
  intros.
  pose proof impp_switch a b c.
  pose proof MP _ _ H0 H.
  apply H1. Qed.

Lemma RIS_infer1: forall a b c d, |-- a --> b --> c --> d -> |-- c --> a --> b --> d.
Proof.
  intros.
  pose proof impp_switch b c d.
  pose proof impp_switch a c (b --> d).
  rewrite H0 in H.
  pose proof MP _ _ H1 H.
  apply H2. Qed.

Lemma negp_double1: forall p, |-- ~~(~~p) --> p.
Proof.
  intros.
  pose proof A_P3 p (~~p).
  pose proof impp_refl (~~p).
  pose proof MP _ _ H H0.
  pose proof A_P1 (~~(~~p)) (~~p).
  pose proof RS _ _ _ H1 H2.
  apply H3. Qed.

Lemma negp_double2: forall p, |-- p --> ~~(~~p).
Proof.
  intros.
  unfold negp.
  pose proof impp_substitute p falsep.
  apply H. Qed.

Lemma impp_comm1: forall p q, |--(~~p --> q) --> (~~q --> p).
Proof.
  intros.
  pose proof A_P1 (~~q) (~~p).
  pose proof A_P3 p (~~q).
  pose proof RS _ _ _ H0 H.
  pose proof RIS _ _ _ H1.
  pose proof negp_double2 q.
  rewrite -> H3 at 1.
  apply H2. Qed.

Lemma impp_comm2: forall p q, |--(p --> ~~q) --> (q --> ~~p).
Proof.
  intros.
  pose proof impp_comm1 (~~p) (~~q).
  pose proof negp_double1 p.
  pose proof negp_double2 q.
  rewrite <- H0 at 1.
  rewrite -> H1 at 2.
  apply H. Qed.

Lemma impp_comm3: forall p q, |--(p --> q) --> (~~q --> ~~p).
Proof.
  intros.
  pose proof impp_comm2 p (~~q).
  pose proof negp_double2 q.
  rewrite H0 at 1.
  apply H. Qed.

Lemma impp_reduc: forall p q, |-- (p --> q) --> (~~p --> q) --> q.
Proof.
  intros.
  pose proof A_P3 q (~~p).
  pose proof impp_comm3 p q.
  rewrite H0.
  pose proof impp_comm1 p q.
  rewrite H1.
  pose proof negp_double2 p.
  rewrite H2 at 2.
  apply H. Qed.

Lemma DS: forall a b, |-- a --> a --> b -> |-- a --> b.
Proof.
  intros.
  pose proof aux_minimun_theorem04 a b.
  pose proof MP _ _ H0 H.
  apply H1. Qed.

Lemma provable_orp_intros1 : forall p q, |-- p --> (p || q).
Proof.
  unfold orp.
  intros.
  pose proof A_P1 p (~~q).
  pose proof impp_comm1 q p.
  pose proof RS _ _ _ H0 H.
  apply H1. Qed.

Lemma provable_orp_intros2 : forall p q, |-- q --> (p || q).
Proof.
  unfold orp.
  intros.
  pose proof A_P1 q (~~p).
  apply H. Qed.

Lemma provable_orp_elim : forall p q r, |-- (p --> r) --> (q --> r) --> ((p || q) --> r).
Proof.
  unfold orp.
  intros.
  pose proof impp_trans (~~p) q r.
  pose proof impp_reduc p r.
  pose proof RIS _ _ _ H0.
  pose proof RS_infer1 _ _ _ _ H1 H.
  pose proof RIS_infer1 _ _ _ _ H2.
  apply H3. Qed.

Lemma provable_andp_intros : forall p q, |-- p --> (q --> (p && q)).
Proof.
  unfold andp.
  unfold orp.
  intros.
  pose proof impp_substitute p (~~q).
  pose proof impp_comm2 (p --> ~~ q) q.
  pose proof RS _ _ _ H0 H.
  pose proof impp_comm2 q (p --> ~~ q).
  rewrite H2 in H1.
  pose proof negp_double2 p.
  rewrite H3 in H1 at 2.
  pose proof impp_comm2 (~~ (~~ p) --> ~~ q) q.
  rewrite H4 in H1.
  apply H1. Qed.

Lemma provable_andp_elim1 : forall p q,  |-- (p && q) --> p.
Proof.
  unfold andp.
  unfold orp.
  intros.
  pose proof impp_comm1 p (~~ (~~ p) --> ~~ q).
  pose proof provable_orp_intros1 (~~p) (~~q). unfold orp in H0.
  pose proof MP _ _ H H0.
  apply H1. Qed.

Lemma provable_andp_elim2 : forall p q, |-- (p && q) --> q.
Proof.
  unfold andp.
  unfold orp.
  intros.
  pose proof A_P1 (~~q) (~~ (~~ p)).
  pose proof impp_comm1 q (~~ (~~ p) --> ~~ q).
  pose proof MP _ _ H0 H.
  apply H1. Qed.

Lemma provable_falsep_elim : forall p, |-- (falsep --> p).
Proof.
  intros.
  pose proof A_P3 p falsep.
  unfold negp in H.
  pose proof impp_refl falsep.
  pose proof RG _ (p --> falsep) H0.
  pose proof RG _ falsep H1.
  pose proof RIS _ _ _ H1.
  rewrite <- H3 in H.
  rewrite <- H2 in H.
  pose proof DS _ _ H.
  apply H4. Qed.

Instance MLPubipGamma: IntuitionisticPropositionalLogic MLPubL MLPubGamma.
Proof.
  constructor.
  + apply ModalLogic_Pub.provable_andp_intros.
  + apply ModalLogic_Pub.provable_andp_elim1.
  + apply ModalLogic_Pub.provable_andp_elim2.
  + apply ModalLogic_Pub.provable_orp_intros1.
  + apply ModalLogic_Pub.provable_orp_intros2.
  + apply ModalLogic_Pub.provable_orp_elim.
  + apply ModalLogic_Pub.provable_falsep_elim.
Qed.

Lemma provable_excluded_middle : forall p, |-- p || ~~ p.
Proof.
  intros.
  unfold orp.
  pose proof impp_refl (~~p).
  apply H. Qed.

Instance MLPubcpGamma: ClassicalPropositionalLogic MLPubL MLPubGamma.
Proof.
  constructor.
  + apply ModalLogic_Pub.excluded_middle.
Qed.

Lemma provable_weak_excluded_middle: forall p, |-- ~~ p || ~~ ~~p.
Proof.
  intros.
  pose proof provable_excluded_middle (~~p).
  apply H.
Qed.

Instance MLPubdmpGamma: DeMorganPropositionalLogic MLPubL MLPubGamma.
Proof.
  constructor.
  + apply ModalLogic_Pub.provable_weak_excluded_middle.
Qed.

Instance T_Pub_iffp_rewrite: RewriteRelation (fun x y => |-- x <--> y).
Qed.
Instance T_Pub_iffp_equiv: Equivalence (fun x y => |-- x <--> y).
Proof.
  pose proof provable_iffp_equiv.
  apply H.
Qed.
Instance T_Pub_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> iff) T_Pub.
Proof.
  pose proof provable_proper_iffp.
  apply H.
Qed.
Instance provables_impp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) impp.
Proof.
  pose proof provables_impp_proper_iffp.
  apply H.
Qed.
Instance provables_andp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) andp.
Proof.
  pose proof provables_andp_proper_impp.
  apply H.
Qed.
Instance provables_orp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) orp.
Proof.
  pose proof provables_orp_proper_impp.
  apply H.
Qed.
Instance provables_negp_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y)) negp.
Proof.
  pose proof provables_negp_proper_impp.
  apply H.
Qed.
Instance provables_andp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) andp.
Proof.
  pose proof provables_andp_proper_iffp.
  apply H.
Qed.
Instance provables_orp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) orp.
Proof.
  pose proof provables_orp_proper_iffp.
  apply H.
Qed.
Instance provables_iffp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) iffp.
Proof.
  pose proof provables_iffp_proper_iffp.
  apply H.
Qed.
Instance provables_negp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) negp.
Proof.
  pose proof provables_negp_proper_iffp.
  apply H.
Qed.


Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class PubBaseLanguage (L: Language): Type := {
  boxp : expr -> expr;
  P0 : expr
}.

Definition diamondp {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {pbL: PubBaseLanguage L} (p : expr): expr :=
  Syntax.negp (boxp (Syntax.negp p)).

Class PubBaseAxiomatization (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {pbL: PubBaseLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} := {
  K_AXIOM: forall p q, |-- boxp (p --> q) --> (boxp p --> boxp q);
  T_AXIOM: forall p, |-- (boxp p) --> p;
  N_RULE: forall a, |-- a -> |-- boxp a;
  PUB_ASSERT: |-- boxp P0 || boxp (~~P0)
}.

Section RewriteClass_Pub.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {pbL: PubBaseLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {dmpAX: DeMorganPropositionalLogic L Gamma}
        {pbAX: PubBaseAxiomatization L Gamma}.

Instance boxp_proper_impp : Proper ((fun x y => |-- Syntax.impp x y) ==> (fun x y => |-- Syntax.impp x y)) boxp.
Proof.
  hnf; intros x1 x2 ?.
  apply N_RULE in H.
  pose proof K_AXIOM x1 x2.
  pose proof provables_modus_ponens _ _ H0 H.
  apply H1. Qed.

Instance boxp_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) boxp.
Proof.
  hnf; intros x1 x2 ?.
  unfold iffp in H.
  pose proof Intuitionistic.provable_andp_elim1 (x1 --> x2) (x2 --> x1).
  pose proof provables_modus_ponens _ _ H0 H.
  pose proof Intuitionistic.provable_andp_elim2 (x1 --> x2) (x2 --> x1).
  pose proof provables_modus_ponens _ _ H2 H.
  pose proof boxp_proper_impp x1 x2. hnf in H4.
  pose proof boxp_proper_impp x2 x1. hnf in H5.
  apply H4 in H1.
  apply H5 in H3.
  pose proof Intuitionistic.provable_andp_intros (boxp x1 --> boxp x2) (boxp x2 --> boxp x1).
  pose proof provables_modus_ponens _ _ H6 H1.
  pose proof provables_modus_ponens _ _ H7 H3.
  unfold iffp.
  apply H8. Qed.

End RewriteClass_Pub.

Existing Instances boxp_proper_impp boxp_proper_iffp.

Section LemmaFromPubBaseAxiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {pbL: PubBaseLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {dmpAX: DeMorganPropositionalLogic L Gamma}
        {pbAX: PubBaseAxiomatization L Gamma}.

Lemma boxp_impp_refl: forall (p: expr), |-- (boxp (p --> p)).
Proof.
  intros.
  pose proof provable_impp_refl p as H1.
  pose proof N_RULE _ H1.
  apply H.
  Qed.

Lemma RK: forall (p q: expr), |-- p --> q -> |-- boxp p --> boxp q.
Proof.
  intros.
  pose proof N_RULE _ H.
  pose proof K_AXIOM p q.
  rewrite H1 in H0.
  apply H0. Qed.

Lemma T_AXIOM_infer1: forall (p: expr), |-- ~~p --> ~~ (boxp p).
Proof.
  intros.
  pose proof T_AXIOM p.
  pose proof provable_contrapositivePP p (boxp p).
  pose proof provables_modus_ponens _ _ H0 H.
  apply H1. Qed.

Lemma falsep_truthp_intros: forall (p q: expr), |-- (~~p) --> q --> ~~(p && q).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_elim1 p q.
  pose proof provable_contrapositivePP p (p && q).
  rewrite H0 in H.
  pose proof aux_minimun_rule00 _ q H.
  pose proof provable_impp_arg_switch q (~~p) (~~ (p && q)).
  rewrite H2 in H1.
  apply H1. Qed.

Lemma provable_negp_orp_infer1: forall (p q: expr), |-- (p || q) --> (~~p --> q).
Proof.
  intros.
  pose proof provable_negp_orp (~~p) q.
  pose proof provable_double_negp p.
  rewrite H0 in H.
  rewrite H.
  pose proof provable_impp_refl (p || q).
  apply H1. Qed.

Lemma P_impp_boxp1: |-- P0 --> boxp P0.
Proof.
  pose proof PUB_ASSERT.
  pose proof provable_negp_orp_infer1 (boxp P0) (boxp (~~P0)).
  rewrite H0 in H.
  pose proof T_AXIOM (~~P0).
  rewrite H1 in H.
  pose proof provable_contrapositiveNP (~~P0) (boxp P0).
  rewrite H2 in H.
  pose proof provable_provable_double_negp_intros P0.
  rewrite <- H3 in H.
  apply H. Qed.

Lemma boxp_andp_elim: forall (p q: expr), |-- boxp(p && q) --> (boxp p && boxp q).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_elim1 p q.
  pose proof Intuitionistic.provable_andp_elim2 p q.
  pose proof RK _ _ H.
  pose proof RK _ _ H0.
  pose proof provables_impp_andp_fold _ _ _ H1 H2.
  apply H3. Qed.

Lemma boxp_andp_intros: forall (p q: expr), |-- (boxp p && boxp q) --> boxp(p && q).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_intros p q.
  pose proof RK _ _ H.
  pose proof K_AXIOM q (p && q).
  rewrite -> H1 in H0.
  pose proof Intuitionistic.provable_andp_impp (boxp p) (boxp q) (boxp (p && q)).
  rewrite H2 in H0.
  apply H0. Qed.

Lemma boxp_orp_intros: forall (p q: expr), |-- (boxp p || boxp q) --> boxp(p || q).
Proof.
  intros.
  pose proof Intuitionistic.provable_orp_intros1 p q.
  pose proof RK _ _ H.
  pose proof Intuitionistic.provable_orp_intros2 p q.
  pose proof RK _ _ H1.
  pose proof provables_orp_impp_fold _ _ _ H0 H2.
  apply H3. Qed.

Lemma diamondp_boxp_intros: forall (p q: expr), |-- diamondp q --> boxp p --> diamondp (p && q).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_intros p q.
  pose proof provable_contrapositivePP (p&&q) q.
  rewrite H0 in H.
  pose proof RK _ _ H.
  pose proof K_AXIOM (~~ (p && q)) (~~q).
  rewrite H2 in H1.
  pose proof provable_contrapositivePP (boxp (~~ q)) (boxp (~~ (p && q))).
  rewrite H3 in H1.
  pose proof provable_impp_arg_switch (boxp p) (~~ boxp (~~ q)) (~~ boxp (~~ (p && q))).
  rewrite H4 in H1.
  unfold diamondp.
  apply H1. Qed.

Lemma basic_situation1: forall (A B: expr), |-- ((diamondp B) && (diamondp (~~B))) --> boxp A --> (~~boxp (A&&B)).
Proof.
  intros.
  pose proof falsep_truthp_intros (boxp B) (boxp A).
  pose proof boxp_andp_elim B A.
  rewrite <- H0 in H.
  pose proof aux_minimun_rule00 _ (~~ boxp (~~B)) H.
  pose proof provable_impp_curry (~~ boxp (~~ B)) (~~ boxp B) (boxp A --> ~~ boxp (B && A)).
  rewrite H2 in H1.
  pose proof provable_andp_comm A B.
  rewrite <- H3 in H1.
  unfold diamondp.
  pose proof provable_double_negp B.
  rewrite <- H4 in H1 at 2.
  apply H1. Qed.

Lemma basic_situation2: forall (A B: expr), |-- ((diamondp B) && (diamondp (~~B))) --> boxp A --> (~~boxp (~~(A&&B))).
Proof.
  intros.
  pose proof diamondp_boxp_intros A B.
  rewrite <- H.
  pose proof Intuitionistic.provable_andp_elim1 (diamondp B) (diamondp (~~B)).
  apply H0. Qed.

Lemma andp_impp_orp: forall (p q: expr), |-- (p && q) --> (p || q).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_elim1 p q.
  pose proof Intuitionistic.provable_orp_intros1 p q.
  rewrite H0 in H at 2.
  apply H. Qed.

Lemma diamondp_negp_elim: forall (p q: expr), |-- diamondp (p && ~~q) && diamondp (~~p && q) && diamondp (~~p && ~~q) --> diamondp(~~(p && q)).
Proof.
  intros.
  unfold diamondp.
  pose proof andp_impp_orp p q.
  pose proof RK _ _ H.
  pose proof demorgan_negp_andp (~~p) (~~q).
  pose proof provable_double_negp p.
  rewrite -> H2 in H1.
  pose proof provable_double_negp q.
  rewrite -> H3 in H1.
  rewrite <- H1 in H0.
  pose proof provable_double_negp (p && q).
  rewrite <- H4 in H0.
  rewrite <- H0.
  pose proof Minimum.provable_impp_refl (~~ boxp (~~ (~~ (p && q)))).
  pose proof aux_minimun_rule00 _ (~~ boxp (~~ (p && ~~ q)) && ~~ boxp (~~ (~~ p && q))) H5.
  pose proof provable_impp_curry (~~ boxp (~~ (p && ~~ q)) && ~~ boxp (~~ (~~ p && q))) (~~ boxp (~~ (~~ (p && q)))) (~~ boxp (~~ (~~ (p && q)))).
  rewrite -> H7 in H6.
  apply H6. Qed.

Lemma diamondp_negp_elim_infer1: forall (p q: expr), |-- diamondp (p && q) && diamondp (p && ~~q) && diamondp (~~p && q) && diamondp (~~p && ~~q) --> diamondp (p && q) && diamondp(~~(p && q)).
Proof.
  intros.
  pose proof provable_andp_assoc (diamondp (p && q) && diamondp (p && ~~ q)) (diamondp (~~ p && q)) (diamondp (~~ p && ~~ q)).
  rewrite -> H.
  pose proof provable_andp_assoc (diamondp (p && q)) (diamondp (p && ~~ q)) (diamondp (~~ p && q) && diamondp (~~ p && ~~ q)).
  rewrite -> H0.
  pose proof provable_andp_assoc (diamondp (p && ~~ q)) (diamondp (~~ p && q)) (diamondp (~~ p && ~~ q)).
  rewrite <- H1.
  pose proof diamondp_negp_elim p q.
  rewrite -> H2.
  pose proof Minimum.provable_impp_refl (diamondp (p && q) && diamondp (~~ (p && q))).
  apply H3. Qed.

Lemma provable_andp_intros_infer1: forall (A B C: expr), |-- ~~A --> ~~(A&&B&&C).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_elim1 A (B&&C).
  pose proof provable_contrapositivePP A (A && (B && C)).
  pose proof provables_modus_ponens _ _ H0 H.
  pose proof provable_andp_assoc A B C.
  rewrite H2.
  apply H1. Qed.

Lemma P_impp_boxp2: |-- ~~P0 --> boxp (~~P0).
Proof.
  pose proof PUB_ASSERT.
  pose proof provable_orp_comm (boxp P0) (boxp (~~ P0)).
  rewrite H0 in H.
  pose proof provable_negp_orp_infer1 (boxp (~~ P0)) (boxp P0).
  rewrite H1 in H.
  pose proof T_AXIOM P0.
  rewrite H2 in H.
  pose proof provable_contrapositiveNP P0 (boxp (~~ P0)).
  rewrite H3 in H.
  apply H. Qed.

Lemma boxp_orp_intros_infer1: forall (p q: expr), |-- boxp p --> boxp (p || ~~q).
Proof.
  intros.
  pose proof boxp_orp_intros p (~~q).
  pose proof Intuitionistic.provable_orp_intros1 (boxp p) (boxp (~~q)).
  rewrite <- H0 in H.
  apply H. Qed.

Lemma diamondp_andp_minus: forall (p q: expr), |-- (diamondp (p && q) && diamondp (p && ~~q) && diamondp (~~p && q) && diamondp (~~p && ~~q)) --> boxp p --> diamondp q && diamondp (~~ q).
Proof.
  intros.
  unfold diamondp.
  pose proof boxp_orp_intros_infer1 p q.
  pose proof aux_minimun_rule00 _ (~~ (~~ boxp (~~ q) && ~~ boxp (~~ (~~ q)))) H.
  pose proof provable_impp_arg_switch (~~ (~~ boxp (~~ q) && ~~ boxp (~~ (~~ q)))) (boxp p) (boxp (p || ~~ q)).
  rewrite -> H1 in H0.
  pose proof provable_contrapositiveNP (boxp (p || ~~ q)) (~~ boxp (~~ q) && ~~ boxp (~~ (~~ q))).
  rewrite -> H2 in H0.
  pose proof provable_impp_arg_switch (boxp p) (~~ boxp (p || ~~ q)) (~~ boxp (~~ q) && ~~ boxp (~~ (~~ q))).
  rewrite -> H3 in H0.
  pose proof demorgan_negp_andp (~~p) q.
  pose proof provable_double_negp p.
  rewrite -> H5 in H4.
  rewrite <- H4 in H0.
  pose proof Intuitionistic.provable_andp_elim1 (~~ boxp (~~ (~~ p && q))) (~~ boxp (~~ (~~ p && ~~ q))).
  rewrite <- H6 in H0.
  pose proof aux_minimun_rule00 _ (~~ boxp (~~ (p && q)) && ~~ boxp (~~ (p && ~~ q))) H0.
  pose proof provable_impp_curry (~~ boxp (~~ (p && q)) && ~~ boxp (~~ (p && ~~ q))) (~~ boxp (~~ (~~ p && q)) && ~~ boxp (~~ (~~ p && ~~ q))) (boxp p --> ~~ boxp (~~ q) && ~~ boxp (~~ (~~ q))).
  rewrite -> H8 in H7.
  pose proof provable_andp_assoc (~~ boxp (~~ (p && q)) && ~~ boxp (~~ (p && ~~ q))) (~~ boxp (~~ (~~ p && q))) (~~ boxp (~~ (~~ p && ~~ q))).
  rewrite <- H9 in H7.
  apply H7. Qed.

Lemma provable_andp_dup_infer1: forall (p q r: expr), |-- (p&&q&&r) --> (p&&q&&q&&r).
Proof.
  intros.
  pose proof provable_andp_dup q.
  rewrite <- H at 1.
  pose proof provable_andp_assoc p q q.
  rewrite <- H0.
  pose proof Minimum.provable_impp_refl (p && q && q && r).
  apply H1. Qed.

Lemma provable_andp_assoc_infer1: forall (p q r s: expr), |-- (p&&q) --> (q&&r) --> s -> |-- (p --> q --> r --> s).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_impp p q (r-->s).
  pose proof Intuitionistic.provable_andp_impp (p && q) r s.
  rewrite -> H1 in H0.
  rewrite H0.
  pose proof provable_andp_dup_infer1 p q r.
  rewrite -> H2.
  pose proof Intuitionistic.provable_andp_impp (p && q) (q && r) s.
  pose proof provable_andp_assoc (p&&q) q r.
  rewrite -> H4.
  rewrite <- H3.
  apply H. Qed.

Lemma provable_andp_intros_infer2: forall (A B C: expr), |-- A --> B --> C --> (A&&B&&C).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_intros (A&&B) C.
  rewrite <- H.
  pose proof Intuitionistic.provable_andp_intros A B.
  apply H0. Qed.

Lemma boxp_one_unknown1: forall (B C: expr), |--(diamondp (B && C) && diamondp (B && ~~C) && diamondp (~~B && C) && diamondp (~~B && ~~C)) --> P0 --> (~~boxp (P0&&B&&C)).
Proof.
  intros.
  pose proof basic_situation1 P0 (B&&C).
  pose proof P_impp_boxp1.
  rewrite <- H0 in H.
  pose proof diamondp_negp_elim_infer1 B C.
  rewrite <- H1 in H.
  pose proof provable_andp_assoc P0 B C.
  rewrite <- H2 in H.
  apply H. Qed.

Lemma boxp_one_unknown2: forall (B C: expr), |-- (diamondp (B && C) && diamondp (B && ~~C) && diamondp (~~B && C) && diamondp (~~B && ~~C)) --> P0 --> (~~boxp (~~(P0&&B&&C))).
Proof.
  intros.
  pose proof basic_situation2 P0 (B&&C).
  pose proof P_impp_boxp1.
  rewrite <- H0 in H.
  pose proof diamondp_negp_elim_infer1 B C.
  rewrite <- H1 in H.
  pose proof provable_andp_assoc P0 B C.
  rewrite <- H2 in H.
  apply H. Qed.

Lemma boxp_from_unknown1: forall (B C: expr), |-- (~~ boxp (P0&&B&&C) && ~~ boxp (~~(P0&&B&&C))) --> P0.
Proof.
  intros.
  pose proof provable_andp_intros_infer1 P0 B C.
  pose proof N_RULE _ H.
  pose proof K_AXIOM (~~ P0) (~~ (P0 && B && C)).
  pose proof provables_modus_ponens _ _ H1 H0.
  pose proof P_impp_boxp2.
  rewrite <- H3 in H2.
  pose proof provable_contrapositiveNP (boxp (~~ (P0 && B && C))) P0.
  pose proof provables_modus_ponens _ _ H4 H2.
  pose proof aux_minimun_rule00 _ (~~ boxp (P0 && B && C)) H5.
  pose proof provable_impp_curry (~~ boxp (P0 && B && C)) (~~ boxp (~~(P0 && B && C))) P0.
  pose proof provables_modus_ponens _ _ H7 H6.
  apply H8. Qed.

Lemma boxp_from_unknown2: forall (A C: expr), |-- (~~ boxp (A&&P0&&C) && ~~ boxp (~~(A&&P0&&C))) --> P0.
Proof.
  intros.
  pose proof boxp_from_unknown1 A C.
  pose proof provable_andp_comm A P0.
  rewrite H0.
  apply H. Qed.

Lemma boxp_two_unknown1: forall (A C: expr), |-- (diamondp (A && C) && diamondp (A && ~~C) && diamondp (~~A && C) && diamondp (~~A && ~~C)) --> boxp A --> P0 --> (~~boxp (A&&P0&&C)).
Proof.
  intros.
  pose proof basic_situation1 (A&&P0) C.
  pose proof boxp_andp_intros A P0.
  pose proof P_impp_boxp1.
  rewrite <- H1 in H0.
  rewrite <- H0 in H.
  pose proof diamondp_andp_minus A C.
  pose proof provable_impp_curry (diamondp (A && C) && diamondp (A && ~~ C) && diamondp (~~ A && C) && diamondp (~~ A && ~~ C)) (boxp A) (diamondp C && diamondp (~~ C)).
  rewrite -> H3 in H2.
  rewrite <- H2 in H.
  pose proof provable_andp_assoc_infer1 _ _ _ _ H.
  apply H4. Qed.

Lemma boxp_two_unknown2: forall (A C: expr), |-- (diamondp (A && C) && diamondp (A && ~~C) && diamondp (~~A && C) && diamondp (~~A && ~~C)) --> boxp A --> P0 --> (~~boxp (~~(A&&P0&&C))).
Proof.
  intros.
  pose proof basic_situation2 (A&&P0) C.
  pose proof boxp_andp_intros A P0.
  pose proof P_impp_boxp1.
  rewrite <- H1 in H0.
  rewrite <- H0 in H.
  pose proof diamondp_andp_minus A C.
  pose proof provable_impp_curry (diamondp (A && C) && diamondp (A && ~~ C) && diamondp (~~ A && C) && diamondp (~~ A && ~~ C)) (boxp A) (diamondp C && diamondp (~~ C)).
  rewrite -> H3 in H2.
  rewrite <- H2 in H.
  pose proof provable_andp_assoc_infer1 _ _ _ _ H.
  apply H4. Qed.

Lemma boxp_from_hear: forall (p q: expr), |-- boxp p --> boxp (p --> q) --> boxp q.
Proof.
  intros.
  pose proof aux_minimun_theorem02 p q.
  pose proof RK _ _ H.
  pose proof K_AXIOM (p --> q) q.
  rewrite -> H1 in H0.
  apply H0. Qed.

Lemma boxp_three_know: forall (A B: expr), |-- boxp A --> boxp B --> P0 --> boxp (A&&B&&P0).
Proof.
  intros.
  pose proof provable_andp_intros_infer2 A B P0.
  pose proof N_RULE _ H.
  pose proof K_AXIOM A (B --> P0 --> A && B && P0).
  rewrite H1 in H0.
  pose proof K_AXIOM B (P0 --> A && B && P0).
  rewrite H2 in H0.
  pose proof K_AXIOM P0 (A && B && P0).
  rewrite H3 in H0.
  pose proof P_impp_boxp1.
  rewrite <- H4 in H0.
  apply H0. Qed.

End LemmaFromPubBaseAxiomatization.


Instance MLPubpbL_a: PubBaseLanguage MLPubL := {|
  boxp := ModalLogic_Pub.boxa;
  P0 := ModalLogic_Pub.A0
|}.

Instance MLPubpbAX_a: @PubBaseAxiomatization MLPubL _ _ MLPubpbL_a MLPubGamma _ _ _.
Proof.
  constructor.
  + apply ModalLogic_Pub.K_AXIOM_A.
  + apply ModalLogic_Pub.T_AXIOM_A.
  + apply ModalLogic_Pub.N_RULE_A.
  + apply ModalLogic_Pub.PUB_ASSERT_A.
Qed.

Instance boxa_proper_impp : Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) boxa.
Proof.
  pose proof boxp_proper_impp.
  apply H.
Qed.

Instance boxa_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) boxa.
Proof.
  pose proof boxp_proper_iffp.
  apply H.
Qed.







Instance MLPubpbL_b: PubBaseLanguage MLPubL := {|
  boxp := ModalLogic_Pub.boxb;
  P0 := ModalLogic_Pub.B0
|}.

Instance MLPubpbAX_b: @PubBaseAxiomatization MLPubL _ _ MLPubpbL_b MLPubGamma _ _ _.
Proof.
  constructor.
  + apply ModalLogic_Pub.K_AXIOM_B.
  + apply ModalLogic_Pub.T_AXIOM_B.
  + apply ModalLogic_Pub.N_RULE_B.
  + apply ModalLogic_Pub.PUB_ASSERT_B.
Qed.

Instance boxb_proper_impp : Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) boxb.
Proof.
  pose proof boxp_proper_impp.
  apply H.
Qed.

Instance boxb_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) boxb.
Proof.
  pose proof boxp_proper_iffp.
  apply H.
Qed.









Instance MLPubpbL_c: PubBaseLanguage MLPubL := {|
  boxp := ModalLogic_Pub.boxc;
  P0 := ModalLogic_Pub.C0
|}.

Instance MLPubpbAX_c: @PubBaseAxiomatization MLPubL _ _ MLPubpbL_c MLPubGamma _ _ _.
Proof.
  constructor.
  + apply ModalLogic_Pub.K_AXIOM_C.
  + apply ModalLogic_Pub.T_AXIOM_C.
  + apply ModalLogic_Pub.N_RULE_C.
  + apply ModalLogic_Pub.PUB_ASSERT_C.
Qed.

Instance boxc_proper_impp : Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) boxc.
Proof.
  pose proof boxp_proper_impp.
  apply H.
Qed.

Instance boxc_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) boxc.
Proof.
  pose proof boxp_proper_iffp.
  apply H.
Qed.





Lemma boxa_one_unknown1: |--(diamonda (B0 && C0) && diamonda (B0 && ~~C0) && diamonda (~~B0 && C0) && diamonda (~~B0 && ~~C0)) --> A0 --> (~~boxa (A0&&B0&&C0)).
Proof.
  pose proof @boxp_one_unknown1 MLPubL _ _ MLPubpbL_a MLPubGamma _ _ _ _ _ B0 C0.
  apply H.
Qed.

Lemma boxa_one_unknown2: |-- (diamonda (B0 && C0) && diamonda (B0 && ~~C0) && diamonda (~~B0 && C0) && diamonda (~~B0 && ~~C0)) --> A0 --> (~~boxa (~~(A0&&B0&&C0))).
Proof.
  pose proof @boxp_one_unknown2 MLPubL _ _ MLPubpbL_a MLPubGamma _ _ _ _ _ B0 C0.
  apply H.
Qed.

Lemma boxa_from_unknown: |-- (~~ boxa (A0&&B0&&C0) && ~~ boxa (~~(A0&&B0&&C0))) --> A0.
Proof.
  pose proof @boxp_from_unknown1 MLPubL _ _ MLPubpbL_a MLPubGamma _ _ _ _ B0 C0.
  apply H.
Qed.

Lemma boxb_two_unknown1: |-- (diamondb (A0 && C0) && diamondb (A0 && ~~C0) && diamondb (~~A0 && C0) && diamondb (~~A0 && ~~C0)) --> boxb A0 --> B0 --> (~~boxb (A0&&B0&&C0)).
Proof.
  pose proof @boxp_two_unknown1 MLPubL _ _ MLPubpbL_b MLPubGamma _ _ _ _ _ A0 C0.
  apply H.
Qed.

Lemma boxb_two_unknown2: |-- (diamondb (A0 && C0) && diamondb (A0 && ~~C0) && diamondb (~~A0 && C0) && diamondb (~~A0 && ~~C0)) --> boxb A0 --> B0 --> (~~boxb (~~(A0&&B0&&C0))).
Proof.
  pose proof @boxp_two_unknown2 MLPubL _ _ MLPubpbL_b MLPubGamma _ _ _ _ _ A0 C0.
  apply H.
Qed.

Lemma boxb_from_unknown: |-- (~~ boxb (A0&&B0&&C0) && ~~ boxb (~~(A0&&B0&&C0))) --> B0.
Proof.
  pose proof @boxp_from_unknown2 MLPubL _ _ MLPubpbL_b MLPubGamma _ _ _ _ A0 C0.
  apply H.
Qed.

Lemma boxc_from_hear: forall (p q: L_Pub), |-- boxc p --> boxc (p --> q) --> boxc q.
Proof.
  intros.
  pose proof @boxp_from_hear MLPubL _ _ MLPubpbL_c MLPubGamma _ _ _ _ p q.
  apply H.
Qed.

Lemma boxc_three_know: |-- boxc A0 --> boxc B0 --> C0 --> boxc (A0&&B0&&C0).
Proof.
  pose proof boxp_three_know A0 B0.
  apply H.
Qed.

Lemma provable_andp_impp: forall p q r, |-- (p --> q --> r) <--> (p && q --> r).
Proof.
  intros.
  pose proof Intuitionistic.provable_andp_impp p q r.
  apply H.
Qed.

Lemma provables_impp_andp_fold_infer1: forall p q r s, |-- p --> q --> r -> |-- p --> q --> s -> |-- p --> q --> r&&s.
Proof.
  intros.
  pose proof provable_andp_impp p q r.
  rewrite H1 in H.
  pose proof provable_andp_impp p q s.
  rewrite H2 in H0.
  pose proof provables_impp_andp_fold (p && q) r s H H0.
  pose proof provable_andp_impp p q (r && s).
  rewrite <- H4 in H3.
  apply H3.
Qed.

Lemma provables_impp_andp_fold_infer2: forall p q r s t, |-- p --> q --> r --> s -> |-- p --> q --> r --> t -> |-- p --> q --> r --> s&&t.
Proof.
  intros.
  pose proof provable_andp_impp p q (r --> s).
  pose proof provable_andp_impp (p && q) r s.
  rewrite H2 in H1.
  rewrite H1 in H.
  pose proof provable_andp_impp p q (r --> t).
  pose proof provable_andp_impp (p && q) r t.
  rewrite H4 in H3.
  rewrite H3 in H0.
  pose proof provables_impp_andp_fold (p && q && r) s t H H0.
  pose proof provable_andp_impp p q (r --> s && t).
  pose proof provable_andp_impp (p && q) r (s && t).
  rewrite H7 in H6.
  rewrite <- H6 in H5.
  apply H5.
Qed.

Lemma provable_andp_impp_infer1: forall a b c p q, |-- (a --> p && q --> b --> c) -> |-- (a --> p --> q --> b --> c).
Proof.
  intros.
  pose proof provable_andp_impp p q (b --> c).
  rewrite <- H0 in H.
  apply H.
Qed.



Lemma A_DONT_KNOW: |-- boxa ((diamonda (B0 && C0) && diamonda (B0 && ~~C0) && diamonda (~~B0 && C0) && diamonda (~~B0 && ~~C0)) --> A0 --> (~~boxa (A0&&B0&&C0)) && (~~boxa (~~(A0&&B0&&C0)))).
Proof.
  pose proof boxa_one_unknown1.
  pose proof boxa_one_unknown2.
  pose proof provables_impp_andp_fold_infer1 _ _ _ _ H H0.
  pose proof N_RULE_A _ H1.
  apply H2. Qed.


Lemma B_DONT_KNOW: |-- boxb ((diamondb (A0 && C0) && diamondb (A0 && ~~C0) && diamondb (~~A0 && C0) && diamondb (~~A0 && ~~C0)) --> boxb (~~boxa (A0&&B0&&C0) && ~~boxa (~~(A0&&B0&&C0))) --> B0 --> (~~boxb (A0&&B0&&C0)) && (~~boxb (~~(A0&&B0&&C0)))).
Proof.
  pose proof boxa_from_unknown.
  rewrite -> H.
  pose proof boxb_two_unknown1.
  pose proof boxb_two_unknown2.
  pose proof provables_impp_andp_fold_infer2 _ _ _ _ _ H0 H1.
  pose proof N_RULE_B _ H2.
  apply H3. Qed.

Lemma C_KNOW: |-- boxc (boxc (~~boxa (A0&&B0&&C0) && ~~boxa (~~(A0&&B0&&C0))) --> boxc (boxb (~~boxa (A0&&B0&&C0) && ~~boxa (~~(A0&&B0&&C0)))) --> boxc (boxb (~~boxa (A0&&B0&&C0) && ~~boxa (~~(A0&&B0&&C0))) --> ~~boxb (A0&&B0&&C0) && ~~boxb (~~(A0&&B0&&C0))) --> C0 --> boxc (A0&&B0&&C0)).
Proof.
  pose proof boxc_from_hear (boxb (~~ boxa (A0 && B0 && C0) && ~~ boxa (~~ (A0 && B0 && C0)))) (~~ boxb (A0 && B0 && C0) && ~~ boxb (~~ (A0 && B0 && C0))).
  pose proof provable_andp_impp (boxc (boxb (~~ boxa (A0 && B0 && C0) && ~~ boxa (~~ (A0 && B0 && C0))))) (boxc (boxb (~~ boxa (A0 && B0 && C0) && ~~ boxa (~~ (A0 && B0 && C0))) --> ~~ boxb (A0 && B0 && C0) && ~~ boxb (~~ (A0 && B0 && C0)))) (boxc (~~ boxb (A0 && B0 && C0) && ~~ boxb (~~ (A0 && B0 && C0)))).
  rewrite -> H0 in H.
  pose proof boxa_from_unknown.
  pose proof boxb_from_unknown.
  pose proof boxc_three_know.
  rewrite <- H2 in H3 at 1.
  rewrite <- H1 in H3 at 1.
  rewrite <- H in H3.
  pose proof provable_andp_impp_infer1 _ _ _ _ _ H3.
  pose proof N_RULE_C _ H4.
  apply H5. Qed.








End ModalLogic_Pub.
