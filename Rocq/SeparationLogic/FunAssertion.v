Require Import ZArith Bool List Morphisms String.

From AUXLib Require Import int_auto Axioms Feq ListLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
Import ListNotations.
From compcert.lib Require Export Integers.

Require Import SimpleC.Common.CTypes.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CommonAssertion.

From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.


Module Type SL <: SeparationLogicSig.

(* Modle Names: LanguageSig. *)
  Definition ParamSig : Type := list SimpleCtype.
  Definition FuncSig : Type := ParamSig * SimpleCtype.
  Export SimpleC.Common.CTypes.
  Export SimpleC.CoreLang.CTypes.

  Definition RetType (t : SimpleCtype) : Type :=
    match t with
    | CT_basic CT_void => unit
    | _ => Z
    end.

  Fixpoint ParamTuple (ts : ParamSig) : Type :=
    match ts with
    | nil => unit
    | t :: nil => Z
    | t :: ts' => (Z * ParamTuple ts')%type
    end.
  (*
    [FunSem] is scoped function semantics.

    [F θ] starts from the callee-entry state, after formal parameters have been
    allocated/initialized. Primitive type parameters are bound to values.
    Aggrerate type parameters are bound to addresses, with the corresponding
    memory regions initialized by the real arguments.

    [F θ] ends at the function-return state after callee-owned parameter storage
    has been discharged.
   *)
  Definition FunSem (s : FuncSig) :=
    ParamTuple (fst s) -> program mem (RetType (snd s)).
  Definition FunEnv :=
    forall (s : FuncSig), Z -> option (FunSem s).

  Record state : Type := {
    st_mem: mem;
    st_χ: FunEnv
  }.

  Definition model := state.

  Definition expr := model -> Prop .

  Definition join : model -> model -> model -> Prop :=
    fun m1 m2 m =>
      mem_join m1.(st_mem) m2.(st_mem) m.(st_mem) /\
      m.(st_χ) = m1.(st_χ) /\ m.(st_χ) = m2.(st_χ).

  Definition is_unit : model -> Prop := fun m =>
    mem_empty m.(st_mem).

(* End LanguageSig. *)

Include DerivedNamesSig.

(* LogicRule <: PrimitiveRuleSig Names *)

  Theorem unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Proof.
    intros. exists {|st_mem := empty_mem; st_χ := n.(st_χ)|}.
    unfold is_unit , join. simpl.
    split. 1: solve_empmem.
    split. 1: solve_empmem.
    split; reflexivity.
  Qed.

  Theorem unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Proof.
    intros [n_mem n_χ] [m_mem m_χ] [u_mem u_χ] H1 [H2 [H3 H4]].
    unfold is_unit, join in *.
    simpl in *.
    solve_empmem.
    f_equal.
  Qed.

  Theorem join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m).
  Proof.
    intros [m1_mem m1_χ] [m2_mem m2_χ] [m_mem m_χ] [H1 [H2 H3]].
    unfold join in *.
    simpl in *.
    split. 1: apply mem_join_comm; auto.
    split; auto.
  Qed.

  Theorem join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz).
  Proof.
    intros [mx_mem mx_χ] [my_mem my_χ] [mz_mem mz_χ] [mxy_mem mxy_χ] [mxyz_mem mxyz_χ] [H1 [H2 H3]] [H4 [H5 H6]].
    unfold join in *.
    simpl in *.
    pose proof (mem_join_assoc2 H1 H4) as [myz_mem [H7 H8]].
    exists {|st_mem := myz_mem; st_χ := mx_χ|}. simpl.
    split; split; auto.
    all: split; congruence.
  Qed.

(* End Rules. *)

Include LogicTheoremSig'.

Arguments exp {A}.

(* The following are basic definitions *)

Definition mstore (p: addr) (v: Z): expr := 
  fun st =>
    exists v', Byte.eqm v v' /\ st.(st_mem) = single_byte_mem p v'.

Definition mstore_noninit (p: addr): expr :=
  fun st => ((st.(st_mem) = single_Noninit_mem p) \/ (exists v, st.(st_mem) = single_byte_mem p v)).

Theorem mstore_mstore_noninit:
  forall p v s,
    mstore p v s ->
    mstore_noninit p s.
Proof.
  unfold mstore, mstore_noninit.
  intros.
  right.
  destruct H as [v' ?]; exists v'.
  tauto.
Qed.

Theorem mstore_eqm: forall p v v',
  Byte.eqm v v' ->
  derivable1 (mstore p v) (mstore p v').
Proof.
  intros.
  unfold mstore, derivable1.
  intros m [v'' [? ?] ].
  exists v''.
  split; [| tauto].
  eapply Byte.eqm_trans.
  + apply Byte.eqm_sym, H.
  + apply H0.
Qed.

Theorem dup_mstore_noninit: 
  forall x,
    derivable1
      (sepcon (mstore_noninit x) (mstore_noninit x))
      (coq_prop False).
Proof.
  unfold mstore_noninit, sepcon, derivable1.
  intros.
  destruct H as [m1 [m2 [? [Hm1 Hm2]]]].
  destruct H as [H _].
  unfold join, mem_join in H.
  specialize (H x).
  destruct H as [ | [ | [ | [ | ]]]].
  + destruct H as [? [? ?]].
    destruct Hm1.
    - rewrite H2 in H.
      unfold single_Noninit_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H.
      unfold single_byte_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
  + destruct H as [? [? ?]].
    destruct Hm1.
    - rewrite H2 in H.
      unfold single_Noninit_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H.
      unfold single_byte_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
  + destruct H as [? [? ?]].
    destruct Hm2.
    - rewrite H2 in H0.
      unfold single_Noninit_mem in H0.
      rewrite Z.eqb_refl in H0.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H0.
      unfold single_byte_mem in H0.
      rewrite Z.eqb_refl in H0.
      discriminate.
  + destruct H as [v' [? [? ?]]].
    destruct Hm1.
    - rewrite H2 in H.
      unfold single_Noninit_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
    - destruct H2 as [v ?].
      rewrite H2 in H.
      unfold single_byte_mem in H.
      rewrite Z.eqb_refl in H.
      discriminate.
  + destruct H as [v' [? [? ?]]].
  destruct Hm2.
  - rewrite H2 in H0.
    unfold single_Noninit_mem in H0.
    rewrite Z.eqb_refl in H0.
    discriminate.
  - destruct H2 as [v ?].
    rewrite H2 in H0.
    unfold single_byte_mem in H0.
    rewrite Z.eqb_refl in H0.
    discriminate.
Qed.

Definition Assertion : Type := expr.

Definition Spec (s : FuncSig) : Type :=
  FunSem s -> Assertion.

Definition HoareExpr_raw {R : Type}
  (P : Assertion) (c : program mem R) (Q : R -> Assertion) : Assertion :=
  fun st =>
    Hoare
      (fun m => P {| st_mem := m; st_χ := st.(st_χ) |})
      c
      (fun r m => Q r {| st_mem := m; st_χ := st.(st_χ) |}).

(* A function specification preserves every disjoint frame. *)
Definition HoareExpr {R : Type}
  (P : Assertion) (c : program mem R) (Q : R -> Assertion) : Assertion :=
  fun st => forall frame : Assertion,
    HoareExpr_raw (sepcon P frame) c (fun r => sepcon (Q r) frame) st.

Definition func_ptr_spec {s : FuncSig}
  (f : Z) (S : Spec s) : Assertion :=
  andp (coq_prop (f <> NULL))
  (fun st => exists F,
    st.(st_χ) s f = Some F /\
    S F st).

Lemma func_ptr_spec_mono {s : FuncSig}
  (f : Z) (S1 S2 : Spec s) :
  (forall F, derivable1 (S1 F) (S2 F)) ->
  derivable1 (func_ptr_spec f S1) (func_ptr_spec f S2).
Proof.
  intros HS st [Hnonzero [F [Hlookup HF]]].
  split; [exact Hnonzero |].
  exists F. split; [exact Hlookup |].
  exact (HS F st HF).
Qed.

Instance func_ptr_spec_derivable1_Proper {s : FuncSig} :
  Proper (eq ==> (pointwise_relation (FunSem s) derivable1) ==> derivable1)
    (@func_ptr_spec s).
Proof.
  intros f1 f2 <- S1 S2 HS.
  apply func_ptr_spec_mono. exact HS.
Qed.

Definition HoareFun (s : FuncSig)
  (P : ParamTuple (fst s) -> Assertion)
  (Q : ParamTuple (fst s) -> RetType (snd s) -> Assertion)
    : Spec s := fun F =>
  allp _ (fun θ : ParamTuple (fst s) =>
    HoareExpr (P θ) (F θ) (Q θ)).

Lemma HoareExpr_corable {R : Type}
  (P : Assertion) (c : program mem R) (Q : R -> Assertion) :
  corable (HoareExpr P c Q).
Proof.
  unfold corable, HoareExpr, HoareExpr_raw, join.
  intros [m1 χ1] [m2 χ2] [m χ] [_ [Hχ1 _]].
  cbn in *.
  subst χ1.
  split; auto.
Qed.

Lemma HoareFun_corable {s : FuncSig}
  (P : ParamTuple (fst s) -> Assertion)
  (Q : ParamTuple (fst s) -> RetType (snd s) -> Assertion)
  (F : FunSem s) :
  corable (HoareFun s P Q F).
Proof.
  unfold corable, HoareFun.
  intros st1 st2 st Hjoin.
  split; intros HF θ.
  - apply (proj1 (HoareExpr_corable (P θ) (F θ) (Q θ) st1 st2 st Hjoin)).
    apply HF.
  - apply (proj2 (HoareExpr_corable (P θ) (F θ) (Q θ) st1 st2 st Hjoin)).
    apply HF.
Qed.

Lemma func_ptr_spec_corable {s : FuncSig}
  (f : Z) (S : Spec s) :
  (forall F, corable (S F)) ->
  corable (func_ptr_spec f S).
Proof.
  intros HS.
  apply corable_andp. 1: apply corable_coq_prop.
  unfold corable, func_ptr_spec.
  intros st1 st2 st Hjoin.
  pose proof Hjoin as Hjoin_χ.
  unfold join in Hjoin_χ.
  destruct Hjoin_χ as [_ [Hχ1 _]].
  split; intros [F [Hlookup HF]]; exists F; split.
  - rewrite Hχ1.
    exact Hlookup.
  - apply (proj1 (HS F st1 st2 st Hjoin)).
    exact HF.
  - rewrite <- Hχ1.
    exact Hlookup.
  - apply (proj2 (HS F st1 st2 st Hjoin)).
    exact HF.
Qed.

Lemma allp_corable {A : Type} (P : A -> Assertion) :
  (forall a, corable (P a)) ->
  corable (allp A P).
Proof.
  unfold corable, allp.
  intros HP st1 st2 st Hjoin.
  split; intros H a.
  - apply (proj1 (HP a st1 st2 st Hjoin)).
    apply H.
  - apply (proj2 (HP a st1 st2 st Hjoin)).
    apply H.
Qed.

Lemma func_ptr_spec_nonzero {s : FuncSig} (f : Z) (S : Spec s) :
  derivable1 (func_ptr_spec f S) (coq_prop (f <> NULL)).
Proof.
  unfold func_ptr_spec.
  apply derivable1_andp_elim1.
Qed.

Lemma func_ptr_spec_nonzero' {s : FuncSig} (f : Z) (S : Spec s) :
  derivable1 (func_ptr_spec f S) (andp (coq_prop (f <> NULL)) (func_ptr_spec f S)).
Proof.
  apply derivable1s_andp_intros.
  - apply func_ptr_spec_nonzero.
  - reflexivity.
Qed.

Instance HoareExpr_raw_mono {R} :
  Proper (derivable1 --> eq ==> (pointwise_relation R derivable1) ==> derivable1) HoareExpr_raw.
Proof.
  unfold Proper, respectful, HoareExpr_raw.
  intros P1 P2 HP F _ <- Q1 Q2 HQ.
  hnf. intros m H.
  split.
  - destruct H as [H _].
    intros a σ1 σ2 HP2 HF. apply HQ. apply (H a σ1 σ2); auto.
  - destruct H as [_ H].
    intros σ HP2. apply (H σ). apply HP. apply HP2.
Qed.

Instance HoareExpr_mono {R} :
  Proper (derivable1 --> eq ==> (pointwise_relation R derivable1) ==> derivable1) HoareExpr.
Proof.
  unfold Proper, respectful.
  intros P1 P2 HP c _ <- Q1 Q2 HQ st H frame.
  assert (HPframe : derivable1 (sepcon P2 frame) (sepcon P1 frame)).
  { apply derivable1_sepcon_mono; [exact HP | reflexivity]. }
  assert (HQframe : pointwise_relation R derivable1
    (fun a => sepcon (Q1 a) frame) (fun a => sepcon (Q2 a) frame)).
  { intros a. apply derivable1_sepcon_mono; [apply HQ | reflexivity]. }
  exact (HoareExpr_raw_mono _ _ HPframe c c eq_refl _ _ HQframe st (H frame)).
Qed.

Lemma HoareExpr_exists {A R} : forall P (Q : R -> _) F,
  logic_equiv
    (HoareExpr (exp P) F Q)
    (allp _ (fun a : A => HoareExpr (P a) F Q)).
Proof.
  intros P Q F.
  split.
  - intros st H x frame.
    specialize (H frame).
    unfold HoareExpr_raw in *.
    eapply Hoare_cons_pre; [| exact H].
    intros m [st1 [st2 [Hjoin [HP HR]]]].
    exists st1, st2. split; [exact Hjoin |].
    split; [exists x; exact HP | exact HR].
  - intros st H frame.
    unfold HoareExpr_raw.
    split.
    + intros a m1 m2 [st1 [st2 [Hjoin [[x HP] HR]]]] Hrun.
      apply (proj1 (H x frame) a m1 m2); [| exact Hrun].
      exists st1, st2. auto.
    + intros m [st1 [st2 [Hjoin [[x HP] HR]]]] Herr.
      apply (proj2 (H x frame) m); [| exact Herr].
      exists st1, st2. auto.
Qed.

Lemma HoareExpr_forget_frame {A}
  (P : Assertion) (c : program mem A) (Q : A -> Assertion) :
  derivable1 (HoareExpr P c Q) (HoareExpr_raw P c Q).
Proof.
  intros st H.
  assert (HQ : pointwise_relation A derivable1
    (fun a => sepcon (Q a) emp) Q).
  { intros a. apply derivable1_sepcon_emp_l. }
  exact (HoareExpr_raw_mono _ _ (derivable1_sepcon_emp_r P)
    c c eq_refl _ _ HQ st (H emp)).
Qed.

Lemma frame_rule_sound {A}
  (c : program mem A) (P : Assertion) (Q : A -> Assertion) (R : Assertion) :
  derivable1
    (HoareExpr P c Q)
    (HoareExpr (sepcon P R) c (fun a => sepcon (Q a) R)).
Proof.
  intros st H frame.
  assert (HP : derivable1 (sepcon (sepcon P R) frame) (sepcon P (sepcon R frame))).
  { apply (proj2 (logic_equiv_sepcon_assoc P R frame)). }
  assert (HQ : pointwise_relation A derivable1
    (fun a => sepcon (Q a) (sepcon R frame))
    (fun a => sepcon (sepcon (Q a) R) frame)).
  { intros a. apply derivable1_sepcon_assoc1. }
  exact (HoareExpr_raw_mono _ _ HP c c eq_refl _ _ HQ st (H (sepcon R frame))).
Qed.

Lemma HoareFun_exists {A s} : forall P Q F,
  logic_equiv
    (HoareFun s (fun θ => exp (fun a : A => P a θ)) Q F)
    (allp _ (fun a => HoareFun s (P a) Q F)).
Proof.
  intros.
  unfold HoareFun.
  split.
  - apply derivable1s_allp_r. intros a.
    apply derivable1s_allp_r. intros θ.
    apply (derivable1s_allp_l _ _ _ θ).
    rewrite HoareExpr_exists.
    apply (derivable1s_allp_l _ _ _ a).
    reflexivity.
  - apply derivable1s_allp_r. intros θ.
    rewrite HoareExpr_exists.
    apply derivable1s_allp_r. intros a.
    apply (derivable1s_allp_l _ _ _ a).
    apply (derivable1s_allp_l _ _ _ θ).
    reflexivity.
Qed.

Definition safety_mono {A} (c : program mem A) : Prop :=
  forall m1,
    ~ c.(MonadErr.err) m1 ->
    forall m2,
      mem_incl m1 m2 ->
      ~ c.(MonadErr.err) m2.

Definition frame_property {A} (c : program mem A) : Prop :=
  forall m a m',
    c.(MonadErr.nrm) m a m' ->
    forall m1 m2,
      mem_join m1 m2 m ->
      ~ c.(MonadErr.err) m1 ->
      exists m1',
        mem_join m1' m2 m' /\
        c.(MonadErr.nrm) m1 a m1'.

Definition frame_properties {A} (c : program mem A) : Prop :=
  safety_mono c /\ frame_property c.

Definition funsem_frame_properties {s} (F : FunSem s) : Prop :=
  forall θ, frame_properties (F θ).

Lemma HoareExpr_raw_frame_rule {A}
  (c : program mem A) (P : Assertion) (Q : A -> Assertion) (R : Assertion) :
  frame_properties c ->
  derivable1
    (HoareExpr_raw P c Q)
    (HoareExpr_raw (sepcon P R) c (fun a => sepcon (Q a) R)).
Proof.
  intros [Hmono Hframe] [m χ] [Hnrm Herr].
  unfold HoareExpr_raw in *; cbn in *.
  split.
  - intros a m0 m' Hsep Hrun.
    unfold sepcon, join in Hsep.
    destruct Hsep as [st1 [st2 [Hjoin [HP HR]]]].
    destruct st1 as [m1 χ1], st2 as [m2 χ2].
    cbn in Hjoin, HP, HR.
    destruct Hjoin as [Hjoin [Hχ1 Hχ2]].
    subst χ1; subst χ2.
    assert (Hsafe1 : ~ c.(MonadErr.err) m1).
    { intros Herr1. eapply Herr; eauto. }
    destruct (Hframe m0 a m' Hrun m1 m2 Hjoin Hsafe1)
      as [m1' [Hjoin' Hrun']].
    unfold sepcon, join.
    exists {| st_mem := m1'; st_χ := χ |},
      {| st_mem := m2; st_χ := χ |}.
    cbn.
    split.
    + split; [exact Hjoin' |].
      split; reflexivity.
    + split.
      * eapply Hnrm; eauto.
      * exact HR.
  - intros m0 Hsep Herr_big.
    unfold sepcon, join in Hsep.
    destruct Hsep as [st1 [st2 [Hjoin [HP _]]]].
    destruct st1 as [m1 χ1], st2 as [m2 χ2].
    cbn in Hjoin, HP.
    destruct Hjoin as [Hjoin [Hχ1 Hχ2]].
    subst χ1; subst χ2.
    assert (Hsafe1 : ~ c.(MonadErr.err) m1).
    { intros Herr1. eapply Herr; eauto. }
    specialize (Hmono m1 Hsafe1 m0 (mem_join_incl_l _ _ _ Hjoin)).
    contradiction.
Qed.

Lemma HoareExpr_of_raw {A}
  (P : Assertion) (c : program mem A) (Q : A -> Assertion) :
  frame_properties c ->
  derivable1 (HoareExpr_raw P c Q) (HoareExpr P c Q).
Proof.
  intros Hlocal st H frame.
  exact (HoareExpr_raw_frame_rule c P Q frame Hlocal st H).
Qed.

Lemma HoareFun_ramification : forall s P_base Q_base P_derived Q_derived,
  (forall θ : ParamTuple (fst s),
    derivable1
      (P_derived θ)
      (sepcon
        (P_base θ)
        (allp _ (fun r : RetType (snd s) => wand (Q_base θ r) (Q_derived θ r))))) ->
  forall F : FunSem s,
    derivable1
      (HoareFun s P_base Q_base F)
      (HoareFun s P_derived Q_derived F).
Proof.
  intros s P_base Q_base P_derived Q_derived Hram F χ HF θ.
  specialize (Hram θ).
  assert (Hpost :
    pointwise_relation _ derivable1
    (fun r => sepcon (Q_base θ r)
      (allp _ (fun r0 : RetType (snd s) => wand (Q_base θ r0) (Q_derived θ r0))))
    (Q_derived θ)).
  {
    intros r.
    rewrite derivable1_sepcon_comm.
    rewrite derivable1s_wand_sepcon_adjoint.
    eapply (derivable1s_allp_l _ _ _ r).
    reflexivity.
  }
  pose proof (frame_rule_sound (F θ) (P_base θ) (Q_base θ)
    (allp _ (fun r : RetType (snd s) => wand (Q_base θ r) (Q_derived θ r)))
    χ (HF θ)) as Hframed.
  exact (HoareExpr_mono _ _ Hram (F θ) (F θ) eq_refl _ _ Hpost χ Hframed).
Qed.

Lemma HoareFun_conseq : forall s P_base Q_base P_derived Q_derived,
  (forall θ, derivable1 (P_derived θ) (P_base θ)) ->
  (forall θ r, derivable1 (Q_base θ r) (Q_derived θ r)) ->
  forall F : FunSem s,
    derivable1
      (HoareFun s P_base Q_base F)
      (HoareFun s P_derived Q_derived F).
Proof.
  intros * HP HQ F χ HF θ.
  exact (HoareExpr_mono _ _ (HP θ) (F θ) (F θ) eq_refl _ _ (HQ θ) χ (HF θ)).
Qed.

Definition func_ptr_hoare (f : Z) (s : FuncSig) P Q : Assertion :=
  func_ptr_spec f (HoareFun s P Q).

Lemma func_ptr_hoare_corable {s : FuncSig}
  (f : Z)
  (P : ParamTuple (fst s) -> Assertion)
  (Q : ParamTuple (fst s) -> RetType (snd s) -> Assertion) :
  corable (func_ptr_hoare f s P Q).
Proof.
  unfold func_ptr_hoare.
  apply func_ptr_spec_corable.
  intros F.
  apply HoareFun_corable.
Qed.

Module Example.
(* apply(f : Z -> Z, x : Z) : Z := f(x) *)
Import SimpleCtypeNotations.
Definition apply_sig : FuncSig :=
  ([ ( *fn (i32) i32) ; (i32) ]%list , i32)%ctype.
Definition unary_sig : FuncSig :=
  ([ i32 ]%list , i32)%ctype.

Definition apply_spec : Spec apply_sig :=
  fun applyF χ =>
    forall P : Z -> Assertion,
    forall Q : Z -> Z -> Assertion,
      HoareFun apply_sig
        (fun '(f, x) =>
          andp
            (* (HasSpec f (fun F => HoareFun unary_sig P F Q)) *)
            (func_ptr_hoare f unary_sig P Q)
            (P x))
        (fun '(f, x) ret =>
          Q x ret) applyF χ.

Definition apply_has_spec (apply_f : Z) : Assertion :=
  func_ptr_spec apply_f apply_spec.
End Example.

Include IterSepconLibSig.

End SL.
