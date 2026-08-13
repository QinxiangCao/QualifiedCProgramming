Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Export Logic.lib.register_typeclass.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.

Inductive P2D_reg:=.
Inductive D2P_reg:=.
Inductive P2D1_reg:=.
Inductive P2E_reg:=.
Inductive D12P_reg:=.
Inductive D12E_reg:=.

Ltac pose_proof_P2D_instance n :=
  let a := get_nth P2D_reg n in
  match a with
  | fun x: unit => ?T => 
    try pose_proof_instance_as T x
  end.

Ltac pose_proof_D2P_instance n :=
  let a := get_nth D2P_reg n in
  match a with
  | fun x: unit => ?T => 
    try pose_proof_instance_as T x
  end.

Ltac pose_proof_P2D1_instance n :=
  let a := get_nth P2D1_reg n in
  match a with
  | fun x: unit => ?T =>
    try pose_proof_instance_as T x
  end.

Ltac pose_proof_P2E_instance n :=
  let a := get_nth P2E_reg n in
  match a with
  | fun x: unit => ?T =>
    try pose_proof_instance_as T x
  end.

Ltac pose_proof_D12P_instance n :=
  let a := get_nth D12P_reg n in
  match a with
  | fun x: unit => ?T => 
    try pose_proof_instance_as T x
  end.

Ltac AddSequentCalculus :=
  let GammaDP := fresh "GammaDP" in
  let GammaD := fresh "GammaD" in
  pose proof Provable2Derivable_Normal as GammaDP;
  set (GammaD := Provable2Derivable) in GammaDP;
  clearbody GammaD;
  rec_from_n (0%nat) pose_proof_P2D_instance.

Ltac AddAxiomatizationFromSequentCalculus :=
  let SC := fresh "GammaPD" in
  let GammaP := fresh "GammaP" in
  pose proof Derivable2Provable_Normal as GammaPD;
  set (GammaP := Derivable2Provable) in GammaPD;
  clearbody GammaP;
  rec_from_n (0%nat) pose_proof_D2P_instance.

Ltac AddAxiomatizationFromDeduction :=
  let GammaPD1 :=fresh "GammaPD1" in
  let GammaP := fresh "GammaP" in
  pose proof Derivable12Provable_Normal as GammaPD1;
  set (GammaP := Derivable12Provable) in GammaPD1;
  clearbody GammaP;
  rec_from_n (0%nat) pose_proof_D12P_instance.

Ltac AddAxiomatization :=
  match goal with
  |AddAxSC:Derivable _ |- _ => AddAxiomatizationFromSequentCalculus
  |ADDAxD:Derivable1 _ |- _ => AddAxiomatizationFromDeduction
  end.

Ltac AddDeduction :=
  let GammaD1P := fresh "GammaD1P" in
  let GammaD1 := fresh "GammaD1" in
  pose proof Provable2Derivable1_Normal as GammaD1P;
  set (GammaD1 := Provable2Derivable1) in GammaD1P;
  clearbody GammaD1;
  rec_from_n (0%nat) pose_proof_P2D1_instance.

Ltac AddEquiv :=
  let GammaEP :=fresh "GammaEP" in
  let GammaE :=fresh "GammaE" in
  pose proof Provable2Equiv_Normal as GammaEP;
  set (GammaE := Provable2Equiv) in GammaEP;
  clearbody GammaE;
  rec_from_n (0%nat) pose_proof_P2E_instance.

#[export] Instance reg_Axiomatization2SequentCalculus_GammaPD:
  RegisterClass P2D_reg (fun SC: unit => @Axiomatization2SequentCalculus_GammaPD) 0.
Qed.

#[export] Instance reg_Axiomatization2SequentCalculus_bSC:
  RegisterClass P2D_reg (fun bSC: unit => @Axiomatization2SequentCalculus_bSC) 1.
Qed.

#[export] Instance reg_Axiomatization2SequentCalculus_fwSC:
  RegisterClass P2D_reg (fun fwSC: unit => @Axiomatization2SequentCalculus_fwSC) 2.
Qed.

#[export] Instance reg_Axiomatization2SequentCalculus_minSC:
  RegisterClass P2D_reg (fun minSC: unit => @Axiomatization2SequentCalculus_minSC) 3.
Qed.

#[export] Instance reg_SequentCalculus2Axiomatization_GammaDP:
  RegisterClass D2P_reg (fun AX: unit => @SequentCalculus2Axiomatization_GammaDP) 0.
Qed.

#[export] Instance reg_SequentCalculus2Axiomatization_minAX:
  RegisterClass D2P_reg (fun minAX: unit => @SequentCalculus2Axiomatization_minAX) 1.
Qed.

#[export] Instance reg_Axiomatization2Deduction_bD:
  RegisterClass P2D1_reg (fun BD: unit => @Axiomatization2Deduction_bD) 0.
Qed.

#[export] Instance reg_Axiomatization2Equiv_bE:
  RegisterClass P2E_reg (fun bE: unit => @Axiomatization2Equiv_bE) 0.
Qed.

Section Test_AddD.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimumAxiomatization L GammaP}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma test_AddD: forall (x:expr), |-- x --> x.
Proof.
  AddDeduction.
  Abort.

End Test_AddD.

Section Test_AddE.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimumAxiomatization L GammaP}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma test_AddE: forall (x:expr), |-- x --> x.
Proof.
  AddEquiv.
  Abort.

End Test_AddE.

Section Test_AddSC.

Context {L: Language}
        {minL: MinimumLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma provable_impp_refl': forall (x: expr), |-- x --> x.
Proof.
  AddSequentCalculus.
Abort.

End Test_AddSC.

Section Test_AddAXSC.

Context {L: Language}
        {minL: MinimumLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma derivable_axiom2': forall Phi (x y z: expr), Phi |--- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  AddAxiomatizationFromSequentCalculus.
Abort.

End Test_AddAXSC.

Section test_AddAXD.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma test_AddE: forall (x:expr), derivable1 x x.
Proof.
  AddAxiomatizationFromDeduction.
  Abort.

End test_AddAXD.

Section text_AX.

Local Open Scope logic_base.
Local Open Scope syntax.

Context {L: Language}
        {minL: MinimumLanguage L}.

Section test_SequentCalculus.

Context {GammaD: Derivable L}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {fwSC: FiniteWitnessedSequentCalculus L GammaD}.

Lemma test_1: forall Phi (x y z: expr), Phi |--- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  AddAxiomatization.
  Abort.

End test_SequentCalculus.

Section test_Deduction.

Context {GammaD1 :Derivable1 L}
        {bD: BasicDeduction L GammaD1}.

Lemma test_2:forall x y, (x --> x) |-- (y --> y).
Proof.
  AddAxiomatization.
  Abort.

End test_Deduction.

End text_AX.
