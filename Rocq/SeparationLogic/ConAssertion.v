Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Export Integers.

From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CommonAssertion.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

Class STS : Type := {
  token : Type;
  STS_state : Type;
  TokenSet := token -> Prop;
  STS_state_transition : Type := (STS_state * TokenSet) -> (STS_state * TokenSet) -> Prop;
  Transition : STS_state_transition;
  InvownedToken : STS_state -> TokenSet
}.

Section lowlevel_state.

Context {S : STS}.

Record Lstate : Type := mk_Lstate {
  s_mem : mem ;
  s_STS : STS_state -> Prop; 
  s_token : TokenSet;
}.

Theorem Lstate_eq_split : forall n m, n.(s_mem) = m.(s_mem) -> n.(s_STS) == m.(s_STS) -> n.(s_token) == m.(s_token) ->
n = m.
Proof.
  intros.
  destruct n,m; simpl in *.
  assert (s_STS0 = s_STS1). { apply pred_ext1; tauto. }
  assert (s_token0 = s_token1). { apply pred_ext1; tauto. }
  subst. auto.
Qed.

Definition TokenSet_join (s1 s2 s3 : TokenSet) : Prop :=
  s3 == s1 ∪ s2 /\ s1 ∩ s2 == ∅.

Definition valid_transtion (s1 s2: STS_state * TokenSet) : Prop := 
  match s1, s2 with 
  | (st1, token1), (st2, token2) =>  
      exists tkf,
        TokenSet_join (InvownedToken st1) token1 tkf /\ 
        TokenSet_join (InvownedToken st2) token2 tkf
  end.

Definition valid_Lstate (ls : Lstate) := forall s, s_STS ls s -> s_token ls ∩ InvownedToken s == ∅.

Definition transtion_disjoint_preserved (T : STS_state_transition) := forall s1 s2 token1 token2,
  T (s1,token1) (s2,token2) ->
  token1 ∩ InvownedToken s1 == ∅ /\ token2 ∩ InvownedToken s2 == ∅.

Definition transition_token_preserved (T : STS_state_transition) := forall s1 s2 token1 token2 tf, 
  T (s1,token1) (s2,token2) ->
  TokenSet_join token1 (InvownedToken s1) tf <-> TokenSet_join token2 (InvownedToken s2) tf.  

Definition STS_state_join (s1 s2 s3 : STS_state -> Prop) : Prop :=
  s3 == s1 ∩ s2.

Definition state_join (s1 s2 s3 : Lstate) : Prop := 
  mem_join s1.(s_mem) s2.(s_mem) s3.(s_mem) /\ 
  TokenSet_join s1.(s_token) s2.(s_token) s3.(s_token) /\ 
  STS_state_join s1.(s_STS) s2.(s_STS) s3.(s_STS).

Theorem valid_state_join : forall s1 s2 s3, 
  state_join s1 s2 s3 ->
  valid_Lstate s1 -> valid_Lstate s2 ->
  valid_Lstate s3.
Proof.
  intros. destruct H as [? [? ?]].
  unfold valid_Lstate in *.
  intros.
  unfold STS_state_join, TokenSet_join in *.
  destruct H2.
  rewrite H2.
  rewrite Sets_intersect_union_distr_r.
  sets_unfold in H3.
  apply H3 in H4.
  destruct H4.
  specialize (H0 _ H4).
  specialize (H1 _ H6).
  rewrite H0. rewrite H1. rewrite Sets_empty_union. reflexivity.
Qed. 

(* rely_closed may be used when proof*)
Definition rely_closed (ls : Lstate) (T : STS_state_transition) : Prop := forall s1 s2,
  ls.(s_STS) s1 -> 
  T (s1 , Sets.complement (ls.(s_token) ∪ InvownedToken s1)) (s2, Sets.complement (ls.(s_token) ∪ InvownedToken s2)) -> 
  ls.(s_STS) s2 .

Definition Closed_transition (T : STS_state_transition) := forall s1 s2 token1 token2 token3,
  T (s1, token1) (s2, token2) ->
    token1 ∩ token3 == ∅ ->
    token3 ∩ InvownedToken s1 == ∅ ->
  T (s1, token1 ∪ token3) (s2, token2 ∪ token3).

Theorem keep_rely_closed : forall ls1 ls2 ls3,
  state_join ls1 ls2 ls3 -> 
  valid_Lstate ls1 ->
  valid_Lstate ls2 ->
  rely_closed ls1 Transition ->
  rely_closed ls2 Transition ->
  transtion_disjoint_preserved Transition ->
  transition_token_preserved Transition ->
  Closed_transition Transition ->
  rely_closed ls3 Transition.
Proof.
  intros.
  rename H0 into valid_ls1.
  rename H1 into valid_ls2.
  rename H4 into valid_trans_disjoin.
  rename H5 into valid_trans_token.
  rename H6 into Closed_transition.
  unfold state_join in *.
  unfold rely_closed. intros.
  destruct H as [? [ ? ? ]].
  unfold TokenSet_join in H4.
  unfold STS_state_join in H5.
  sets_unfold in H5.
  intros.
  apply H5. apply H5 in H0. 
  clear H5.
  replace (s_token ls3) with (s_token ls1 ∪ s_token ls2) in H1.
  2: { 
    apply pred_ext1.
    intros.
    destruct H4. sets_unfold in H4.
    rewrite H4. sets_unfold. tauto.
  }
  destruct H4, H0. sets_unfold in H5.
  assert (Sets.complement (s_token ls1 ∪ s_token ls2) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s1) ∪ InvownedToken s1).
  {
    rewrite! Sets_complement_union.
    rewrite! Sets_union_intersect_distr_r.
    rewrite Sets_complement_self_union.
    rewrite Sets_intersect_full.
    rewrite <- Sets_union_intersect_distr_r.
    sets_unfold.
    intros.
    split ; intros ; try tauto.
    destruct H7 ; try tauto.
    split ; intro.
    + specialize (valid_ls1 _ H0).
      sets_unfold in valid_ls1.
      eapply valid_ls1 ; eauto. 
    + specialize (valid_ls2 _ H6).
      sets_unfold in valid_ls2.
      eapply valid_ls2 ; eauto.
  }
  assert (Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s1) ∩ InvownedToken s1 == ∅).
  {
    rewrite !Sets_complement_union.
    rewrite Sets_intersect_assoc.
    rewrite Sets_complement_self_intersect.
    rewrite Sets_intersect_empty. reflexivity.
  }
  split.
  - eapply (H2 s1) ; eauto ; try tauto.
  hnf in valid_trans_token.
    specialize (valid_trans_token _ _ _ _ (Sets.complement
    (s_token ls1 ∪ s_token ls2)) H1).
    unfold TokenSet_join in valid_trans_token.
    assert (Sets.complement (s_token ls1 ∪ InvownedToken s1) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s1) ∪ (s_token ls2)).
    {
      rewrite! Sets_complement_union.
      rewrite! Sets_union_intersect_distr_r.
      rewrite Sets_complement_self_union.
      rewrite Sets_intersect_full.
      rewrite <- Sets_union_intersect_distr_r.
      sets_unfold.
      intros.
      split ; intros ; try tauto.
      destruct H9 ; split ; intro ; try tauto.
      + eapply H5 ; eauto.
      + specialize (valid_ls2 _ H6).
        sets_unfold in valid_ls2.
        eapply valid_ls2 ; eauto.
    }
    assert (Sets.complement (s_token ls1 ∪ s_token ls2) ==
    Sets.complement
      (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s2)
    ∪ InvownedToken s2 /\
    Sets.complement
      (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s2)
    ∩ InvownedToken s2 == ∅). { apply valid_trans_token. tauto. } 
    clear valid_trans_token.
    replace (Sets.complement (s_token ls1 ∪ InvownedToken s1)) with 
      ((Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s1)) ∪ (s_token ls2)). 
    2: {
      sets_unfold.
      apply pred_ext1. sets_unfold in H9. intro. rewrite H9. reflexivity.
    }
    destruct H10.
    replace (Sets.complement (s_token ls1 ∪ InvownedToken s2)) with 
      (Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s2) ∪ (s_token ls2)).
    2:{
      sets_unfold.
      apply pred_ext1. intros.
      sets_unfold in H5.
      split.
      - intros. intro. destruct H12 ; try tauto.
        destruct H13.
        + eapply H5 ; eauto.
        + assert (~ (s_token ls1 a \/ s_token ls2 a)).
          { sets_unfold in H10.
            apply H10. tauto.
          }
          tauto.
      - intros. tauto.
      }
    eapply Closed_transition ; eauto.
    sets_unfold. intros ; split ; intros ; tauto.
  - eapply (H3 s1) ; eauto ; try tauto.
  specialize (valid_trans_token _ _ _ _ (Sets.complement
  (s_token ls1 ∪ s_token ls2)) H1).
  unfold TokenSet_join in valid_trans_token.
  assert (Sets.complement (s_token ls2 ∪ InvownedToken s1) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s1) ∪ (s_token ls1)).
  {
    rewrite! Sets_complement_union.
    rewrite! Sets_union_intersect_distr_r.
    rewrite Sets_complement_self_union.
    rewrite Sets_full_intersect.
    rewrite <- Sets_union_intersect_distr_r.
    sets_unfold.
    intros.
    split ; intros ; try tauto.
    destruct H9 ; split ; intro ; try tauto.
    + eapply H5 ; eauto.
    + specialize (valid_ls1 _ H0).
      sets_unfold in valid_ls1.
      eapply valid_ls1 ; eauto.
  }
  assert (Sets.complement (s_token ls1 ∪ s_token ls2) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s2) ∪ InvownedToken s2 /\ Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s2) ∩ InvownedToken s2 == ∅). { apply valid_trans_token ; tauto. } 
  clear valid_trans_token.
  replace (Sets.complement (s_token ls2 ∪ InvownedToken s1)) with 
    ((Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s1)) ∪ (s_token ls1)). 
  2: {
    sets_unfold.
    apply pred_ext1. sets_unfold in H9. intro. rewrite H9. reflexivity.
  }
  destruct H10.
  replace (Sets.complement (s_token ls2 ∪ InvownedToken s2)) with 
    (Sets.complement (s_token ls1 ∪ s_token ls2 ∪ InvownedToken s2) ∪ (s_token ls1)).
  2:{
    sets_unfold.
    apply pred_ext1. intros.
    sets_unfold in H7.
    split.
    - intros. intro. destruct H12 ; try tauto.
      destruct H13.
      + eapply H5 ; eauto.
      + assert (~ (s_token ls1 a \/ s_token ls2 a)).
        { sets_unfold in H10.
          apply H10. tauto.
        }
        tauto.
    - intros. tauto.
    }
  eapply Closed_transition ; eauto.
  sets_unfold. intros ; split ; intros ; tauto.
Qed. 

Definition state_empty (s: Lstate) : Prop := 
  mem_empty s.(s_mem) /\ 
  s.(s_token) == ∅ /\ s.(s_STS) == Sets.full.

Definition empty_state : Lstate :=  {|
  s_mem := empty_mem ;
  s_STS := Sets.full;
  s_token := ∅
|}.

Lemma empty_state_is_empty : state_empty empty_state.
Proof.
  unfold empty_state.
  repeat split ; simpl ; auto. 
Qed.

End lowlevel_state.

Module Type STS_def.
  Parameter sts : STS.
End STS_def.

Module Type CSL (L_STS: STS_def) <: SeparationLogicSig.

Import L_STS.

(* Modle Names: LanguageSig. *)

  Definition model : Type := @Lstate sts.

  Definition expr := model -> Prop .

  Definition join : model -> model -> model -> Prop := state_join.
  
  Definition is_unit : model -> Prop := state_empty.

(* End LanguageSig. *)

Include DerivedNamesSig.

(* Rules <: PrimitiveRuleSig Names *)

  Theorem unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Proof.
    intros. exists empty_state.
    unfold is_unit , join , state_join.
    split ; [apply empty_state_is_empty | ].
    intros. 
    split ;  [solve_empmem | unfold empty_state ; simpl; split].
    - unfold TokenSet_join. sets_unfold. tauto.
    - unfold STS_state_join. sets_unfold.  tauto. 
  Qed.
      
  Theorem unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Proof.
    intros.
    unfold is_unit, join in *.
    destruct H0 as [? [? ?]].
    destruct H as [? [? ?]].
    apply mem_empty_IS_empty_mem' in H. 
    rewrite H in *.
    apply mem_join_emp_r in H0.
    unfold TokenSet_join in *.
    unfold STS_state_join in *.
    rewrite H3 in H1. rewrite H4 in H2.
    destruct H1.
    rewrite Sets_union_empty in H1.
    rewrite Sets_intersect_full in H2.
    apply Lstate_eq_split; auto ; try (symmetry ; tauto).
  Qed.

  Theorem join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m).
  Proof.
    intros.
    unfold join , state_join, TokenSet_join in *.
    destruct H as [? [? ?]].
    split ; [|split].
    - apply mem_join_comm ; auto.
    - destruct H0. rewrite H0. rewrite Sets_union_comm.
      split ; [reflexivity | rewrite Sets_intersect_comm ; auto]. 
    - unfold STS_state_join in *.
      rewrite H1. rewrite Sets_intersect_comm. reflexivity.
  Qed.  

  Theorem join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz).
  Proof.
    intros.
    unfold join , state_join, TokenSet_join, STS_state_join in *.
    destruct H as [? [[? ?] ?]].
    destruct H0 as [? [[? ?] ?]].
    exists (mk_Lstate (merge (s_mem my) (s_mem mz)) (s_STS my ∩ s_STS mz) (s_token my ∪ s_token mz)).
    simpl. 
    split ; (split ; [ | split ]).
    - apply disjoint_merge_mem_join.
      pose proof (mem_join_disjoint H0).
      apply disjoint_comm.
      eapply disjoint_mem_join_r ; eauto.
      apply disjoint_comm ; auto.
    - split ; try reflexivity.
      revert H1 H2 H4 H5.
      sets_unfold ; intros.
      split ; try tauto.
      intros. destruct H7.
      erewrite <- H5.
      split ; eauto.
      apply H1 ; auto.
    - reflexivity.
    - apply mem_join_merge_assoc_l.
      + eapply mem_join_disjoint ; eauto.
      + apply mem_join_eqmerge in H.
        rewrite <- H. auto.
    - split.
      + rewrite H4. rewrite H1.
        rewrite Sets_union_assoc. reflexivity.
      + rewrite Sets_intersect_union_distr_l.
        rewrite H2. rewrite Sets_empty_union.
        revert H1 H2 H4 H5.
        sets_unfold ; intros.
        split ; try tauto.
        intros. destruct H7.
        erewrite <- H5.
        split ; eauto.
        apply H1 ; auto.
    - rewrite H6. rewrite H3.
      rewrite Sets_intersect_assoc. reflexivity.
  Qed.  

(* End Rules. *)

Include LogicTheoremSig'.

Arguments exp {A}.


(* The following are basic definitions *)

Definition mstore (p: addr) (v: Z) : expr := 
  fun Lst => exists v',
             Byte.eqm v v' /\
             Lst.(s_mem) = single_byte_mem p v' /\ 
             Lst.(s_STS) == Sets.full /\ 
             Lst.(s_token) == ∅.

Definition mstore_noninit (p: addr) : expr :=
  fun Lst => Lst.(s_STS) == Sets.full /\ 
             Lst.(s_token) == ∅ /\
             ((Lst.(s_mem) = single_Noninit_mem p) \/ 
                (exists v, Lst.(s_mem) = single_byte_mem p v) ).

Theorem mstore_mstore_noninit:
  forall p v s,
    mstore p v s ->
    mstore_noninit p s.
Proof.
  unfold mstore, mstore_noninit.
  intros.
  destruct H as [v' ?].
  split; [tauto | ].
  split; [tauto | ].
  right.
  exists v'.
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
  destruct H as [m1 [m2 [? [[? [? Hm1]] [? [? Hm2]]]]]].
  unfold join, state_join in H.
  destruct H as [Hjoin ?].
  unfold mem_join in Hjoin.
  specialize (Hjoin x).
  destruct Hjoin as [ | [ | [ | [ | ]]]].
  + destruct H4 as [? [? ?]].
    destruct Hm1.
    - rewrite H7 in H4.
      unfold single_Noninit_mem in H4.
      rewrite Z.eqb_refl in H4.
      discriminate.
    - destruct H7 as [v H7].
      rewrite H7 in H4.
      unfold single_byte_mem in H4.
      rewrite Z.eqb_refl in H4.
      discriminate.
  + destruct H4 as [? [? ?]].
    destruct Hm1.
    - rewrite H7 in H4.
      unfold single_Noninit_mem in H4.
      rewrite Z.eqb_refl in H4.
      discriminate.
    - destruct H7 as [v H7].
      rewrite H7 in H4.
      unfold single_byte_mem in H4.
      rewrite Z.eqb_refl in H4.
      discriminate.
  + destruct H4 as [? [? ?]].
    destruct Hm2.
    - rewrite H7 in H5.
      unfold single_Noninit_mem in H5.
      rewrite Z.eqb_refl in H5.
      discriminate.
    - destruct H7 as [v H7].
      rewrite H7 in H5.
      unfold single_byte_mem in H5.
      rewrite Z.eqb_refl in H5.
      discriminate.
  + destruct H4 as [v' [? [? ?]]].
    destruct Hm1.
    - rewrite H7 in H4.
      unfold single_Noninit_mem in H4.
      rewrite Z.eqb_refl in H4.
      discriminate.
    - destruct H7 as [v H7].
      rewrite H7 in H4.
      unfold single_byte_mem in H4.
      rewrite Z.eqb_refl in H4.
      discriminate.
  + destruct H4 as [v' [? [? ?]]].
    destruct Hm2.
    - rewrite H7 in H5.
      unfold single_Noninit_mem in H5.
      rewrite Z.eqb_refl in H5.
      discriminate.
    - destruct H7 as [v H7].
      rewrite H7 in H5.
      unfold single_byte_mem in H5.
      rewrite Z.eqb_refl in H5.
      discriminate.
Qed.

Definition at_states (P: STS_state -> Prop): expr :=
  fun Q => 
    Q.(s_mem) = empty_mem /\
    Sets.equiv P Q.(s_STS) /\
    Sets.equiv Q.(s_token) Sets.empty.

Definition has_tokens (P: TokenSet): expr :=
  fun Q => 
    Q.(s_mem) = empty_mem /\
    Sets.equiv Q.(s_STS) Sets.empty /\
    Sets.equiv P Q.(s_token).

End CSL.

Definition naive_S : STS := {|
  token := False;
  STS_state := False;
  Transition := fun _ _ => False;
  InvownedToken := fun _ _ => False;
|}.

Module STS_naive <: STS_def.
  Definition sts := naive_S.
End STS_naive.

