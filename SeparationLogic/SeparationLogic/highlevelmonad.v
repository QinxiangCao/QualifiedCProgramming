Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From AUXLib Require Import relations Axioms. 
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import SetsNotation.
Local Open Scope sets.



Class StateTransitionSys {T: Type} : Type := {
  valid_st: T -> Prop;
  trans: T -> T -> Prop;
  #[global] trans_refl :: Reflexive trans;
}.

Class highlevelstatemodel : Type := {
  hmem : Type;
  (* FIRST LEVEL sts state *)
  STS_stateₕ  : Type;
  #[global] STSₕ :: @StateTransitionSys STS_stateₕ;
  (* SECOND LEVEL sts state *)
  STS_stateₕ₂: Type;
  #[global] STSₕ₂ :: @StateTransitionSys STS_stateₕ₂;
}.

Record Hstate {hst: highlevelstatemodel}: Type := mk_hstate {
  hs_mem: hmem;
  hs_STS: STS_stateₕ -> Prop;
  hs_STSₕ₂: STS_stateₕ₂ -> Prop;
}.



Arguments mk_hstate {hst} _ _ _.

Definition closure {T: Type} `{@StateTransitionSys T} (s1: T) : T -> Prop := fun s2 =>
 trans s1 s2.

Section  highlevel_monad.
  
  (* Alive 线程集合 : 暂定不需要 *)
  Context {stmodel: highlevelstatemodel}.


  (* Definition atomic_step (atom:  STS_stateₕ -> unit -> STS_stateₕ -> Prop) : program unit :=
    step_to_program (fun hs1 hs2 =>  
                (forall s1, hs1.(hs_STS) s1 -> valid_st s1 -> 
                  forall s0 s2,  atom s1 tt s0 -> trans s0 s2 -> hs2.(hs_STS) s2) /\ 
                (forall s2, hs2.(hs_STS) s2 -> valid_st s2 -> 
                  exists s1 s0, valid_st s1 /\ hs1.(hs_STS) s1 /\ atom s1 tt s0 /\ trans s0 s2) /\
                     hs2.(hs_STSₕ₂) = hs2.(hs_STSₕ₂) /\  
                     hs2.(hs_mem) = hs2.(hs_mem)).


  Definition atomic_step_ret {A: Type} (atom:  STS_stateₕ -> A ->  STS_stateₕ -> Prop) : program A :=
    fun hs1 a hs2 => 
                (forall s1, hs1.(hs_STS) s1 -> valid_st s1 -> 
                  forall s0 s2,  atom s1 a s0 -> trans s0 s2 -> hs2.(hs_STS) s2) /\ 
                (forall s2, hs2.(hs_STS) s2 -> valid_st s2 -> 
                      exists s1 s0, valid_st s1 /\ hs1.(hs_STS) s1 /\ atom s1 a s0 /\ trans s0 s2) /\ 
                    hs2.(hs_STSₕ₂) = hs2.(hs_STSₕ₂) /\ 
                    hs2.(hs_mem) = hs2.(hs_mem). *)
  Definition Σ := @Hstate stmodel.

  Definition atomic_step (atom:  STS_stateₕ -> unit -> STS_stateₕ -> Prop) : program Σ unit :=
    @step_to_program (Σ) (fun hs1 hs2 =>  exists s1 s2, hs1.(hs_STS) s1 /\ valid_st s1 /\ atom s1 tt s2 /\ hs2.(hs_STS) == closure s2 /\
                     hs2.(hs_STSₕ₂) = hs2.(hs_STSₕ₂) /\  
                     hs2.(hs_mem) = hs2.(hs_mem)).


  Definition atomic_step_ret {A: Type} (atom:  STS_stateₕ -> A ->  STS_stateₕ -> Prop) : program A :=
    fun hs1 a hs2 => exists s1 s2, hs1.(hs_STS) s1 /\ valid_st s1 /\ atom s1 a s2 /\ hs2.(hs_STS) == closure s2 /\ 
                    hs2.(hs_STSₕ₂) = hs2.(hs_STSₕ₂) /\ 
                    hs2.(hs_mem) = hs2.(hs_mem).


End  highlevel_monad.

Import MonadNotation.
Local Open Scope monad. 
Module HighMonadNotation.

  Notation " 'ATOM' o " := (atomic_step o) (at level 60, no associativity) : stmonad_scope.

  Notation " 'ATOMR' o " := (atomic_step_ret o) (at level 60, no associativity) : stmonad_scope.

End HighMonadNotation.


Definition hsts_sat {hstm: highlevelstatemodel} (P: STS_stateₕ -> Prop) : Σ -> Prop :=
  fun hst =>  hst.(hs_STS) == P.

Definition Outside_critical {hstm: highlevelstatemodel} (P: STS_stateₕ -> Prop) : Σ -> Prop := 
  hsts_sat P.

Definition Inside_critical {hstm: highlevelstatemodel} (s: STS_stateₕ) : Σ -> Prop := 
  hsts_sat [s].  

Ltac destruct_hst hst := 
    let m := fresh "m" in let stsₕ := fresh "stsₕ" in let stsₕ₂ := fresh "stsₕ₂" in destruct hst as [m stsₕ stsₕ₂]. 

Section  highlevel_monad_rules.
  Context {stmodel: highlevelstatemodel}.

  Import HighMonadNotation.

  Definition sts_eval {A: Type}  (P : STS_stateₕ -> Prop) (c : STS_stateₕ -> A ->  STS_stateₕ -> Prop) (a : A) (Q : (STS_stateₕ -> Prop))  := 
    exists st, P st /\ valid_st st /\ exists st',  c st a st' /\  Q == closure st'.


  Definition exact_eval  {A: Type}  (P : STS_stateₕ -> Prop) (c : STS_stateₕ -> A ->  STS_stateₕ -> Prop) (a : A) (Q : (STS_stateₕ -> Prop))  := 
  (forall st, P st -> valid_st st -> forall st', c st a st' ->  Q st') /\ 
  (forall st',  Q st' -> valid_st st' -> exists st, c st a st'  /\ valid_st st /\ P st ).

  Definition closed_asrt {T: Type} `{@StateTransitionSys T} (P: T -> Prop) : Prop := 
    forall s1 s2, P s1 -> trans s1 s2 -> P s2.


  Lemma atomicstep_eval : forall  (op: STS_stateₕ -> unit -> STS_stateₕ -> Prop) (P Q: STS_stateₕ -> Prop), 
    sts_eval P (op) tt Q  ->
    (hsts_sat P) -@ (ATOM op) -→ (hsts_sat Q).
  Proof.
    intros *.
    unfold hs_eval, hsts_sat;intros.
    exists tt.
    intros.
    destruct_hst σₕ.
    cbn in H0.
    exists (mk_hstate m Q stsₕ₂).
    unfold atomic_step.
    unfold step_to_program in *.
    cbn.
    splits;auto.
    2: reflexivity.
    destruct H as (s1 & ? & ? & (s2 & ? & ?) ).
    exists s1, s2.
    splits;auto.
    apply H0;auto.
  Qed.

  Lemma atomicret_eval : forall  {A: Type} (op: STS_stateₕ -> A -> STS_stateₕ -> Prop) (P Q: STS_stateₕ -> Prop) a,
    sts_eval P (op) a Q  ->
    (hsts_sat P) -@ (ATOMR op) -⥅ (hsts_sat Q) ♯ a.
  Proof.
    intros *.
    unfold sts_eval, hs_eval, hsts_sat;intros.
    destruct_hst σₕ.
    cbn in H0.
    exists (mk_hstate m Q stsₕ₂).
    unfold atomic_step_ret.
    cbn.
    splits;auto.
    2: reflexivity.
    intros.
    destruct H as (s1 & ? & ? & (s2 & ? & ?) ).
    exists s1, s2.
    splits;auto.
    apply H0;auto.
  Qed.

End  highlevel_monad_rules. 




Section  monad_instance.
  Import HighMonadNotation.

  Context (mem: Type).
  Context (sts2: Type).
  Context {timests: @StateTransitionSys sts2}.

  Definition tranR (st1 st2 : list Z) := exists l, st2 = l ++ st1.
  

  Instance r_refl : Reflexive tranR.
  Proof. econstructor. instantiate (1:= nil). auto.  Qed.

  Instance stackstate : stateclass := {|
    Σ := (list Z)
  |}.

  Instance stacksts : @StateTransitionSys (list Z):= {|
    valid_st := fun (st : list Z) => True;
    trans:= tranR;
    trans_refl := r_refl;
  |}.

  Instance stackmodel : highlevelstatemodel := {|
    hmem := mem;
    STS_stateₕ :=  list Z;
    STS_stateₕ₂ := sts2;
  |}.

  Definition stkpop :  STS_stateₕ -> option Z -> STS_stateₕ -> Prop  :=
    fun l1 => (match l1 with 
              | nil => return None
              | x :: l1' => (fun _ v l2 => v = Some x /\ l2 = l1')
              end) l1.
  

  Compute (stkpop (nil)%Z).
  Compute (stkpop (1::nil)%Z).
  Compute (stkpop (1::2::nil)%Z).

  Definition stack_trypop_2times :  STS_stateₕ -> option Z -> STS_stateₕ -> Prop  :=
    v <- stkpop ;;
    (match v with
      | None =>  stkpop
      | Some a => return (Some a)
      end).


  Definition atomstkpop := ATOMR stkpop.

  Definition stack_trypop_aux  :=
    (whileret (return_some) (fun _ => atomstkpop)).
  
  Definition stack_trypop := 
    x <- return None;; stack_trypop_aux x.

  Definition stack_push (x: Z) : STS_stateₕ -> unit -> STS_stateₕ -> Prop := fun l1 _ l2 => l2 = x :: l1.

  Definition stack_length : STS_stateₕ -> Z -> STS_stateₕ -> Prop := fun l1 n l2 => n = Zlength (l1) /\ l2 = l1.

  Definition Outsidesee (l: list Z) := 
    Outside_critical (fun st => exists l', st = l' ++ l).

  Lemma stack_push_eval:  forall l z l',
    Outsidesee l -@ ATOM stack_push z -→ Outsidesee (z :: l' ++ l).
  Proof.
    unfold Outsidesee, Outside_critical.
    intros.
    eapply atomicstep_eval.
    unfold sts_eval.
    exists (l' ++ l).
    cbn.
    splits;eauto.
    unfold stack_push.
    eexists.
    splits;eauto.
    sets_unfold.
    intros l''.
    split;auto.
  Qed. 
  Lemma stack_push_safeexec_derive:  forall l z,
  (forall X, safeExec (Outsidesee l) (ATOM (stack_push z)) X ->  
            forall l', safeExec (Outsidesee (z :: (l' ++  l))) (return tt) X).
  Proof.
    intros.
    eapply highstepend_derive;eauto.
    clear H.
    eapply stack_push_eval.
  Qed.

  Lemma stack_push2_safeexec_derive:  forall l z1 z2,
  (forall X, safeExec (Outsidesee l) ((ATOM (stack_push z1)) ;; (ATOM (stack_push z2))) X ->  
            forall l' l'', safeExec (Outsidesee (z2 :: (l'' ++ z1 :: (l' ++  l)))) (return tt) X).
  Proof.
    intros.
    eapply highstepseq_derive in H.
    2: { eapply stack_push_eval with (l':= l'). }
    eapply highstepend_derive;eauto.
    eapply stack_push_eval;eauto.
  Qed.

  Lemma stack_length_eval:  forall l  l',
    Outsidesee l -@ ATOMR stack_length -⥅ Outsidesee (l' ++ l) ♯ (Zlength (l' ++ l)).
  Proof.
    unfold Outsidesee, Outside_critical.
    intros.
    eapply atomicret_eval.
    unfold sts_eval.
    exists (l' ++ l).
    cbn.
    splits;eauto.
    unfold stack_length.
    eexists.
    splits;eauto.
    sets_unfold.
    intros l''.
    split;auto.
  Qed. 

  Lemma stack_pushlength_safeexec_derive:  forall l,
  (forall X, safeExec (Outsidesee l) ( z <- (ATOMR (stack_length)) ;; (ATOM (stack_push z))) X ->  
            forall l' l'', safeExec (Outsidesee (Zlength (l' ++ l) :: (l'' ++  (l' ++  l)))) (return tt) X).
  Proof.
    intros.
    eapply highstepbind_derive with (P':= (fun (x: Z) => Outsidesee (l' ++ l))) in H.
    2: { eapply stack_length_eval with (l':= l'). }
    eapply highstepend_derive;eauto.
    eapply stack_push_eval;eauto.
  Qed.

End  monad_instance.


