Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From MonadLib.MonadErr Require Import MonadErrBasic.

Import Monad MonadNotation SetsNotation.
Local Open Scope sets.
Local Open Scope monad.
Export CPO_lift.
Local Open Scope order_scope.

(*************************************************************************************************************)
(**********************************          monad program registerd         *********************************)
(**********************************                program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)

#[export] Instance oLub_program {Σ A: Type} : OmegaLub (MonadErr.M Σ A) :=
  ProgramPO.indexed_union.

#[export] Instance bot_program {Σ A: Type} : Bot (MonadErr.M Σ A) :=
  ProgramPO.bot.

#[export] Instance oCPO_program {Σ A: Type} : CompletePartialOrder_Setoid (MonadErr.M Σ A).
Proof.
  split.
  + apply program_PO.
  + unfold seq_mono, seq_least_upper_bound, seq_upper_bound.
    unfold omega_lub, order_rel, program_order, oLub_program; simpl.
    intros T H.
    split.
    - intros n.
      specialize (H n) as [H H1].
      constructor;simpl in *. 
      * sets_unfold. intros.
        exists n.
        tauto.
      * sets_unfold. intros.
        exists n.
        tauto.
    - intros a H0.
      constructor;simpl in *.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [H0 _]. eapply H0;eauto.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [_ H0]. eapply H0;eauto.
  + unfold least_element.
    unfold bot, order_rel, program_order, bot_program; simpl.
    intros a.
    constructor;simpl.
    sets_unfold. 
    tauto.
    sets_unfold. 
    tauto.
Qed.

(*************************************************************************************************************)
(**********************************     lift monad program registerd         *********************************)
(**********************************           B -> program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)
#[export] Instance Transitive_lift  {A: Type} {B: Type} {RB: Order B} {TB: Transitive (@order_rel B _) } 
  : Transitive (@order_rel (A -> B) _ ).
Proof.
  unfold Transitive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  etransitivity;eauto.
Qed.

#[export] Instance Reflexive_lift  {A: Type} {B: Type} {RB: Order B} {ReflB: Reflexive (@order_rel B _) } 
  : Reflexive (@order_rel (A -> B) _ ).
Proof.
  unfold Reflexive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  reflexivity.
Qed.



(*************************************************************************************************************)
(**********************************     mono and continuous_lemmas           *********************************)
(*************************************************************************************************************)
Section mono_and_continuous_lemmas.
  Import MonadErr.
  Import MonadNotation.
  Context {Σ: Type}.

  Notation " ⋃  a " := (omega_lub a): order_scope.

  Definition increasing {A: Type} {RA: Order A } (T : nat -> A):= @seq_mono A RA T.

  Definition mono {A: Type} {RA: Order A}  {B: Type} {RB: Order B}  
    (f : A -> B) := Proper (order_rel ==> order_rel) f.
  Definition continuous {A: Type} {RA: Order A} {oLubA: OmegaLub A}
          {B: Type} {EB: Equiv B} {oLubB: OmegaLub B}
    (f : A -> B) := @seq_continuous  A RA oLubA B EB oLubB f.
  Definition mono_cont {A: Type} {RA: Order A} {oLubA: OmegaLub A} {B: Type} {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B}
    (f : A -> B) := mono f /\ continuous f.

  Lemma BW_fixpoint'{A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Setoid A} f:
    mono_cont f ->
    BW_fix f == f (BW_fix f).
  Proof.
    unfold mono_cont; intros.
    apply BourbakiWitt_fixpoint; tauto.
  Qed.

  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    increasing c -> c n <= c (n + m).
  Proof.
    induction m;intros.
    - assert (n + 0 = n) by lia. rewrite H0.
      reflexivity.
    - assert (n + S m = S (n + m)) by lia.
      rewrite H0.
      transitivity (c (n + m)).
      eapply IHm;auto.
      eapply H.
  Qed. 

  Lemma increasing_program_le : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    (n <= m)%nat ->  increasing c  -> c n <= c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus;auto.
  Qed.

  Lemma increasing_program_plus' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    increasing c -> c n <= c (n + m).
  Proof.
    induction m;intros.
    - assert (n + 0 = n) by lia. rewrite H0.
      reflexivity.
    - assert (n + S m = S (n + m)) by lia.
      rewrite H0.
      transitivity (c (n + m)).
      eapply IHm;auto.
      eapply H.
  Qed. 

  Lemma increasing_program_le' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    (n <= m)%nat ->  increasing c  -> c n <= c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus' ;auto.
  Qed.

  Lemma mono_intro {X I Y: Type} {RX: Order X} {RY: Order Y}:
    forall (f: X -> I -> Y),
      (forall i, mono (fun x => f x i)) ->
      mono f.
  Proof.
    unfold mono, Proper, respectful.
    unfold order_rel, R_lift, LiftConstructors.lift_rel2, order_rel.
    sets_unfold; intros.
    eapply H; auto.
  Qed.

  Lemma mono_bind {X C D: Type} {RX: Order X}:
    forall (c1: X -> program Σ D) (c2: X -> D -> program Σ C),
      mono c1 ->
      (forall d, mono (fun x => c2 x d)) ->
      mono (fun x => bind (c1 x) (c2 x)).
  Proof.
    unfold mono, Proper, respectful.
    intros.
    specialize (H x y H1).
    inversion H. 
    constructor; unfold_monad. 
    - unfold nrm_nrm.
      intros s0 b s2 [d [s1 [Hc1 Hc2]]].
      apply nrmle in Hc1.
      specialize (H0 d x y H1).
      inversion H0.
      apply nrmle0 in Hc2.
      exists d, s1.
      tauto.
    - unfold nrm_err; sets_unfold.
      intros s [? | [d [s1 [Hn He]]]].
      + apply errle in H2; tauto.
      + specialize (H0 d x y H1).
        inversion H0.
        apply nrmle in Hn.
        apply errle0 in He.
        right; exists d, s1.
        tauto.
  Qed.

  Lemma mono_bind' {B C D: Type}:
    forall  (c1: (program Σ B) -> program Σ D) (c2: (program Σ B) -> D -> program Σ C),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    intros. apply mono_bind; auto.
  Qed.

  Lemma mono_choice {X D: Type} {RX: Order X}:
    forall (c1 c2: X -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun x => choice (c1 x) (c2 x)).
  Proof.
    unfold mono, Proper, respectful, choice.
    intros.
    specialize (H x y H1).
    specialize (H0 x y H1).
    constructor; simpl; sets_unfold.
    - intros s0 d s1 [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
    - intros s [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
  Qed.

  Lemma mono_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    intros. apply mono_choice; auto.
  Qed.

  Lemma continuous_intro {X I Y: Type}
    {RX: Order X} {LX: OmegaLub X} {EY: Equiv Y} {LY: OmegaLub Y}:
    forall (f: X -> I -> Y),
      (forall i, continuous (fun x => f x i)) ->
      continuous f.
  Proof.
    unfold continuous, seq_continuous, seq_mono.
    unfold equiv, Equiv_lift, LiftConstructors.lift_rel2,
      omega_lub, oLub_lift, LiftConstructors.lift_binder.
    intros. apply H. assumption.
  Qed.

  Lemma continuous_const {X Y: Type}
    {RX: Order X} {LX: OmegaLub X}
    {RY: Order Y} {EY: Equiv Y} {LY: OmegaLub Y} {BY: Bot Y}
    {equY: Equivalence (@equiv Y EY)}
    {CPOY: CompletePartialOrder_Setoid Y}:
    forall (y: Y),
      continuous (fun (_: X) => y).
  Proof.
    intros y T HT. symmetry. apply const_limit.
  Qed.

  Lemma continuous_const' {B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: program Σ B) => f).
  Proof.
    intros. apply continuous_const.
  Qed.

  Lemma continuous_bind {X C D: Type}
    {RX: Order X} {EX: Equiv X} {LX: OmegaLub X} {BX: Bot X}
    {equX: Equivalence (@equiv X EX)}
    {CPOX: CompletePartialOrder_Setoid X}:
    forall (c1: X -> program Σ D) (c2: X -> D -> program Σ C),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun x => c2 x d)) ->
      (forall d, continuous (fun x => c2 x d)) ->
      continuous (fun x => bind (c1 x) (c2 x)).
  Proof.
    unfold mono, continuous, seq_continuous, Proper, respectful.
    unfold_monad; intros.
    specialize (H0 T H3).
    constructor; 
    unfold nrm_nrm, nrm_err;
    simpl;
    sets_unfold; [intros s0 b s2 | intros s]; split.
    - intros [d [s1 [Hc1 Hc2]]].
      specialize (H2 d T H3).
      apply H0 in Hc1; simpl in Hc1; sets_unfold in Hc1.
      apply H2 in Hc2; simpl in Hc2; sets_unfold in Hc2.
      destruct Hc1 as [i1 Hc1].
      destruct Hc2 as [i2 Hc2].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s1.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        eapply seq_mono_nat_le; eauto.
      + exists i1, d, s1.
        apply leb_complete_conv in Heq.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        eapply seq_mono_nat_le; eauto; lia.
    - intros [i [d [s1 [Hc1 Hc2]]]].
      exists d, s1.
      split.
      apply H0.
      econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
    - intros [Hc1 | [d [s1 [Hc1 Hc2]]]].
      {
        apply H0 in Hc1.
        inversion Hc1.
        exists x; tauto.
      }
      apply H0 in Hc1.
      apply H2 in Hc2; auto.
      inversion Hc1.
      inversion Hc2; rename x0 into y.
      destruct (x <=? y) eqn:Heq.
      + apply leb_complete in Heq.
        exists y; right.
        exists d, s1.
        split; auto.
        apply H with (x:= T x); auto.
        eapply seq_mono_nat_le; eauto.
      + apply leb_complete_conv in Heq.
        exists x; right.
        exists d, s1.
        split; auto.
        apply H1 with (x:= T y); auto.
        eapply seq_mono_nat_le; eauto; lia.
    - intros [i [Hc1 | [d [s1 [Hc1 Hc2]]]]].
      {
        left; apply H0.
        econstructor; eauto.
      }
      right; exists d, s1.
      split.
      apply H0; econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
  Qed.

  Lemma continuous_bind' {B C D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ C),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    intros. apply continuous_bind; auto.
  Qed.

  Lemma continuous_choice {X D: Type} {RX: Order X} {LX: OmegaLub X}:
    forall (c1 c2: X -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun x => choice (c1 x) (c2 x)).
  Proof.
    unfold continuous, seq_continuous.
    unfold choice; intros.
    specialize (H T H1).
    specialize (H0 T H1).
    do 2 constructor; simpl; sets_unfold.
    - intros [? | ?].
      + apply H in H2.
        inversion H2.
        eexists; eauto.
      + apply H0 in H2.
        inversion H2.
        eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
    - intros [? | ?].
      apply H in H2.
      inversion H2.
      eexists; eauto.
      apply H0 in H2.
      inversion H2.
      eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
  Qed.

  Lemma continuous_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    intros. apply continuous_choice; auto.
  Qed.

  Lemma mono_cont_pointwise {X I Y: Type}
    {RX: Order X} {LX: OmegaLub X}
    {RY: Order Y} {EY: Equiv Y} {LY: OmegaLub Y}:
    forall (f: X -> I -> Y),
      (forall i, mono_cont (fun x => f x i)) ->
      mono_cont f.
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_intro.
      intros; apply H.
    - apply continuous_intro.
      intros; apply H.
  Qed.

  Lemma mono_cont_at {X I Y: Type}
    {RX: Order X} {LX: OmegaLub X}
    {RY: Order Y} {EY: Equiv Y} {LY: OmegaLub Y}:
    forall (f: X -> I -> Y) (i: I),
      mono_cont f ->
      mono_cont (fun x => f x i).
  Proof.
    intros f i [Hmono Hcont]. split.
    - intros x1 x2 Hx. exact (Hmono x1 x2 Hx i).
    - intros T HT. exact (Hcont T HT i).
  Qed.

  Lemma mono_cont_id {X: Type}
    {RX: Order X} {EX: Equiv X} {LX: OmegaLub X} {BX: Bot X}
    {equX: Equivalence (@equiv X EX)}
    {CPOX: CompletePartialOrder_Setoid X}:
    mono_cont (fun x: X => x).
  Proof.
    split.
    - unfold mono, Proper, respectful. intros; assumption.
    - unfold continuous, seq_continuous. intros; reflexivity.
  Qed.

  (** Compatibility wrapper for the original function-program interface. *)
  Lemma mono_cont_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, mono_cont (fun W => f W a)) ->
      mono_cont f.
  Proof.
    intros. apply mono_cont_pointwise. assumption.
  Qed.

  Lemma mono_cont_const {X Y: Type}
    {RX: Order X} {LX: OmegaLub X}
    {RY: Order Y} {EY: Equiv Y} {LY: OmegaLub Y} {BY: Bot Y}
    {equY: Equivalence (@equiv Y EY)}
    {CPOY: CompletePartialOrder_Setoid Y}:
    forall (y: Y),
      mono_cont (fun (_: X) => y).
  Proof.
    intros. split.
    - unfold mono, Proper, respectful. intros. reflexivity.
    - apply continuous_const.
  Qed.

  Lemma mono_cont_const' {B C: Type}:
    forall (f: program Σ C),
      mono_cont (fun (W:program Σ B) => f).
  Proof.
    intros. apply mono_cont_const.
  Qed.

  Lemma mono_cont_bind {X C D: Type}
    {RX: Order X} {EX: Equiv X} {LX: OmegaLub X} {BX: Bot X}
    {equX: Equivalence (@equiv X EX)}
    {CPOX: CompletePartialOrder_Setoid X}:
    forall (c1: X -> program Σ D) (c2: X -> D -> program Σ C),
      mono_cont c1 ->
      (forall d, mono_cont (fun x => c2 x d)) ->
      mono_cont (fun x => bind (c1 x) (c2 x)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_bind; try tauto.
      intros d; apply H0.
    - apply continuous_bind; try tauto;
      intros d; apply H0.
  Qed.

  Lemma mono_cont_bind' {B C D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ C),
      mono_cont c1 ->
      (forall d, mono_cont (fun W => c2 W d)) ->
      mono_cont (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    intros. apply mono_cont_bind; auto.
  Qed.

  Lemma mono_cont_choice {X D: Type}
    {RX: Order X} {EX: Equiv X} {LX: OmegaLub X} {BX: Bot X}
    {equX: Equivalence (@equiv X EX)}
    {CPOX: CompletePartialOrder_Setoid X}:
    forall (c1 c2: X -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun x => choice (c1 x) (c2 x)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice; tauto.
    - apply continuous_choice; tauto.
  Qed.

  Lemma increasing_mono_increasing:
  forall {A B: Type} {RA: Order A} {RB: Order B}
         (f: A -> B)
         (l: nat -> A),
    increasing l -> mono f -> increasing (fun n => f (l n)).
  Proof.
    intros.
    unfold increasing, seq_mono. intros.
    apply H0. apply H.
  Qed.

  Lemma mono_BW_fix {A B: Type} {RA: Order A} {RB: Order B} {EB: Equiv B}
    {oLubB: OmegaLub B} {BotB: Bot B}
    {equ: Equivalence equiv}
    {CPO: CompletePartialOrder_Setoid B}:
    forall (f: A -> B -> B),
      (forall a, mono (f a)) ->
      (forall b, mono (fun W => f W b)) ->
      mono (fun W => (BW_fix (f W))).
  Proof.
    unfold mono in *.
    unfold Proper, respectful in *.
    intros.
    apply BourbakiWitt_fixpoint_monotonic.
    - intros b1 b2 Hb. apply (H x b1 b2 Hb).
    - intros b1 b2 Hb. apply (H y b1 b2 Hb).
    - intros.
      transitivity (f y a).
      + apply H0; auto.
      + apply (H y); auto.
  Qed.

  Lemma BW_fix_seq_cont_general {A B} {RA: Order A} 
    {EA: Equiv A}
    {oLubA: OmegaLub A} {BotA: Bot A}
    {CPOA: CompletePartialOrder_Setoid A}
    {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B} {BotB: Bot B}
    {equA: Equivalence (@equiv A EA)}
    {equB: Equivalence (@equiv B EB)}
    {CPOB: CompletePartialOrder_Setoid B}:
  forall (f: A -> B -> B)
          (Hf_mono: Proper (order_rel ==> order_rel ==> order_rel) f)
          (Hfa_sseq: forall a, continuous (f a))
          (Hf_sseq: forall b, continuous (fun a => f a b)),
    continuous (fun a: A => BW_fix (f a)).
  Proof.
    intros. intros T HT.
    apply antisymmetricity_setoid.
    - unfold BW_fix at 1.
      apply limit_smaller_iff.
      + apply (@iter_bot_mono B _ _ _ _ CPOB (f (omega_lub T))).
        intros x y Hxy. apply Hf_mono. reflexivity. apply Hxy.
      + intros n.
        induction n.
        * simpl. apply CPO_least.
        * simpl.
          transitivity (f (omega_lub T) (omega_lub (fun n => BW_fix (f (T n))))).
          { apply Hf_mono. reflexivity. apply IHn. }
          transitivity (omega_lub (fun n => f (T n) (omega_lub (fun k => BW_fix (f (T k)))))).
          { apply PO_Reflexive_Setoid. apply Hf_sseq. apply HT. }
          apply limit_smaller_iff.
          { apply (@increasing_mono_increasing A B RA RB (fun a => f a (omega_lub (fun k => BW_fix (f (T k))))) T).
            - apply HT.
            - unfold mono, Proper, respectful. intros.
              apply Hf_mono. assumption. reflexivity. }
          intros k.
          transitivity (omega_lub (fun n => f (T k) (BW_fix (f (T n))))).
          { apply PO_Reflexive_Setoid. apply Hfa_sseq.
            apply (@increasing_mono_increasing A B RA RB (fun a => BW_fix (f a)) T).
            - apply HT.
            - apply mono_BW_fix.
              + intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
              + intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
          }
          apply limit_smaller_iff.
          { apply (@increasing_mono_increasing A B RA RB (fun a => f (T k) (BW_fix (f a))) T).
            - apply HT.
            - unfold mono, Proper, respectful. intros x y Hxy.
              apply Hf_mono. reflexivity.
              apply mono_BW_fix.
              + intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
              + intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
              + assumption. }
          intros m.
          apply limit_greater.
          { apply (@increasing_mono_increasing A B RA RB (fun a => BW_fix (f a)) T).
            - apply HT.
            - apply mono_BW_fix.
              + intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
              + intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity. }
          exists (max k m).
          assert (BW_fix (f (T (max k m))) == f (T (max k m)) (BW_fix (f (T (max k m))))).
          { apply BourbakiWitt_fixpoint; auto. apply Hf_mono. reflexivity. apply Hfa_sseq. }
          transitivity (f (T (max k m)) (BW_fix (f (T (max k m))))).
          2: { apply PO_Reflexive_Setoid. symmetry. apply H. }
          apply Hf_mono.
          { apply (@seq_mono_nat_le A RA _ _ T HT k (max k m)). apply Nat.le_max_l. }
          { apply mono_BW_fix.
            - intros a0. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
            - intros b0. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
            - apply (@seq_mono_nat_le A RA _ _ T HT m (max k m)). apply Nat.le_max_r. }
    - apply limit_smaller_iff.
      + apply (@increasing_mono_increasing A B RA RB (fun a => BW_fix (f a)) T).
        * apply HT.
        * apply mono_BW_fix.
          -- intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
          -- intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
      + intros n.
        apply mono_BW_fix.
        * intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
        * intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
        * eapply limit_greater.
          apply HT.
          exists n. reflexivity.
  Qed.

  Lemma mono_cont_BW_fix {A B} {RA: Order A} 
    {EA: Equiv A}
    {oLubA: OmegaLub A} {BotA: Bot A}
    {CPOA: CompletePartialOrder_Setoid A}
    {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B} {BotB: Bot B}
    {equA: Equivalence (@equiv A EA)}
    {equB: Equivalence (@equiv B EB)}
    {CPOB: CompletePartialOrder_Setoid B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun W => f W b)) ->
      mono_cont (fun W => BW_fix (f W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_BW_fix; intros.
      + destruct (H a); auto.
      + destruct (H0 b); auto.
    - apply BW_fix_seq_cont_general; intros.
      + unfold Proper, respectful.
        intros.
        transitivity (f x y0).
        * destruct (H x) as [Hm _]. apply Hm; auto.
        * destruct (H0 y0) as [Hm _]. apply Hm; auto.
      + apply H.
      + apply H0.
  Qed.

  Lemma mono_cont_choice' {B D: Type}:
    forall (c1 c2: (program Σ B) -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    intros. apply mono_cont_choice; auto.
  Qed.

  Lemma Rec_unfold {X: Type} {RX: Order X} {EX: Equiv X}
    {oLubX: OmegaLub X} {BotX: Bot X}
    {equX: Equivalence (@equiv X EX)}
    {CPOX: CompletePartialOrder_Setoid X}:
    forall (f: X -> X),
      mono_cont f -> Rec f == f (Rec f).
  Proof.
    intros. unfold Rec. apply BW_fixpoint'. assumption.
  Qed.

  Lemma Rec_mono {A B: Type} {RA: Order A} {RB: Order B} {EB: Equiv B}
    {oLubB: OmegaLub B} {BotB: Bot B}
    {equB: Equivalence (@equiv B EB)}
    {CPOB: CompletePartialOrder_Setoid B}:
    forall (f: A -> B -> B),
      (forall a, mono (f a)) ->
      (forall b, mono (fun x => f x b)) ->
      mono (fun x => Rec (f x)).
  Proof.
    intros. unfold Rec. apply mono_BW_fix; assumption.
  Qed.

  Lemma Rec_continuous {A B: Type} {RA: Order A} {EA: Equiv A}
    {oLubA: OmegaLub A} {BotA: Bot A}
    {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B} {BotB: Bot B}
    {equA: Equivalence (@equiv A EA)}
    {equB: Equivalence (@equiv B EB)}
    {CPOA: CompletePartialOrder_Setoid A}
    {CPOB: CompletePartialOrder_Setoid B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun x => f x b)) ->
      continuous (fun x => Rec (f x)).
  Proof.
    intros. unfold Rec.
    destruct (mono_cont_BW_fix f H H0). assumption.
  Qed.

  Lemma mono_cont_Rec {A B: Type} {RA: Order A} {EA: Equiv A}
    {oLubA: OmegaLub A} {BotA: Bot A}
    {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B} {BotB: Bot B}
    {equA: Equivalence (@equiv A EA)}
    {equB: Equivalence (@equiv B EB)}
    {CPOA: CompletePartialOrder_Setoid A}
    {CPOB: CompletePartialOrder_Setoid B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun x => f x b)) ->
      mono_cont (fun x => Rec (f x)).
  Proof.
    intros. unfold Rec. apply mono_cont_BW_fix; assumption.
  Qed.

End mono_and_continuous_lemmas.

Ltac mono_cont_auto :=
  lazymatch goal with
  | H: mono_cont ?f |- mono_cont ?f => exact H
  | |- mono_cont (fun x => x) => apply mono_cont_id
  | |- mono_cont (fun (x: ?X) (i: ?I) => _) =>
      apply mono_cont_pointwise; intro; mono_cont_auto
  | |- mono_cont (fun (x: ?X) => bind _ _) =>
      apply mono_cont_bind; [mono_cont_auto | intro; mono_cont_auto]
  | |- mono_cont (fun (x: ?X) => choice _ _) =>
      apply mono_cont_choice; [mono_cont_auto | mono_cont_auto]
  | |- mono_cont (fun (x: ?X) => match ?a with _ => _ end) =>
      destruct a; mono_cont_auto
  | |- mono_cont (fun (x: ?X) => Rec _) =>
      apply mono_cont_Rec; intro; mono_cont_auto
  | |- mono_cont (fun (x: ?X) => BW_fix _) =>
      apply mono_cont_BW_fix; intro; mono_cont_auto
  | |- mono_cont (bind _) =>
      apply mono_cont_bind; [mono_cont_auto | intro; mono_cont_auto]
  | |- mono_cont (fun (x: ?X) => ?f ?arg) =>
      first
        [ apply mono_cont_const
        | apply (mono_cont_at (fun x => f) arg); mono_cont_auto
        | fail 1 "mono_cont_auto: unsupported application" ]
  | |- mono_cont (fun (x: ?X) => ?body) =>
      first
        [ apply mono_cont_const
        | fail 1 "mono_cont_auto: unsupported term" body ]
  | |- ?goal => fail 1 "mono_cont_auto: unsupported goal" goal
  end.

Ltac unfold_rec :=
  lazymatch goal with
  | |- Rec ?f == ?rhs =>
      let Hmc := fresh "Hmono_cont" in
      assert (Hmc: mono_cont f) by
        (first [is_const f; unfold f; mono_cont_auto | mono_cont_auto]);
      transitivity (f (Rec f)); [exact (Rec_unfold f Hmc) |];
      clear Hmc
  | |- ?lhs == Rec ?f =>
      let Hmc := fresh "Hmono_cont" in
      assert (Hmc: mono_cont f) by
        (first [is_const f; unfold f; mono_cont_auto | mono_cont_auto]);
      transitivity (f (Rec f)); [| symmetry; exact (Rec_unfold f Hmc)];
      clear Hmc
  | |- ?goal => fail 1 "unfold_rec: expected a top-level Rec equivalence" goal
  end.

Ltac unfold_rec_in H :=
  lazymatch type of H with
  | Rec ?f == ?rhs =>
      let Hmc := fresh "Hmono_cont" in
      assert (Hmc: mono_cont f) by
        (first [is_const f; unfold f; mono_cont_auto | mono_cont_auto]);
      let Hnew := fresh H in
      assert (Hnew: f (Rec f) == rhs) by
        (transitivity (Rec f); [symmetry; exact (Rec_unfold f Hmc) | exact H]);
      clear H; rename Hnew into H;
      clear Hmc
  | ?lhs == Rec ?f =>
      let Hmc := fresh "Hmono_cont" in
      assert (Hmc: mono_cont f) by
        (first [is_const f; unfold f; mono_cont_auto | mono_cont_auto]);
      let Hnew := fresh H in
      assert (Hnew: lhs == f (Rec f)) by
        (transitivity (Rec f); [exact H | exact (Rec_unfold f Hmc)]);
      clear H; rename Hnew into H;
      clear Hmc
  | ?T => fail 1 "unfold_rec: expected a top-level Rec equivalence in" H ":" T
  end.

Tactic Notation "unfold_rec" "in" hyp(H) := unfold_rec_in H.

(*************************************************************************************************************)
(**********************************          while op for state monad        *********************************)
(**********************************                 program Σ A              *********************************)
(**********************************   1. while cond body :                   *********************************)
(**********************************            program Σ unit                *********************************)
(**********************************   2. whileret cond body :                *********************************)
(**********************************            A -> program Σ A              *********************************)
(**********************************   3. repeat_break body :                   *********************************)
(**********************************            A -> program Σ B              *********************************)
(*************************************************************************************************************)

Section  while_monad.

  Context {Σ: Type}.

  Definition while_f (cond: (program Σ bool))  (body : (program Σ unit)) 
                     (W : (program Σ unit)) 
                        : (program Σ unit) :=
  (x <- cond ;; (match x with 
  | true => body;; W
  | false => ret tt
  end)).

  Definition while (cond: (program Σ bool)) (body : program Σ unit)  := Rec (while_f cond body).

  Definition whileP_f (cond: Σ -> Prop)  (body : (program Σ unit)) 
                     (W : program Σ unit) 
                        : program Σ unit :=
  choice (assume cond;; body;; W) 
         (assume (fun s => ~ cond s);; ret tt).
  
  Definition whileP (cond: Σ -> Prop) (body : program Σ unit)  := Rec (whileP_f cond body).

  Definition whileret_f {A: Type}  (cond: A -> (program Σ bool)) (body : A -> (program Σ A)) 
                     (W :  A -> program Σ A) 
                        : A -> program Σ A :=
  fun a => (x <- (cond a) ;; match x with 
  | true =>  bind (body a) W
  | false => (ret a)
  end).

  Definition continue {A B: Type} (a: A): (program Σ (CntOrBrk A B)) := (ret (by_continue a)).
  Definition break {A B: Type} (b: B): (program Σ (CntOrBrk A B)) := (ret (by_break b)).

  Definition whileret {A: Type}  (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  := Rec (whileret_f cond body).

  Definition whileretP_f {A: Type}  (cond: A -> Σ -> Prop) (body : A -> (program Σ A))
                     (W :  A -> program Σ A)
                        : A -> program Σ A :=
  fun a =>
    choice (assume (fun s => cond a s);; a' <- body a;; W a')
           (assume (fun s => ~ cond a s);; ret a).

  Definition whileretP {A: Type}  (cond: A -> Σ -> Prop) (body : A -> (program Σ A))  := Rec (whileretP_f cond body).

  Definition repeat_break_f {A B: Type} (body: A -> program Σ (CntOrBrk A B)) (W: A -> program Σ B): A -> program Σ B :=
    fun a =>
      x <- body a;;
      match x with
      | by_continue a' => W a'
      | by_break b => ret b
      end.

  Definition repeat_break {A B: Type} (body: A -> program Σ (CntOrBrk A B)): A -> program Σ B :=
    Rec (repeat_break_f body).

  Definition repeat_break_f_noinput {B: Type} (body: program Σ (CntOrBrk unit B)) (W: program Σ B):  program Σ B :=
      x <- body ;;
      match x with
      | by_continue _ => W 
      | by_break b => ret b
      end.

  Definition repeat_break_noin {B: Type} (body: program Σ (CntOrBrk unit B)): program Σ B :=
    Rec (repeat_break_f_noinput body).

  Definition range_iter_f {A: Type} (hi: Z) (body: Z -> A -> program Σ A) (W: (Z * A) -> program Σ A): (Z * A) -> program Σ A :=
    fun '(lo, a0) => 
      choice
        (assume!! (lo < hi)%Z;;
         a1 <- body lo a0;;
         W ((lo + 1)%Z, a1))
        (assume!! (lo >= hi)%Z;;
         ret a0).

  Definition range_iter {A: Type} (lo hi: Z) (body: Z -> A -> program Σ A): A -> program Σ A :=
    fun a => Rec (range_iter_f hi body) (lo, a).

  Definition range_iter_break_f {A B: Type} (hi: Z) 
    (body: Z -> A -> program Σ (CntOrBrk A B)) 
    (W: Z * A -> program Σ (CntOrBrk A B)): 
      Z * A -> program Σ (CntOrBrk A B) :=
    fun '(lo, a0) => 
      choice
        (assume!! (lo < hi)%Z;;
         ab <- body lo a0;;
         match ab with
         | by_continue a1 => W ((lo + 1)%Z, a1)
         | by_break b => break b
         end)
        (assume!! (lo >= hi)%Z;;
         continue a0).

  Definition range_iter_break {A B: Type} (lo hi: Z) 
    (body: Z -> A -> program Σ (CntOrBrk A B)): 
      A -> program Σ (CntOrBrk A B) :=
    fun a => Rec (range_iter_break_f hi body) (lo, a).

  Definition forset_f {A: Type}
    (body: A -> program Σ unit)
    (W: (A -> Prop) -> program Σ unit) (universe: A -> Prop): program Σ unit :=
    choice (a <- get (fun _ a => a ∈ universe);;
            body a;;
            W (fun x => x ∈ universe /\ x <> a))
           (assume!! ((universe == ∅)%sets);;
            ret tt).

  Definition forset {A: Type}
    (universe: A -> Prop)
    (body: A -> program Σ unit): program Σ unit :=
    Rec (forset_f body) universe.

  Definition Repeat_f  (body : (program Σ unit))
                      (W : (program Σ unit))
                          : (program Σ unit) :=
    body ;; W.

  Definition Repeat (body : (program Σ unit))  := Rec (Repeat_f body).

  Fixpoint list_iter {Σ A B: Type}
    (body: A -> B -> program Σ B)
    (universe : list A) (b: B)
    : program Σ B :=
    match universe with
    | nil => ret b
    | cons a universe' =>
        b0 <- body a b;;
        list_iter body universe' b0
    end.

  Definition ret_some {A: Type} (a: option A): program Σ bool :=
    match a with 
    | Some _ => ret true
    | None => ret false
    end.

  Lemma while_unfold: forall (cond: (program Σ bool)) (body : program Σ unit), 
  while cond body == (x <- cond ;;
                      match x with
                      | true => body ;; (while cond body)
                      | false => ret tt
                      end).
  Proof.
    intros.
    unfold while.
    apply (BW_fixpoint' (while_f cond body)).
    unfold while_f.
    mono_cont_auto.
  Qed.

  Lemma whileP_unfold: forall (cond: Σ -> Prop) (body : program Σ unit), 
    whileP cond body == choice 
                         (assume cond;; body;; whileP cond body)
                         (assume (fun s => ~ cond s);; ret tt).
  Proof.
    intros.
    unfold while.
    apply (BW_fixpoint' (whileP_f cond body)).
    unfold whileP_f.
    mono_cont_auto.
  Qed.
  
  Lemma whileret_unfold: forall {A: Type} (cond: (A -> (program Σ bool))) (body : A -> (program Σ A)), 
    whileret cond body == fun a => (x <- (cond a);; 
                             match x with 
                             | true => y <- body a ;; whileret cond body y
                             | false => ret a
                             end).
  Proof.
    intros.
    unfold whileret.
    apply (BW_fixpoint' (whileret_f cond body)).
    unfold whileret_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_unfold {A B: Type}:
    forall (body: A -> program Σ (CntOrBrk A B)),
    repeat_break body == fun a =>
                        x <- body a;; 
                        match x with
                        | by_continue a0 => repeat_break body a0
                        | by_break b0 => ret b0
                        end.
  Proof.
    intros.
    unfold repeat_break.
    apply (BW_fixpoint' (repeat_break_f body)).
    unfold repeat_break_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_noin_unfold {B: Type}:
    forall (body: program Σ (CntOrBrk unit B)),
    repeat_break_noin body == 
                        x <- body;; 
                        match x with
                        | by_continue _ => repeat_break_noin body
                        | by_break b0 => ret b0
                        end.
  Proof.
    intros.
    unfold repeat_break.
    apply (BW_fixpoint' (repeat_break_f_noinput body)).
    unfold repeat_break_f_noinput.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold_aux:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A),
    (fun '(lo, a) => range_iter lo hi body a) ==
    fun '(lo, a) => choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (assume!! (lo >= hi)%Z;;
      ret a).
  Proof.
    intros. unfold range_iter.
    assert ((fun '(lo, a) => BW_fix (range_iter_f hi body) (lo, a))
      == BW_fix (range_iter_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (BW_fixpoint' (range_iter_f hi body)).
    unfold range_iter_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A) lo a,
    range_iter lo hi body a ==
    choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (assume!! (lo >= hi)%Z;;
      ret a).
  Proof.
    intros.
    pose proof (range_iter_unfold_aux hi body).
    unfold equiv in H; simpl in H.
    unfold Equiv_lift, LiftConstructors.lift_rel2 in H.
    specialize (H (lo, a)).
    auto.
Qed.

  Lemma range_iter_break_unfold_aux:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (CntOrBrk A B)),
    (fun '(lo, a) => range_iter_break lo hi body a) ==
    fun '(lo, a) => choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | by_continue a' => range_iter_break (lo + 1)%Z hi body a'
      | by_break b' => break b'
      end)
      (assume!! (lo >= hi)%Z;;
      continue a).
  Proof.
    intros. unfold range_iter_break.
    assert ((fun '(lo, a) => BW_fix (range_iter_break_f hi body) (lo, a))
      == BW_fix (range_iter_break_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (BW_fixpoint' (range_iter_break_f hi body)).
    unfold range_iter_break_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_break_unfold:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (CntOrBrk A B)) lo a,
    range_iter_break lo hi body a ==
    choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | by_continue al => range_iter_break (lo + 1)%Z hi body al
      | by_break br => break br
      end)
      (assume!! (lo >= hi)%Z;;
      continue a).
  Proof.
    intros.
    pose proof (range_iter_break_unfold_aux hi body).
    unfold equiv in H; simpl in H.
    unfold Equiv_lift, LiftConstructors.lift_rel2 in H.
    specialize (H (lo, a)).
    auto.
  Qed.

  Lemma forset_unfold_aux {A: Type}
    (body: A -> program Σ unit):
    BW_fix (forset_f body) == fun universe =>
    choice (a <- get (fun _ a => a ∈ universe);;
            body a;;
            forset (fun x => x ∈ universe /\ x <> a) body)
           (assume!! ((universe == ∅)%sets);;
            ret tt).
  Proof.
    apply (BW_fixpoint' (forset_f body)).
    unfold forset_f.
    mono_cont_auto.
  Qed.

  Lemma forset_unfold {A: Type}
    (universe: A -> Prop)
    (body: A -> program Σ unit):
    forset universe body ==
    choice (a <- get (fun _ a => a ∈ universe);;
            body a;;
            forset (fun x => universe x /\ x <> a) body)
           (assume!! ((universe == ∅)%sets);;
            ret tt).
  Proof.
    unfold forset.
    pose proof (forset_unfold_aux body).
    apply H.
  Qed.

  Lemma list_iter_nil_unfold {A B: Type}
    (body: A -> B -> program Σ B) b:
    list_iter body nil b == ret b.
  Proof.
    reflexivity.
  Qed.

  Lemma list_iter_cons_unfold {A B: Type}
    (a: A) (universe: list A) (body: A -> B -> program Σ B) b:
    list_iter body (a :: universe) b ==
      b0 <- body a b;; list_iter body universe b0.
  Proof.
    reflexivity.
  Qed.

End  while_monad.

Ltac unfold_loop:=
  rewrite ?(while_unfold _ _) ;
  rewrite ?(whileP_unfold _ _) ;
  rewrite ?(whileret_unfold _ _ _) ;
  rewrite ?(repeat_break_unfold _ _) ;
  rewrite ?(repeat_break_noin_unfold _) ;
  rewrite ?(range_iter_unfold _ _ _ _) ;
  rewrite ?(range_iter_break_unfold _ _ _ _) ;
  rewrite ?(forset_unfold _ _) .

Ltac unfold_loop_in H :=
  rewrite ?(while_unfold _ _) in H;
  rewrite ?(whileP_unfold _ _) in H;
  rewrite ?(whileret_unfold _ _ _) in H;
  rewrite ?(repeat_break_unfold _ _) in H;
  rewrite ?(repeat_break_noin_unfold _) in H;
  rewrite ?(range_iter_unfold _ _ _ _) in H;
  rewrite ?(range_iter_break_unfold _ _ _ _) in H;
  rewrite ?(forset_unfold _ _) in H.


Tactic Notation "unfold_loop" "in" hyp(H) :=
  unfold_loop_in H.

(*************************************************************************************************************)
(*****    Pseudocode notation: write a whole abstract program inline, no auxiliary definitions      ******)
(*************************************************************************************************************)
(*                                                                                                          *)
(*  This is the error-monad twin of StateRelMonad's [prog_scope].  Open [progerr_scope] to write            *)
(*  error-monad programs as inline pseudocode -- blocks are self-delimiting keywords, so they nest and      *)
(*  chain with [;;] without extra parentheses or intermediate [Definition]s:                                 *)
(*                                                                                                          *)
(*      UPDATE s := f s ;;                     -- state update  (update' (fun s => f s))                     *)
(*      WHILE s , P s DO ... END ;;            -- pre-tested loop   (whileP)                                 *)
(*      IF s , P s THEN c1 ELSE c2 FI          -- two-armed choice  (if_else)                                *)
(*      WHEN s , P s THEN c END                -- one-armed guard   (If)                                     *)
(*      FOR i FROM lo TO hi DO c END           -- counted loop over [lo, hi)   (range_iter)                  *)
(*      LOOP ... BREAK v ... CONTINUE ... END  -- break/continue loop   (repeat_break_noin)                  *)
(*      CHOOSE { c1 | c2 | c3 }                -- nondeterministic choice, one branch per | (choice)         *)
(*                                                                                                          *)
(*  Every construct that inspects the state binds it under the fixed name [s]: a guard [s , P] expands to     *)
(*  the predicate [fun s => P : Σ -> Prop].  The loop index [i] of FOR is a [Z] bound in the body.            *)
(*                                                                                                          *)

Declare Scope progerr_scope.
Delimit Scope progerr_scope with progerr.

Notation "'UPDATE' s ':=' e" :=
  (update' (fun s => e))
  (at level 50, s ident,
   format "'UPDATE'  s  ':='  e") : progerr_scope.

(* Multi-branch nondeterministic choice, one branch per [|] inside braces.  Each arity expands
   directly to nested [choice] (no auxiliary function, no trailing empty program):
   [CHOOSE { a | b | c }] *is* [choice a (choice b c)].  Supported for 2..6 branches. *)
Notation "'CHOOSE' '{' c1 '|' c2 '}'" :=
  (choice c1 c2)
  (at level 0, c1 at level 200, c2 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '}' ']'") : progerr_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '}'" :=
  (choice c1 (choice c2 c3))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '}' ']'") : progerr_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '}'" :=
  (choice c1 (choice c2 (choice c3 c4)))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '}' ']'") : progerr_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '|' c5 '}'" :=
  (choice c1 (choice c2 (choice c3 (choice c4 c5))))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200, c5 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '|'  c5 '//' '}' ']'") : progerr_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '|' c5 '|' c6 '}'" :=
  (choice c1 (choice c2 (choice c3 (choice c4 (choice c5 c6)))))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200, c5 at level 200, c6 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '|'  c5 '//' '|'  c6 '//' '}' ']'") : progerr_scope.

Notation "'IF' s ',' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (if_else (fun s => b) c1 c2)
  (at level 0, s ident, b at level 99, c1 at level 200, c2 at level 200,
   format "'[v' 'IF'  s ','  b  'THEN' '//' c1 '//' 'ELSE' '//' c2 '//' 'FI' ']'") : progerr_scope.

Notation "'WHEN' s ',' b 'THEN' c 'END'" :=
  (If (fun s => b) c)
  (at level 0, s ident, b at level 99, c at level 200,
   format "'[v' 'WHEN'  s ','  b  'THEN' '//' c '//' 'END' ']'") : progerr_scope.

Notation "'WHILE' s ',' b 'DO' c 'END'" :=
  (whileP (fun s => b) c)
  (at level 0, s ident, b at level 99, c at level 200,
   format "'[v' 'WHILE'  s ','  b  'DO' '//' c '//' 'END' ']'") : progerr_scope.

Notation "'FOR' i 'FROM' lo 'TO' hi 'DO' c 'END'" :=
  (range_iter lo hi (fun i _ => c) tt)
  (at level 0, i ident, lo at level 99, hi at level 99, c at level 200,
   format "'[v' 'FOR'  i  'FROM'  lo  'TO'  hi  'DO' '//' c '//' 'END' ']'") : progerr_scope.

Notation "'LOOP' c 'END'" :=
  (repeat_break_noin c)
  (at level 0, c at level 200,
   format "'[v' 'LOOP' '//' c '//' 'END' ']'") : progerr_scope.

(* Accumulator-carrying loop: [p] is the loop variable, [a0] its initial value; the body
   ends each round with [NEXT a'] to loop with [a'] or [BREAK b] to exit with result [b]. *)
Notation "'REPEAT' ' p 'FROM' a0 'DO' c 'END'" :=
  (repeat_break (fun p => c) a0)
  (at level 0, p strict pattern, a0 at level 99, c at level 200,
   format "'[v' 'REPEAT'  ' p  'FROM'  a0  'DO' '//' c '//' 'END' ']'") : progerr_scope.

Notation "'BREAK' e" := (break e) (at level 50) : progerr_scope.
Notation "'NEXT' a" := (continue a) (at level 50) : progerr_scope.
Notation "'CONTINUE'" := (continue tt) (at level 0) : progerr_scope.
