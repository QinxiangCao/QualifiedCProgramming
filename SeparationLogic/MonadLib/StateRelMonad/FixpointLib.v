Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From FP Require Import SetsFixedpoints PartialOrder_Setoid.
Require Import StateRelBasic. 
Import Monad MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Section mono_and_continuous_lemmas.

  Definition increasing {A: Type} {_SETS_A : Sets.SETS A} (T : nat -> A):= @sseq_mono A _SETS_A T.
  Definition mono {A: Type} {_SETS_A : Sets.SETS A}  {B: Type} {_SETS_B : Sets.SETS B}  
    (f : A -> B) := Proper (Sets.included ==> Sets.included) f.
  Definition continuous {A: Type} {_SETS_A : Sets.SETS A} {B: Type} {_SETS_B : Sets.SETS B} 
    (f : A -> B) := @sseq_continuous  A _SETS_A B _SETS_B f.
  Definition mono_cont {A: Type} {_SETS_A : Sets.SETS A} {B: Type} {_SETS_B : Sets.SETS B} 
    (f : A -> B) := mono f /\ continuous f.
  
  Lemma Lfix_fixpoint'{A} {_SETS_A: Sets.SETS A} {_SETS_Properties_A: SETS_Properties A}: 
    forall f,
      mono_cont f -> Lfix f == f (Lfix f).
  Proof.
    intros.
    hnf in H.
    apply Lfix_fixpoint; tauto.
  Qed.

  Lemma mono_Lfix {A B: Type} {_SETS_A: Sets.SETS A} {_SETS_B: Sets.SETS B} 
    {_SETS_PROP_A: SETS_Properties A} {_SETS_PROP_B: SETS_Properties B}:
    forall (f: A -> B -> B),
      (forall a, mono (f a)) ->
      (forall b, mono (fun W => f W b)) ->
      mono (fun W => (Lfix (f W))).
  Proof.
    unfold mono.
    unfold Proper, respectful.
    intros; apply Lfix_mono.
    - unfold Proper, respectful.
      intros; apply H; auto.
    - intros. apply H0; auto.
  Qed.
  
Lemma Lfix_seq_cont_general {A B} {SET_A: Sets.SETS A} {PROP_A: SETS_Properties A}
                          {SET_B: Sets.SETS B} {PROP_B: SETS_Properties B}:
forall (f: A -> B -> B)
        (Hf_mono: Proper (Sets.included ==> Sets.included ==> Sets.included) f)
        (Hfa_sseq: forall a, sseq_continuous (f a))
        (Hf_sseq: forall b, sseq_continuous (fun a => f a b)),
  sseq_continuous (fun a: A => Lfix (f a)).
Proof.
  intros. intros until 1. apply Sets_equiv_Sets_included. split.
  - apply Sets_indexed_union_included. intros n. induction n.
    + simpl. apply Sets_empty_included.
    + simpl. rewrite IHn. erewrite Hf_sseq;auto.
      apply Sets_indexed_union_included. intros m.
      erewrite Hfa_sseq.
      apply Sets_indexed_union_included. intros k.
      set(mk:= max m k). assert (Hk: T k ⊆ T mk).
      { apply sseq_mono_nat_le;auto. apply Nat.le_max_r. }
      assert (Hm: T m ⊆ T mk).
      { apply sseq_mono_nat_le;auto. apply Nat.le_max_l. }
      rewrite <- (Sets_included_indexed_union mk).
      rewrite (Lfix_fixpoint (f (T mk))).
      apply Hf_mono;auto. 
      apply Lfix_mono. apply Hf_mono. reflexivity.
      intros. apply Hf_mono;auto. reflexivity.
      apply Hf_mono. reflexivity. apply Hfa_sseq.
      unfold sseq_mono. intros. 
      apply Lfix_mono. apply Hf_mono. reflexivity.
      intros. apply Hf_mono;auto. reflexivity.
  - apply Sets_indexed_union_included. intros.
    apply Lfix_mono. apply Hf_mono;auto. reflexivity.
    intros. apply Hf_mono. rewrite <- (Sets_included_indexed_union (S n)).
    auto. reflexivity.
Qed.

  Context {Σ: Type}.

  Lemma increasing_mono_increasing:
  forall {A B: Type} {_SETS_A : Sets.SETS A}  {_SETS_B : Sets.SETS B}
         (f: A -> B)
         (l: nat -> A),
    increasing l -> mono f -> increasing (fun n => f (l n)).
  Proof.
    intros.
    unfold increasing, sseq_mono. intros.
    apply H0. apply H.
  Qed.

  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    increasing c -> c n ⊆ c (n + m).
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
    n <= m -> increasing c -> c n ⊆ c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus;auto.
  Qed.

  Lemma increasing_program_plus' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    increasing c -> c n ⊆ c (n + m).
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
    n <= m -> increasing c -> c n ⊆ c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus';auto.
  Qed.
  
  Lemma mono_intro {X I Y: Type}
    {_SETS_X: Sets.SETS X} {_SETS_Y: Sets.SETS Y}:
    forall (f: X -> I -> Y),
      (forall i, mono (fun x => f x i)) ->
      mono f.
  Proof.
    unfold mono, Proper, respectful.
    sets_unfold; intros.
    eapply H; eauto.
  Qed.

  Lemma mono_bind {X C D: Type} {_SETS_X: Sets.SETS X}:
    forall (c1: X -> program Σ D) (c2: X -> D -> program Σ C),
      mono c1 ->
      (forall d, mono (fun x => c2 x d)) ->
      mono (fun x => bind (c1 x) (c2 x)).
  Proof.
    unfold mono.
    unfold Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    destruct H2 as [d [s2 [H2 H3]]].
    exists d, s2.
    split; auto.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma mono_bind' {B C D: Type}:
    forall  (c1: (program Σ B) -> program Σ D) (c2: (program Σ B) -> D -> program Σ C),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    intros. apply mono_bind; auto.
  Qed.

  Lemma mono_choice {X D: Type} {_SETS_X: Sets.SETS X}:
    forall (c1 c2: X -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun x => choice (c1 x) (c2 x)).
  Proof.
    unfold mono, Proper, respectful, choice.
    sets_unfold.
    intros.
    destruct H2.
    - left. eapply H; eauto.
    - right. eapply H0; eauto.
  Qed.

  Lemma mono_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    intros. apply mono_choice; auto.
  Qed.

  Lemma continuous_intro {X I Y: Type}
    {_SETS_X: Sets.SETS X} {_SETS_Y: Sets.SETS Y}:
    forall (f: X -> I -> Y),
      (forall i, continuous (fun x => f x i)) ->
      continuous f.
  Proof.
    unfold continuous, sseq_continuous, sseq_mono.
    sets_unfold; intros.
    eapply H; eauto.
  Qed.

  Lemma continuous_const {X Y: Type}
    {_SETS_X: Sets.SETS X} {_SETS_Y: Sets.SETS Y}
    {_SETS_Properties_Y: SETS_Properties Y}:
    forall (y: Y),
      continuous (fun (_: X) => y).
  Proof.
    intros y T HT. apply omega_union_const.
  Qed.

  Lemma continuous_const' {B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: program Σ B) => f).
  Proof.
    intros. apply continuous_const.
  Qed.

  Lemma continuous_bind {X C D: Type}
    {_SETS_X: Sets.SETS X} {_SETS_Properties_X: SETS_Properties X}:
    forall (c1: X -> program Σ D) (c2: X -> D -> program Σ C),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun x => c2 x d)) ->
      (forall d, continuous (fun x => c2 x d)) ->
      continuous (fun x => bind (c1 x) (c2 x)).
  Proof.
    unfold mono, continuous, sseq_continuous, Proper, respectful.
    unfold_monad.
    sets_unfold.
    intros.
    split; intros.
    - destruct H4 as [d [s2 [H4 H5]]].
      apply H0 in H4; eauto.
      apply H2 in H5; eauto.
      clear H0 H2.
      destruct H4 as [i1 H4].
      destruct H5 as [i2 H5].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s2.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        eapply sseq_mono_nat_le; eauto.
      + apply leb_complete_conv in Heq.
        exists i1, d, s2.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        eapply sseq_mono_nat_le; eauto; lia.
    - destruct H4 as [i [d [s2 [H4 H5]]]].
      exists d, s2.
      split.
      + apply H0; auto.
        exists i; auto.
      + apply H2; auto.
        exists i; auto.
  Qed.

  Lemma continuous_bind' {B C D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ C),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    intros. apply continuous_bind; auto.
  Qed.

  Lemma continuous_choice {X D: Type} {_SETS_X: Sets.SETS X}:
    forall (c1 c2: X -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun x => choice (c1 x) (c2 x)).
  Proof.
    unfold continuous, sseq_continuous.
    unfold choice; sets_unfold; intros.
    split; intros.
    - destruct H2.
      + apply H in H2; auto.
        destruct H2.
        exists x; tauto.
      + apply H0 in H2; auto.
        destruct H2.
        exists x; tauto.
    - destruct H2 as [i [H2 | H2]].
      + left; apply H; auto.
        exists i; auto.
      + right; apply H0; auto.
        exists i; auto.
  Qed.

  Lemma continuous_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    intros. apply continuous_choice; auto.
  Qed.

  Lemma mono_cont_pointwise {X I Y: Type}
    {_SETS_X: Sets.SETS X} {_SETS_Y: Sets.SETS Y}:
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
    {_SETS_X: Sets.SETS X} {_SETS_Y: Sets.SETS Y}:
    forall (f: X -> I -> Y) (i: I),
      mono_cont f ->
      mono_cont (fun x => f x i).
  Proof.
    intros f i [Hmono Hcont]. split.
    - unfold mono, Proper, respectful.
      intros x1 x2 Hx.
      assert (Hinc : f x1 ⊆ f x2) by (apply Hmono; assumption).
      sets_unfold. sets_unfold in Hinc. apply Hinc.
    - unfold continuous, sseq_continuous.
      intros T HT. cbv beta.
      assert (Heq : f (⋃ T) == ⋃ (fun n => f (T n))) by
        (apply Hcont; assumption).
      sets_unfold. sets_unfold in Heq. apply Heq.
  Qed.

  Lemma mono_cont_id {X: Type}
    {_SETS_X: Sets.SETS X} {_SETS_Properties_X: SETS_Properties X}:
    mono_cont (fun x: X => x).
  Proof.
    split.
    - unfold mono, Proper, respectful. intros; assumption.
    - unfold continuous, sseq_continuous. intros; reflexivity.
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
    {_SETS_X: Sets.SETS X} {_SETS_Y: Sets.SETS Y}
    {_SETS_Properties_Y: SETS_Properties Y}:
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
    {_SETS_X: Sets.SETS X} {_SETS_Properties_X: SETS_Properties X}:
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

  Lemma mono_cont_choice {X D: Type} {_SETS_X: Sets.SETS X}:
    forall (c1 c2: X -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun x => choice (c1 x) (c2 x)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice; tauto.
    - apply continuous_choice; tauto.
  Qed.

  Lemma mono_cont_choice' {B D: Type}:
    forall (c1 c2: (program Σ B) -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    intros. apply mono_cont_choice; auto.
  Qed.

  Lemma mono_cont_Lfix {A B: Type} {_SETS_A: Sets.SETS A} {_SETS_B: Sets.SETS B}
    {_SETS_Properties_A: SETS_Properties A} {_SETS_Properties_B: SETS_Properties B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun W => f W b)) ->
      mono_cont (fun W => Lfix (f W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_Lfix; intros.
      apply H. apply H0.
    - apply Lfix_seq_cont_general; intros.
      unfold Proper, respectful.
      intros.
      etransitivity.
      apply H; eauto.
      apply H0; auto.
      apply H. apply H0.
  Qed.

  Lemma Rec_unfold {X: Type} {_SETS_X: Sets.SETS X}
    {_SETS_Properties_X: SETS_Properties X}:
    forall (f: X -> X),
      mono_cont f -> Rec f == f (Rec f).
  Proof.
    intros. unfold Rec. apply Lfix_fixpoint'. assumption.
  Qed.

  Lemma Rec_mono {A B: Type} {_SETS_A: Sets.SETS A} {_SETS_B: Sets.SETS B}
    {_SETS_Properties_A: SETS_Properties A} {_SETS_Properties_B: SETS_Properties B}:
    forall (f: A -> B -> B),
      (forall a, mono (f a)) ->
      (forall b, mono (fun x => f x b)) ->
      mono (fun x => Rec (f x)).
  Proof.
    intros. unfold Rec. apply mono_Lfix; assumption.
  Qed.

  Lemma Rec_continuous {A B: Type} {_SETS_A: Sets.SETS A} {_SETS_B: Sets.SETS B}
    {_SETS_Properties_A: SETS_Properties A} {_SETS_Properties_B: SETS_Properties B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun x => f x b)) ->
      continuous (fun x => Rec (f x)).
  Proof.
    intros. unfold Rec.
    destruct (mono_cont_Lfix f H H0). assumption.
  Qed.

  Lemma mono_cont_Rec {A B: Type} {_SETS_A: Sets.SETS A} {_SETS_B: Sets.SETS B}
    {_SETS_Properties_A: SETS_Properties A} {_SETS_Properties_B: SETS_Properties B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun x => f x b)) ->
      mono_cont (fun x => Rec (f x)).
  Proof.
    intros. unfold Rec. apply mono_cont_Lfix; assumption.
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
  | |- mono_cont (fun (x: ?X) => Lfix _) =>
      apply mono_cont_Lfix; intro; mono_cont_auto
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

Section loop_unfold.
Context {Σ: Type}.

  Lemma whileb_unfold: forall (cond: (program Σ bool)) (body : program Σ unit), 
  while cond body == (x <- cond ;;
                      match x with
                      | true => body ;; (while cond body)
                      | false => ret tt
                      end).
  Proof.
    intros.
    unfold while.
    apply (Lfix_fixpoint' (while_f cond body)).
    unfold while_f.
    mono_cont_auto.
  Qed.

  Lemma whileretb_unfold: forall {A: Type} (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  (a: A), 
      whileret cond body == fun a => (x <- (cond a);; 
                              match x with 
                              | true => y <- body a ;; whileret cond body y
                              | false => ret a
                              end).
  Proof.
    intros.
    unfold whileret.
    apply (Lfix_fixpoint' (whileret_f cond body)).
    unfold whileret_f.
    mono_cont_auto.
  Qed.

  Lemma while_unfold: forall (cond: Σ -> Prop) (body : program Σ unit), 
    whileP cond body == choice 
                         (assume cond;; body;; whileP cond body)
                         (assume (fun s => ~ cond s);; ret tt).
  Proof.
    intros.
    unfold whileP.
    apply (Lfix_fixpoint' (whileP_f cond body)).
    unfold whileP_f.
    mono_cont_auto.
  Qed.

  Lemma whileret_unfold: forall {A: Type} (cond: A -> Σ -> Prop) (body : A -> (program Σ A)), 
    whileretP cond body == 
    fun a => 
      choice (assume (fun s => cond a s);; a' <- body a;; whileretP cond body a') 
             (assume (fun s => ~ cond a s);; ret a).
  Proof.
    intros.
    unfold whileretP.
    apply (Lfix_fixpoint' (whileretP_f cond body)).
    unfold whileretP_f.
    mono_cont_auto.
  Qed.

  Lemma Repeat_unfold (body : (program Σ unit)):
    Repeat body == (body;; Repeat body).
  Proof.
    unfold Repeat, Repeat_f.
    apply (Lfix_fixpoint' (Repeat_f body)).
    unfold Repeat_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_unfold:
    forall {A B} (body: A -> program Σ (CntOrBrk A B)),
    repeat_break body == fun a =>
                         x <- body a;; 
                         match x with
                         | by_continue a0 => repeat_break body a0
                         | by_break b0 => ret b0
                         end.
  Proof.
    intros.
    unfold repeat_break.
    apply (Lfix_fixpoint' (repeat_break_f body)).
    unfold repeat_break_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_noin_unfold:
    forall {B} (body: program Σ (CntOrBrk unit B)),
    repeat_break_noin body ==
      x <- body;;
      match x with
      | by_continue _ => repeat_break_noin body
      | by_break b0 => ret b0
      end.
  Proof.
    intros.
    unfold repeat_break_noin.
    apply (Lfix_fixpoint' (repeat_break_f_noinput body)).
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
    assert ((fun '(lo, a) => Lfix (range_iter_f hi body) (lo, a))
      == Lfix (range_iter_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (Lfix_fixpoint' (range_iter_f hi body)).
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
    hnf in H.
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
    assert ((fun '(lo, a) => Lfix (range_iter_break_f hi body) (lo, a))
      == Lfix (range_iter_break_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (Lfix_fixpoint' (range_iter_break_f hi body)).
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
    hnf in H.
    specialize (H (lo, a)).
    auto.
  Qed.

  Lemma forset_unfold_aux {A: Type}
    (body: A -> program Σ unit):
    Lfix (forset_f body) == fun universe =>
    choice (a <- get (fun _ a => a ∈ universe);; 
            body a;;
            forset (fun x => x ∈ universe /\ x <> a) body)
           (assume!! (universe == ∅);;
            ret tt).
  Proof.
    apply (Lfix_fixpoint' (forset_f body)).
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
           (assume!! (universe == ∅);;
            ret tt).
  Proof.
    unfold forset.
    pose proof (forset_unfold_aux body).
    apply H.
  Qed.

End loop_unfold.

Ltac unfold_loop:=
  rewrite ?(whileb_unfold _ _) ;
  rewrite ?(whileretb_unfold _ _ _) ;
  rewrite ?(while_unfold _ _) ;
  rewrite ?(whileret_unfold _ _ _) ;
  rewrite ?(Repeat_unfold _) ;
  rewrite ?(repeat_break_unfold _ _) ;
  rewrite ?(forset_unfold _ _) .

Ltac unfold_loop_in H :=
  rewrite ?(whileb_unfold _ _) in H;
  rewrite ?(whileretb_unfold _ _ _) in H;
  rewrite ?(while_unfold _ _) in H;
  rewrite ?(whileret_unfold _ _ _) in H;
  rewrite ?(Repeat_unfold _) in H;
  rewrite ?(repeat_break_unfold _ _) in H;
  rewrite ?(forset_unfold _ _) in H.


Tactic Notation "unfold_loop" "in" hyp(H) :=
  unfold_loop_in H.
