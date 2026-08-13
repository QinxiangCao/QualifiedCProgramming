(*************************************************)
(** Proof of the Bourbaki-Witt Fixpoint Theorem **)
(*************************************************)

(** This file and PartialOrder_Setoid.v is based on a course project of Shanghai
    Jiao Tong University, CS263 2020 spring, developed by Xinyi Wan and Zimeng
    Huang. Qinxiang Cao editted this file and add more theorems to it later. *)

    Require Import ClassicalFacts.
    Require Import Coq.Logic.Classical_Prop.
    Require Import Coq.micromega.Psatz.
    Require Import Coq.Classes.Morphisms.
    Require Import Coq.Classes.Equivalence.
    Require Import Coq.Classes.RelationPairs.
    Require Import SetsClass.SetsDomain.
    Require Import FP.PartialOrder_Setoid.
    Require Import FP.LiftConstructors.
    
    Local Open Scope order_scope.
    (* 基本定义*)
    (**************************************)
    
    Definition seq_upper_bound
                 {A: Type} {RA: Order A}
                 (T: nat -> A) (bnd: A): Prop :=
      forall n, T n <= bnd.
    (*检查bnd是否是一个无穷序列的上界*)
    
    Definition seq_least_upper_bound
                 {A: Type} {RA: Order A}
                 (T: nat -> A) (bnd: A): Prop :=
      seq_upper_bound T bnd /\
      forall bnd', seq_upper_bound T bnd' -> bnd <= bnd'.
    (*一个无穷序列的上确界*)
    
    Definition least_element {A: Type} {RA: Order A} (bot:A): Prop:=
      forall a, bot <= a.
    (* 集合的最小元 *)
    
    Definition seq_mono {A: Type} {RA: Order A} (T: nat -> A): Prop :=
      forall n, T n <= T (S n).
    (** 序列单调递增 *)

    Class OmegaLub (A: Type): Type :=
      omega_lub: (nat -> A) -> A.
    
    Class Bot (A: Type): Type :=
      bot: A.
    
    Class CompletePartialOrder_Setoid
            (A: Type)
            {RA: Order A} {EA: Equiv A}
            {oLubA: OmegaLub A} {BotA: Bot A}: Prop :=
    {
      CPO_PartialOrder: PartialOrder_Setoid A;
      CPO_SeqCont: forall T, seq_mono T -> seq_least_upper_bound T (omega_lub T);
      CPO_least: least_element bot;
    }.
    
    Class CompletePartialOrder_Strong_Setoid
            (A: Type)
            {RA: Order A} {EA: Equiv A}
            {oLubA: OmegaLub A} {BotA: Bot A}: Prop :=
    {
      CPOs_CompletePartialOrder: CompletePartialOrder_Setoid A;
      CPOs_SeqCont: forall T, seq_least_upper_bound T (omega_lub T)
    }.

    Definition limit_congr {A: Type} {EA: Equiv A} (oLubA: OmegaLub A): Prop :=
      forall (T1 T2: nat -> A), (forall n, T1 n == T2 n) ->
      omega_lub T1 == omega_lub T2.

    #[export] Existing Instance CPO_PartialOrder.
    
    Definition seq_continuous
                 {A: Type} {RA: Order A} {oLubA: OmegaLub A}
                 {B: Type} {EB: Equiv B} {oLubB: OmegaLub B}
                 (f: A -> B): Prop :=
      forall T: nat -> A,
        seq_mono T ->
        f (omega_lub T) == omega_lub (fun n => f (T n)).
    (* 函数连续性 *)
    
    Definition BW_fix
                 {A: Type} {oLubA: OmegaLub A} {BotA: Bot A}
                 (f: A -> A): A :=
      omega_lub (fun n => Nat.iter n f bot).
    
    (* 基本定义结束*)
    (**************************************)
    
    (* 基本引理与证明指令 *)
    (**************************************)
    
    Lemma limit_smaller_iff:
      forall {A: Type} `{CPO: CompletePartialOrder_Setoid A} xs y,
        seq_mono xs ->
        (omega_lub xs <= y <-> forall n, xs n <= y).
    Proof.
      intros.
      split; intros.
      + rewrite <- H0.
        destruct (CPO_SeqCont xs); auto.
      + destruct (CPO_SeqCont xs); auto.
    Qed.
    
    Lemma limit_greater:
      forall {A: Type} `{CPO: CompletePartialOrder_Setoid A} xs y,
        seq_mono xs ->
        (exists n, y <= xs n) ->
        y <= omega_lub xs.
    Proof.
      intros.
      destruct H0 as [n ?].
      rewrite H0.
      destruct (CPO_SeqCont xs); auto.
    Qed.
    
    Theorem limit_mono:
      forall {A: Type}
             {RA: Order A} {EA: Equiv A}
             {oLubA: OmegaLub A} {BotA: Bot A}
             {equ: Equivalence equiv}
             {CPO: CompletePartialOrder_Setoid A},
      forall T1 T2,
        seq_mono T1 ->
        seq_mono T2 ->
        lift_rel2 order_rel T1 T2 ->
        omega_lub T1 <= omega_lub T2.
    Proof.
      intros.
      apply limit_smaller_iff; auto.
      intros.
      apply limit_greater; auto.
      exists n; auto.
    Qed.

    Lemma CPOs_limit_congr: 
      forall {A: Type}
             {RA: Order A} {EA: Equiv A}
             {oLubA: OmegaLub A} {BotA: Bot A}
             {equ: Equivalence equiv}
             {CPOs: CompletePartialOrder_Strong_Setoid A},
      limit_congr oLubA.
    Proof.
      intros;hnf;intros.
      pose proof CPOs.(CPOs_CompletePartialOrder) as CPO.
      apply PO_AntiSymmetric_Setoid.
      - apply CPOs.(CPOs_SeqCont).
        intros n;rewrite (H n).
        apply CPOs.(CPOs_SeqCont).
      - apply CPOs.(CPOs_SeqCont).
        intros n;rewrite <- (H n).
        apply CPOs.(CPOs_SeqCont).
    Qed.

    (*Module OrderTac.*)
    
    Ltac solve_order R (*test_bot test_limit test_Proper1 test_Proper2*) :=
      match goal with
      | H: R ?x ?y |- R ?x ?y =>
          exact H
      | |- R ?x ?x =>
          reflexivity
      | CPO: CompletePartialOrder_Setoid _ |- ?bot <= _ =>
          apply CPO_least
      | CPO: CompletePartialOrder_Setoid _ |- omega_lub ?xs <= omega_lub ?ys =>
          solve [ apply limit_mono;
                    [ solve_seq_mono R
                    | solve_seq_mono R
                    | unfold lift_rel2;
                      let n := fresh "n" in
                      intros n;
                      solve_order_ind R n
                    ]
                ]
      | CPO: CompletePartialOrder_Setoid _ |- omega_lub ?xs <= ?y =>
          let H := fresh "H" in
          assert (seq_mono xs) as H;
          [ solve_seq_mono R
          | apply (proj2 (@limit_smaller_iff _ _ _ _ _ CPO xs y H));
            let n := fresh "n" in
            intros n;
            clear H;
            solve_order_ind R n
          ]
      | CPO: CompletePartialOrder_Setoid _, H: ?x == ?y |- ?x <= ?y =>
          apply PO_Reflexive_Setoid, H
      | CPO: CompletePartialOrder_Setoid _, H: ?y == ?x |- ?x <= ?y =>
          apply PO_Reflexive_Setoid; symmetry; apply H
      | HP1: Proper (?RB ==> R) ?f |- R (?f _) (?f _) =>
          apply HP1; solve_order RB
      | HP2: Proper (?RB1 ==> ?RB2 ==> R) ?f |- R (?f _ _) (?f _ _) =>
          apply HP2; [solve_order RB1 | solve_order RB2]
      | HP3: Proper (?RB1 ==> ?RB2 ==> ?RB3 ==> R) ?f |- R (?f _ _ _) (?f _ _ _) =>
          apply HP3; [solve_order RB1 | solve_order RB2 | solve_order RB3]
      | Hsm: seq_mono ?xs |- ?xs ?n <= ?xs (S ?n) =>
          exact (Hsm n)
      | Hsb: seq_upper_bound ?xs ?y |- R (?xs ?n) ?y =>
          exact (Hsb n)
      | |- _ => auto
      end
    with solve_order_ind R n :=
      first
        [ progress (solve_order R)
        | solve
            [ let IH := fresh "IH" n in
              induction n as [| n IH]; [simpl | simpl in IH |- *]; solve_order R
            ]
        | idtac
        ]
    with solve_seq_mono R :=
      match goal with
      | |- seq_mono ?xs =>
          let n := fresh "n" in
          intros n;
          solve_order_ind R n
      | |- _ => idtac
      end
    with solve_seq_upper_bound R :=
      match goal with
      | |- seq_upper_bound ?xs ?y =>
          let n := fresh "n" in
          intros n;
          solve_order_ind R n
      | |- _ => idtac
      end.
    
    (* 一些性质与引理的证明*)
    (**************************************)
    
    Lemma const_limit:
      forall {A: Type}
             {RA: Order A} {EA: Equiv A}
             {oLubA: OmegaLub A} {BotA: Bot A}
             {equ: Equivalence equiv}
             {CPO: CompletePartialOrder_Setoid A} c,
      omega_lub (fun n => c) == c.
    Proof.
      intros.
      apply antisymmetricity_setoid.
      + solve_order order_rel.
      + apply limit_greater; [solve_seq_mono order_rel |].
        exists 0; reflexivity.
    Qed.
    
    Lemma seq_mono_nat_le:
      forall {A: Type} {RA: Order A}
             {rfR: Reflexive order_rel} {trR: Transitive order_rel}
             (T: nat -> A),
      seq_mono T ->
      forall n m, (n <= m)%nat -> T n <= T m.
    Proof.
      intros.
      induction H0.
      + reflexivity.
      + etransitivity; eauto.
    Qed.
    
    Lemma seq_least_upper_bound_unique:
      forall {A: Type} `{CPO: PartialOrder_Setoid A},
      forall T bnd1 bnd2,
      seq_least_upper_bound T bnd1 ->
      seq_least_upper_bound T bnd2 ->
      bnd1 == bnd2.
    Proof.
      intros.
      destruct H, H0.
      apply H2 in H.
      apply H1 in H0.
      apply antisymmetricity_setoid; auto.
    Qed.
    
    Lemma iter_bot_mono: forall {A: Type} `{CPO: CompletePartialOrder_Setoid A},
      forall f,
        Proper (order_rel ==> order_rel) f ->
        seq_mono (fun n => Nat.iter n f bot).
    Proof. intros. solve_seq_mono order_rel. Qed.
    
    Lemma seq_mono_without_0_seq_mono: forall {A: Type} {RA: Order A} T,
      seq_mono T ->
      seq_mono (fun n => T (S n)).
    Proof. intros. solve_seq_mono order_rel. Qed.
    
    Lemma seq_mono_without_0_upper_bound: forall {A: Type} {RA: Order A} T bnd,
      seq_mono T ->
      seq_upper_bound T bnd ->
      seq_upper_bound (fun n => T (S n)) bnd.
    Proof. intros. solve_seq_upper_bound order_rel. Qed.
    
    Lemma seq_mono_without_0_upper_bound_inv: forall {A: Type} {RA: Order A},
      Transitive order_rel ->
      forall T bnd,
      seq_mono T ->
      seq_upper_bound (fun n => T (S n)) bnd ->
      seq_upper_bound T bnd.
    Proof.
      unfold seq_upper_bound.
      intros.
      destruct n; [| apply H1; auto].
      transitivity (T (S O)); [apply H0 | apply H1].
    Qed.
    
    Lemma seq_mono_without_0_least_upper_bound: forall {A: Type} {RA: Order A},
      Transitive order_rel ->
      forall T bnd,
      seq_mono T ->
      seq_least_upper_bound T bnd ->
      seq_least_upper_bound (fun n => T (S n)) bnd.
    Proof.
      unfold seq_least_upper_bound; intros.
      destruct H1.
      split; intros.
      + apply seq_mono_without_0_upper_bound; auto.
      + apply seq_mono_without_0_upper_bound_inv in H3; auto.
    Qed.
    
    Lemma seq_mono_without_0_limit:
      forall {A: Type} `{CPO: CompletePartialOrder_Setoid A} T,
      seq_mono T ->
      omega_lub T == omega_lub (fun n => T (S n)).
    Proof.
      intros.
      pose proof CPO_SeqCont T H.
      pose proof CPO_SeqCont _ ltac:(eapply seq_mono_without_0_seq_mono; eauto).
      apply seq_mono_without_0_least_upper_bound in H0; auto; [| apply CPO].
      eapply seq_least_upper_bound_unique; eauto.
    Qed.
    
    Theorem seq_mono_squeeze_limit:
      forall {A: Type} `{CPO: CompletePartialOrder_Setoid A} T1 T2,
        seq_mono T1 ->
        seq_mono T2 ->
        (forall n, T1 n <= T2 n) ->
        (forall n, T2 n <= omega_lub T1) ->
        omega_lub T1 == omega_lub T2.
    Proof.
      intros.
      eapply seq_least_upper_bound_unique; [| apply CPO_SeqCont; auto].
      split.
      + intros; auto.
      + intros.
        solve_order R.
        etransitivity; [apply H1 | apply H3].
    Qed.
    
    (* 引理证明结束*)
    
    (**************************************) 
    
    (* 定理:<当A,R>是完备偏序集, 函数f单调且连续, 集合存在最小元时, (Nat.iter n f bot)的上确界是函数f的不动点 *)
    
    Theorem BourbakiWitt_fixpoint:
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Setoid A} f,
        Proper (order_rel ==> order_rel) f ->
        seq_continuous f ->
        BW_fix f == f (BW_fix f).
    Proof.
      intros.
      unfold BW_fix.
      rewrite H0 by (solve_seq_mono R).
      rewrite seq_mono_without_0_limit by (solve_seq_mono R).
      simpl. reflexivity.
    Qed.
    
    Theorem BourbakiWitt_least_fixpoint:
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Setoid A} f p,
        Proper (order_rel ==> order_rel) f ->
        seq_continuous f ->
        fixpoint f p ->
        BW_fix f <= p.
    Proof.
      intros.
      unfold BW_fix.
      set (L := fun n => Nat.iter n f bot).
      pose proof CPO_SeqCont L.
      assert (seq_mono L) by (eapply iter_bot_mono; eauto).
      specialize (H2 H3) as [? ?].
      apply H4.
      hnf; intros.
      unfold fixpoint in H1.
      clear - CPO equ H H1; subst L.
      induction n; simpl.
      + apply CPO_least.
      + rewrite H1.
        apply H; auto.
    Qed.
    
    (*更宽松的定理，不一定用F本身迭代，而可以用更大的步伐迭代*)
    
    Theorem BourbakiWitt_fixpoint_relax:
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Setoid A} f g,
        Proper (order_rel ==> order_rel) f ->
        Proper (order_rel ==> order_rel) g ->
        seq_continuous f ->
        seq_continuous g ->
        (forall a b, a <= b -> a <= f a -> f a <= g b) ->
        (forall b, (forall a, a <= b -> f a <= b) -> (forall a, a <= b -> g a <= b)) ->
        BW_fix f == BW_fix g.
    Proof.
      intros.
      assert (forall n, Nat.iter n f bot <= Nat.iter n g bot).
      {
        intros.
        induction n.
        + simpl; reflexivity.
        + pose proof iter_bot_mono  _ H n.
          simpl.
          apply H3; auto.
      }
      assert (forall n, Nat.iter n g bot <= BW_fix f).
      {
        intros.
        induction n.
        + apply CPO_least.
        + simpl.
          apply H4; auto.
          intros.
          rewrite BourbakiWitt_fixpoint by auto.
          apply H; auto.
      }
      unfold BW_fix.
      apply seq_mono_squeeze_limit; auto;
      apply iter_bot_mono; auto.
    Qed.
    
    (*如果两个函数一个比另一个大，则他们的不动点也有对应大小关系*)
    
    Theorem BourbakiWitt_fixpoint_monotonic:
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Setoid A} f g,
        Proper (order_rel ==> order_rel) f ->
        Proper (order_rel ==> order_rel) g ->
        (forall a b, a <= b -> f a <= g b) ->
        BW_fix f <= BW_fix g.
    Proof.
      intros.
      unfold BW_fix.
      solve_order order_rel.
    Qed.
    
    Theorem BourbakiWitt_fixpoint_mono:
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Strong_Setoid A} f g,
        Proper (order_rel ==> order_rel) f ->
        (forall a b, a <= b -> f a <= g b) ->
        BW_fix f <= BW_fix g.
    Proof.
      intros.
      unfold BW_fix. pose proof CPO.(CPOs_CompletePartialOrder) as CP.
      solve_order order_rel.
      assert((Nat.iter n f bot) <= (Nat.iter n g bot)).
      { induction n;simpl;[reflexivity|]. apply H0;tauto. }
      rewrite H1. eapply CPO.(CPOs_SeqCont).
    Qed.
    
    Theorem BourbakiWitt_fixpoint_mono':
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Strong_Setoid A} f g,
        Proper (order_rel ==> order_rel) f ->
        (forall a, f a <= g a) ->
        BW_fix f <= BW_fix g.
    Proof.
      intros.
      unfold BW_fix. pose proof CPO.(CPOs_CompletePartialOrder) as CP.
      solve_order order_rel.
      assert((Nat.iter n f bot) <= (Nat.iter n g bot)).
      { induction n;simpl;[reflexivity|]. rewrite IHn. apply H0. }
      rewrite H1. eapply CPO.(CPOs_SeqCont).
    Qed.
    
    Theorem BourbakiWitt_fixpoint_congr:
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Strong_Setoid A} f g,
        (forall a b, a == b -> f a == g b) ->
        BW_fix f == BW_fix g.
    Proof.
      intros. unfold BW_fix. pose proof CPO.(CPOs_CompletePartialOrder) as CP. apply CPOs_limit_congr. induction n;simpl;[reflexivity|].
      apply H;auto.
    Qed.
    
    Theorem BourbakiWitt_fixpoint_congr':
      forall
        {A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Strong_Setoid A} f g,
        Proper (equiv ==> equiv) f ->
        (forall a, f a == g a) ->
        BW_fix f == BW_fix g.
    Proof.
      intros. unfold BW_fix. pose proof CPO.(CPOs_CompletePartialOrder) as CP.
      apply CPOs_limit_congr. induction n;simpl;[reflexivity|].
      rewrite IHn;auto.
    Qed.  
    
    
    (**************************************)
    
    (** CPO的实例与构造 *)
    
    Module CPO_sets.
    Import PO_sets.
    
    #[export] Instance oLub_sets
               {T: Type}
               {_SETS: Sets.SETS T}: OmegaLub T :=
      Sets.indexed_union.
    
    #[export] Instance Bot_sets
               {T: Type}
               {_SETS: Sets.SETS T}: Bot T :=
      (∅: T)%sets.
    
    Ltac unfold_CPO_defs :=
      unfold equiv, order_rel, omega_lub, bot,
             R_sets, Equiv_sets, oLub_sets, Bot_sets.
    
    #[export] Instance CPO_sets
               {T: Type}
               {_SETS: Sets.SETS T}
               {_SETS_Properties: SETS_Properties T}:
      CompletePartialOrder_Setoid T.
    Proof.
      split.
      + apply PO_sets.
      + intros; hnf; intros.
        split; intros.
        - hnf; intros. 
          apply Sets_included_indexed_union; intros.
        - apply Sets_indexed_union_included.
          auto.
      + intros a. apply Sets_empty_included.
    Qed.
    
    #[export] Instance CPOs_sets
               {T: Type}
               {_SETS: Sets.SETS T}
               {_SETS_Properties: SETS_Properties T}:
      CompletePartialOrder_Strong_Setoid T.
    Proof.
      constructor.
      + apply CPO_sets.
      + intros. hnf. split.
        - hnf;intros. apply Sets_included_indexed_union.
        - unfold seq_upper_bound. apply Sets_indexed_union_included.
    Qed.
    
    Arguments oLub_sets: simpl never.
    Arguments Bot_sets: simpl never.
    
    End CPO_sets.
    
    Module CPO_Prop.
    
    #[export] Instance R_Prop: Order Prop :=
      fun P Q: Prop => P -> Q.
    
    #[export] Instance Equiv_Prop: Equiv Prop := iff.
    
    #[export] Instance oLub_Prop: OmegaLub Prop :=
      (@ex _).
    
    #[export] Instance Bot_Prop: Bot Prop :=
      False.
    
    Ltac unfold_CPO_defs :=
      unfold equiv, order_rel, omega_lub, bot,
             R_Prop, Equiv_Prop, oLub_Prop, Bot_Prop.
    
    #[export] Instance PO_Prop: PartialOrder_Setoid Prop.
    Proof.
      constructor.
      + hnf; unfold_CPO_defs; tauto.
      + unfold_CPO_defs; intros; tauto.
      + hnf; unfold_CPO_defs; intros; tauto.
    Qed.
    
    #[export] Instance CPO_Prop: CompletePartialOrder_Setoid Prop.
    Proof.
      constructor.
      + apply PO_Prop.
      + intros.
        split.
        - hnf; intros.
          exists n; auto.
        - unfold_CPO_defs.
          intros.
          destruct H1 as [n ?].
          apply H0 in H1.
          auto.
      + unfold_CPO_defs; intros; firstorder.
    Qed.
    
    End CPO_Prop.
    
    Module CPO_Prop_flip.
    
    #[export] Instance R_Prop_flip: Order Prop :=
      fun P Q: Prop => Q -> P.
    
    #[export] Instance Equiv_Prop_flip: Equiv Prop := iff.
    
    #[export] Instance oLub_Prop_flip: OmegaLub Prop :=
      (fun P => forall n, P n).
    
    #[export] Instance Bot_Prop_flip: Bot Prop :=
      True.
    
    Ltac unfold_CPO_defs :=
      unfold equiv, order_rel, omega_lub, bot,
             R_Prop_flip, Equiv_Prop_flip,
             oLub_Prop_flip, Bot_Prop_flip.
    
    #[export] Instance PO_Prop_flip: PartialOrder_Setoid Prop.
    Proof.
      constructor.
      + hnf; unfold_CPO_defs; tauto.
      + unfold_CPO_defs; intros; tauto.
      + hnf; unfold_CPO_defs; intros; tauto.
    Qed.
    
    #[export] Instance CPO_Prop_flip: CompletePartialOrder_Setoid Prop.
    Proof.
      constructor.
      + apply PO_Prop_flip.
      + intros.
        split.
        - hnf; unfold_CPO_defs; intros.
          apply H; auto.
        - unfold_CPO_defs; intros.
          apply H0; auto.
      + hnf; unfold_CPO_defs; intros.
        tauto.
    Qed.
    
    End CPO_Prop_flip.
    
    Module CPO_lift.
    Import PO_lift.
    
    Section CPO_lift.
    
    Context (A: Type) {B: Type} `{CPOB: CompletePartialOrder_Setoid B}.
    
    #[export] Instance oLub_lift: OmegaLub (A -> B) :=
      lift_binder omega_lub.
    
    #[export] Instance Bot_lift: Bot (A -> B) :=
      lift_fun0 bot.
    
    Ltac unfold_CPO_defs :=
      unfold equiv, order_rel, omega_lub, bot,
             R_lift, Equiv_lift, oLub_lift, Bot_lift,
             lift_rel2, lift_binder, lift_fun0.
    
    #[export] Instance CPO_lift: CompletePartialOrder_Setoid (A -> B).
    Proof.
      constructor.
      + apply PO_lift.
        apply CPO_PartialOrder. 
      + intros.
        pose proof fun a => CPO_SeqCont (fun n => T n a).
        split.
        - hnf; unfold_CPO_defs; intros.
          specialize (H0 a ltac:(intro; apply H)).
          destruct H0.
          apply H0.
        - unfold_CPO_defs; intros.
          specialize (H0 a ltac:(intro; apply H)).
          destruct H0.
          apply H2.
          hnf; intros; apply H1.
      + hnf; unfold_CPO_defs; intros.
        apply CPO_least.
    Qed.
    
    End CPO_lift.
    
    End CPO_lift.
  