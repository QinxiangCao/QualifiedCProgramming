Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CopyPasteStep (current : list Z) (op : Z * Z) : list Z :=
  current ++ sublist (fst op - 1) (snd op) current.

Definition Pre (s : list Z) (ops : list (Z * Z)) (queries : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\ 1 <= Zlength ops <= 40 /\
  1 <= Zlength queries <= 10000 /\ Forall (fun c => 97 <= c <= 122) s /\
  exists states,
    Zlength states = Zlength ops + 1 /\ Znth 0 states nil = s /\
    (forall i, 0 <= i < Zlength ops ->
       1 <= fst (Znth i ops (0, 0)) <= snd (Znth i ops (0, 0)) /\
       snd (Znth i ops (0, 0)) <= Zlength (Znth i states nil) /\
       Znth (i + 1) states nil = CopyPasteStep (Znth i states nil) (Znth i ops (0, 0))) /\
    Forall (fun k => 1 <= k <= Zlength (Znth (Zlength ops) states nil)) queries.

Definition Spec (s : list Z) (ops : list (Z * Z)) (queries out : list Z) : Prop :=
  let final := fold_left CopyPasteStep ops s in
  Forall2
    (fun query answer => answer = Znth (query - 1) final 0)
    queries out.

Definition CopyPasteStates
    (s : list Z) (ops : list (Z * Z)) (states : list (list Z)) : Prop :=
  Zlength states = Zlength ops + 1 /\
  Znth 0 states nil = s /\
  forall i, 0 <= i < Zlength ops ->
    1 <= fst (Znth i ops (0, 0)) <= snd (Znth i ops (0, 0)) /\
    snd (Znth i ops (0, 0)) <= Zlength (Znth i states nil) /\
    Znth (i + 1) states nil =
      CopyPasteStep (Znth i states nil) (Znth i ops (0, 0)).

Definition StateLengthsPrefix
    (states : list (list Z)) (upto : Z) (lengths : list Z) : Prop :=
  Zlength lengths = upto /\
  forall i, 0 <= i < upto ->
    Znth i lengths 0 = Zlength (Znth i states nil).

Definition BacktrackedPosition
    (states : list (list Z)) (query i k : Z) : Prop :=
  let final_index := Zlength states - 1 in
  -1 <= i < final_index /\
  1 <= query <= Zlength (Znth final_index states nil) /\
  1 <= k <= Zlength (Znth (i + 1) states nil) /\
  Znth (k - 1) (Znth (i + 1) states nil) 0 =
    Znth (query - 1) (Znth final_index states nil) 0.

Definition AnswerPrefix
    (s : list Z) (ops : list (Z * Z))
    (queries : list Z) (upto : Z) (out : list Z) : Prop :=
  let final := fold_left CopyPasteStep ops s in
  0 <= upto <= Zlength queries /\
  Zlength out = upto /\
  forall i, 0 <= i < upto ->
    Znth i out 0 = Znth (Znth i queries 0 - 1) final 0.

Definition FinalCharacter
    (s : list Z) (ops : list (Z * Z)) (query answer : Z) : Prop :=
  answer = Znth (query - 1) (fold_left CopyPasteStep ops s) 0.

Require Import Coq.micromega.Lia.
Lemma copy_paste_states_length_pow_bound__copy_state_transition :
  forall text ops states k,
    CopyPasteStates text ops states ->
    Zlength text <= 200000 ->
    0 <= k <= Zlength ops ->
    Zlength (Znth k states nil) <= 200000 * 2 ^ k.
Proof.
  intros text ops states k Hstates Htext Hk.
  destruct Hstates as [Hstates_len [Hinitial Hstep]].
  assert (Hk_nat : k = Z.of_nat (Z.to_nat k)) by lia.
  remember (Z.to_nat k) as n eqn:Hn.
  subst k.
  clear Hn.
  revert Hk.
  induction n as [|n IH]; intros Hk.
  - change (Zlength (Znth 0 states nil) <= 200000 * 2 ^ 0).
    rewrite Z.pow_0_r, Hinitial.
    nia.
  - rewrite Nat2Z.inj_succ in *.
    specialize (IH ltac:(lia)).
    specialize (Hstep (Z.of_nat n) ltac:(lia)).
    destruct Hstep as [[Hleft Hright] [Hright_bound Hnext]].
    replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) by lia.
    rewrite Hnext.
    unfold CopyPasteStep.
    rewrite Zlength_app, Zlength_sublist by lia.
    replace (Z.of_nat n + 1) with (Z.succ (Z.of_nat n)) by lia.
    rewrite Z.pow_succ_r by lia.
    nia.
Qed.
Lemma Znth_app_left__copy_state_transition :
  forall (l1 l2 : list Z) (d j : Z),
    0 <= j < Zlength l1 ->
    Znth j (l1 ++ l2) d = Znth j l1 d.
Proof.
  intros l1 l2 d j Hj.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hj.
  lia.
Qed.
Lemma Znth_app_last__copy_state_transition :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (Datatypes.length l)) - Datatypes.length l)%nat
      with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma CopyPasteStates_prefix_fold__backtrack_transitions :
  forall s ops states i,
    CopyPasteStates s ops states ->
    0 <= i <= Zlength ops ->
    Znth i states nil =
      fold_left CopyPasteStep (sublist 0 i ops) s.
Proof.
  intros s ops states i Hstates [Hi0 Hiupper].
  destruct Hstates as [Hlen [Hzero Hstep]].
  assert (Hbase : 0 <= i) by exact Hi0.
  revert Hi0 Hiupper.
  pattern i.
  apply Z_lt_induction.
  intros x IH Hxnonneg Hxupper.
  destruct (Z.eq_dec x 0) as [-> | Hx0].
  - rewrite Hzero.
    reflexivity.
  - specialize (Hstep (x - 1) ltac:(lia)).
    destruct Hstep as [_ [_ Hstep]].
    replace (x - 1 + 1) with x in Hstep by lia.
    rewrite Hstep.
    rewrite (IH (x - 1)) by lia.
    rewrite (sublist_split 0 x (x - 1) ops) by lia.
    assert (Hsingle : sublist (x - 1) x ops =
                      (Znth (x - 1) ops (0, 0) :: nil)%list).
    { replace x with (x - 1 + 1) by lia.
      replace (x - 1 + 1 - 1) with (x - 1) by lia.
      apply sublist_single.
      lia. }
    rewrite Hsingle.
    rewrite fold_left_app.
    simpl.
    reflexivity.
  - exact Hbase.
Qed.
Lemma Forall_Znth_in_range__backtrack_transitions :
  forall (A : Type) (P : A -> Prop) l d i,
    Forall P l ->
    0 <= i < Zlength l ->
    P (Znth i l d).
Proof.
  intros A P l d i Hforall Hi.
  apply (proj1 (Forall_forall P l) Hforall).
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma CopyPasteStates_final_fold__backtrack_transitions :
  forall s ops states,
    CopyPasteStates s ops states ->
    Znth (Zlength ops) states nil = fold_left CopyPasteStep ops s.
Proof.
  intros s ops states Hstates.
  rewrite (CopyPasteStates_prefix_fold__backtrack_transitions s ops states
             (Zlength ops) Hstates)
    by (pose proof (Zlength_nonneg ops); lia).
  rewrite (sublist_self ops (Zlength ops)) by reflexivity.
  reflexivity.
Qed.
Lemma CopyPasteStates_length_at__backtrack_transitions :
  forall s ops states i,
    CopyPasteStates s ops states ->
    0 <= i <= Zlength ops ->
    Zlength (Znth i states nil) <= Zlength s * 2 ^ i.
Proof.
  intros s ops states i Hstates [Hi0 Hiupper].
  destruct Hstates as [Hstates_len [Hstates_zero Hstates_step]].
  assert (Hbase : 0 <= i) by exact Hi0.
  revert Hi0 Hiupper.
  pattern i.
  apply Z_lt_induction.
  - intros x IH Hxnonneg Hxupper.
    destruct (Z.eq_dec x 0) as [-> | Hx0].
    + rewrite Hstates_zero.
      simpl.
      nia.
    + specialize (Hstates_step (x - 1) ltac:(lia)).
      destruct Hstates_step as [Hop_lr [Hop_r Htransition]].
      replace (x - 1 + 1) with x in Htransition by lia.
      rewrite Htransition.
      unfold CopyPasteStep.
      rewrite Zlength_app.
      rewrite Zlength_sublist by lia.
      pose proof (IH (x - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as Hprev.
      replace x with (Z.succ (x - 1)) by lia.
      rewrite Z.pow_succ_r by lia.
      replace (Z.succ (x - 1) - 1) with (x - 1) by lia.
      nia.
  - exact Hbase.
Qed.
Lemma CopyPasteStates_final_length_bound__backtrack_transitions :
  forall s ops states,
    Zlength s <= 200000 ->
    Zlength ops <= 40 ->
    CopyPasteStates s ops states ->
    Zlength (Znth (Zlength ops) states nil) <= 219902325555200000.
Proof.
  intros s ops states Hs Hops Hstates.
  pose proof (CopyPasteStates_length_at__backtrack_transitions
                s ops states (Zlength ops) Hstates
                ltac:(pose proof (Zlength_nonneg ops); lia)) as Hlength.
  assert (Hpow : 2 ^ Zlength ops <= 2 ^ 40).
  { apply Z.pow_le_mono_r; lia. }
  change (2 ^ Zlength ops <= 1099511627776) in Hpow.
  pose proof (Zlength_nonneg s).
  nia.
Qed.


Lemma query_bound__backtrack_transitions : forall s ops qs states z,
 Pre s ops qs -> CopyPasteStates s ops states ->
 0 <= z < Zlength qs ->
 1 <= Znth z qs 0 <= Zlength (Znth (Zlength ops) states nil).
Proof.
 intros s ops qs states z HP HS Hz.
 destruct HP as [_ [_ [_ [_ [old [HL [H0 [HT HQ]]]]]]]].
 assert (HO : CopyPasteStates s ops old) by (unfold CopyPasteStates; exact (conj HL (conj H0 HT))).
 pose proof (Forall_Znth_in_range__backtrack_transitions _ _ _ 0 z HQ Hz) as HB.
 rewrite (CopyPasteStates_final_fold__backtrack_transitions _ _ _ HO) in HB.
 rewrite (CopyPasteStates_final_fold__backtrack_transitions _ _ _ HS).
 exact HB.
Qed.
Lemma backtrack_start__backtrack_transitions : forall s ops qs states z,
 Pre s ops qs -> CopyPasteStates s ops states -> 0 <= z < Zlength qs ->
 BacktrackedPosition states (Znth z qs 0) (Zlength ops - 1) (Znth z qs 0) /\
 1 <= Znth z qs 0 <= 219902325555200000.
Proof.
 intros s ops qs states z HP HS Hz.
 pose proof (query_bound__backtrack_transitions _ _ _ _ _ HP HS Hz) as HB.
 pose proof HP as [Hs [Ho _]].
 pose proof (CopyPasteStates_final_length_bound__backtrack_transitions _ _ _ (proj2 Hs) (proj2 Ho) HS) as HM.
 destruct HS as [HL _].
 split; [unfold BacktrackedPosition; rewrite HL; replace (Zlength ops + 1 - 1) with (Zlength ops) by lia; replace (Zlength ops - 1 + 1) with (Zlength ops) by lia; repeat split; try lia; reflexivity | lia].
Qed.
Lemma backtrack_finish__backtrack_transitions : forall s ops states query i k,
 CopyPasteStates s ops states -> BacktrackedPosition states query i k ->
 i < 0 -> 1 <= k <= Zlength s /\ FinalCharacter s ops query (Znth (k-1) s 0).
Proof.
 intros s ops states query i k HS HB Hi.
 pose proof HS as [HL [H0 HT]].
 unfold BacktrackedPosition in HB.
 destruct HB as [HI [HQ [HK HE]]].
 assert (i = -1) by lia; subst i.
 change (-1+1) with 0 in HK, HE.
 rewrite H0 in HK, HE.
 rewrite HL in HE.
 replace (Zlength ops + 1 - 1) with (Zlength ops) in HE by lia.
 rewrite (CopyPasteStates_final_fold__backtrack_transitions _ _ _ HS) in HE.
 split; [exact HK | exact HE].
Qed.
Lemma backtrack_left__backtrack_transitions : forall s ops states query i k,
 CopyPasteStates s ops states -> BacktrackedPosition states query i k ->
 0 <= i < Zlength ops -> k <= Zlength (Znth i states nil) ->
 BacktrackedPosition states query (i-1) k.
Proof.
 intros s ops states query i k HS HB Hi HK.
 pose proof HS as [HL [H0 HT]].
 specialize (HT i Hi); destruct HT as [Hlr [Hr HE]].
 unfold BacktrackedPosition in *.
 destruct HB as [HI [HQ [HKold HC]]].
 replace (i-1+1) with i by lia.
 repeat split; try lia; try tauto.
 rewrite HE in HC; unfold CopyPasteStep in HC.
 rewrite Znth_app_left__copy_state_transition in HC by lia.
 exact HC.
Qed.
Lemma backtrack_right__backtrack_transitions : forall s ops states query i k,
 CopyPasteStates s ops states -> BacktrackedPosition states query i k ->
 0 <= i < Zlength ops -> Zlength (Znth i states nil) < k ->
 BacktrackedPosition states query (i-1)
   (fst (Znth i ops (0,0)) + k - Zlength (Znth i states nil) - 1).
Proof.
 intros s ops states query i k HS HB Hi HK.
 pose proof HS as [HL [H0 HT]].
 specialize (HT i Hi); destruct HT as [Hlr [Hr HE]].
 unfold BacktrackedPosition in *.
 destruct HB as [HI [HQ [HKold HC]]].
 rewrite HE in HKold, HC; unfold CopyPasteStep in HKold, HC.
 rewrite Zlength_app, Zlength_sublist in HKold by lia.
 replace (i-1+1) with i by lia.
 repeat split; try lia; try tauto.
 assert (HA : forall (a b : list Z) j, Zlength a <= j ->
   Znth j (a++b) 0 = Znth (j-Zlength a) b 0).
 { intros a b j Hj. unfold Znth. rewrite app_nth2.
   - f_equal. rewrite Zlength_correct. lia.
   - rewrite Zlength_correct in Hj. lia. }
 rewrite HA in HC by lia.
 rewrite Znth_sublist in HC by lia.
 replace (k-1-Zlength (Znth i states nil)+(fst (Znth i ops (0,0))-1))
   with (fst (Znth i ops (0,0))+k-Zlength (Znth i states nil)-1-1) in HC by lia.
 exact HC.
Qed.
Lemma Znth_default__copy_safety : forall (A : Type) (xs : list A) i d1 d2,
  0 <= i < Zlength xs -> Znth i xs d1 = Znth i xs d2.
Proof.
  intros A xs i d1 d2 Hi.
  unfold Znth.
  apply nth_indep.
  rewrite Zlength_correct in Hi. lia.
Qed.
