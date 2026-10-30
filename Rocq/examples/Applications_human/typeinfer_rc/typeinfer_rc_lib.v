From Coq Require Import ZArith List String Lia.
From AUXLib Require Import ListLib.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From MonadLib.MonadErr Require Import StateRelMonadErr.
From SimpleC.EE.Applications_human.typeinfer Require Export type_infer_lib sound_pv.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

From SimpleC.EE.Applications_human.typeinfer_rc Require Export typeinfer_rc.
(* Compile the soundness certificate through the ordinary case dependency
   chain.  Its goal/proof modules depend only on the instance, never on lib. *)
From SimpleC.EE.Applications_human.typeinfer_rc Require Import typeinfer_rc_strategy_goal_check.


(* 以下是 C 验证所需的辅助引理区，而非另一套 RC 定义。阅读时可按用途搜索：
   - right_variable / left_variable：变量入表时的解码、预算与 solution 更新；
   - representative_cleanup：临时代表元释放后，保留调用前的基准图和引用；
   - release_children / release_delete：删父节点、转换子边、逐个释放的账目；
   - same_return_final_bridge：将实现结果接回原有数学正确性，使用同一返回码；
   - world / payload / tag 相关引理：拆出 C 字段再重组，区分别名和不同节点。
   引理名中的双下划线后缀用于区分证明组来源，不表示新增状态或权限。

   扩展范围提醒：通用部分是有限无环图的 RC 账目和这些操作；本文件未实现
   任意 syntax 节点插入/替换的完整通用 API，也尚未验证表达式匹配。
   若下一步引入 expression 节点或多个容器，需重新规定 owning 出边和容器
   引用预算，不能仅复用纯 store_type 就推断已有独立的可释放权限。
*)
From Coq Require Import Logic.FunctionalExtensionality.
(* Transitional node-level proof views, scoped to VC helper implementation.
   C and instance clients use only store_world_missing; these views are not
   another public storage API and carry no new assumptions. *)
Module TypeinferRCFrameCompat.
Definition store_world_without_count (M : RcState) (p : addr) : Assertion :=
  EX n : TypeNode, “ TypeRCMap.nodes M p = Some n ” &&
    store_node_payload p n ** store_world_except M p.


Definition store_world_without_tag (M : RcState) (p : addr) (n : TypeNode)
    : Assertion :=
  (&(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p) **
  store_payload_aux p n ** store_world_except M p.


Definition store_world_without_payload (M : RcState) (p : addr) (n : TypeNode)
    : Assertion :=
  (&(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p) **
  (&(p # "atype" ->ₛ "t") # Int |-> node_tag n) **
  store_world_except M p.


Definition store_world_without_tags2 (M : RcState)
    (p : addr) (np : TypeNode) (q : addr) (nq : TypeNode) : Assertion :=
  (&(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p) **
  store_payload_aux p np **
  (&(q # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M q) **
  store_payload_aux q nq ** store_world_except2 M p q.


Definition store_world_without_payloads2 (M : RcState)
    (p : addr) (np : TypeNode) (q : addr) (nq : TypeNode) : Assertion :=
  (&(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p) **
  (&(p # "atype" ->ₛ "t") # Int |-> node_tag np) **
  (&(q # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M q) **
  (&(q # "atype" ->ₛ "t") # Int |-> node_tag nq) **
  store_world_except2 M p q.


Lemma missing_tag_view : forall M p n,
  TypeRCMap.nodes M p = Some n ->
  store_world_missing M [(p,Tag)] --||-- store_world_without_tag M p n.
Proof.
  intros M p n H; unfold store_world_without_tag; split.
  - sep_apply (proj1 (store_world_missing_at M [(p,Tag)] p n H ltac:(simpl; intros; intuition congruence))).
    sep_apply (proj1 (store_node_missing_tag M p n)); cancel; reflexivity.
  - sep_apply_r_atomic (proj2 (store_world_missing_at M [(p,Tag)] p n H ltac:(simpl; intros; intuition congruence))).
    sep_apply_r_atomic (proj2 (store_node_missing_tag M p n)); cancel; reflexivity.
Qed.

Lemma missing_payload_view : forall M p n,
  TypeRCMap.nodes M p = Some n ->
  store_world_missing M (payload_keys p n) --||-- store_world_without_payload M p n.
Proof.
  intros M p n H; unfold store_world_without_payload; split.
  - sep_apply (proj1 (store_world_missing_at M (payload_keys p n) p n H (payload_keys_owner p n))).
    sep_apply (proj1 (store_node_missing_payload M p n)); cancel; reflexivity.
  - sep_apply_r_atomic (proj2 (store_world_missing_at M (payload_keys p n) p n H (payload_keys_owner p n))).
    sep_apply_r_atomic (proj2 (store_node_missing_payload M p n)); cancel; reflexivity.
Qed.

Lemma missing_count_view : forall M p n,
  TypeRCMap.nodes M p = Some n ->
  store_world_missing M [(p,RefCount)] --||-- store_world_without_count M p.
Proof.
  intros M p n H; unfold store_world_without_count; split.
  - sep_apply (proj1 (store_world_missing_at M [(p,RefCount)] p n H ltac:(simpl; intros; intuition congruence))).
    sep_apply (proj1 (store_node_missing_count M p n)); Exists n.
    apply _derivable1_andp_intros.
    + apply dump_spatial_left; exact H.
    + reflexivity.
  - Intros m; rewrite H in H0; inversion H0; subst m.
    sep_apply_r_atomic (proj2 (store_world_missing_at M [(p,RefCount)] p n H ltac:(simpl; intros; intuition congruence))).
    sep_apply_r_atomic (proj2 (store_node_missing_count M p n)); cancel; reflexivity.
Qed.

Lemma missing_tags_view : forall M p np q nq,
  TypeRCMap.nodes M p = Some np -> TypeRCMap.nodes M q = Some nq -> p <> q ->
  store_world_missing M [(p,Tag);(q,Tag)] --||-- store_world_without_tags2 M p np q nq.
Proof.
  intros M p np q nq Hp Hq Hneq.
  assert (Ep : store_node_missing M [(p,Tag);(q,Tag)] p np = store_node_missing M [(p,Tag)] p np).
  { apply store_node_missing_ext; intro s; simpl; intuition congruence. }
  assert (Eq : store_node_missing M [(p,Tag);(q,Tag)] q nq = store_node_missing M [(q,Tag)] q nq).
  { apply store_node_missing_ext; intro s; simpl; intuition congruence. }
  pose proof (store_world_missing_at_two M [(p,Tag);(q,Tag)] p np q nq Hp Hq Hneq
    ltac:(intros r s Hin; simpl in Hin; intuition congruence)) as Hv.
  setoid_rewrite Ep in Hv; setoid_rewrite Eq in Hv.
  unfold store_world_without_tags2; split.
  - sep_apply (proj1 Hv).
    sep_apply (proj1 (store_node_missing_tag M p np)).
    sep_apply (proj1 (store_node_missing_tag M q nq)); cancel; reflexivity.
  - sep_apply_r_atomic (proj2 Hv).
    rewrite <- (proj2 (store_node_missing_tag M p np)).
    rewrite <- (proj2 (store_node_missing_tag M q nq)).
    sepcon_assoc_change; reflexivity.
Qed.

Lemma missing_payloads_view : forall M p np q nq,
  TypeRCMap.nodes M p = Some np -> TypeRCMap.nodes M q = Some nq -> p <> q ->
  store_world_missing M (payload_keys p np ++ payload_keys q nq)
    --||-- store_world_without_payloads2 M p np q nq.
Proof.
  intros M p np q nq Hp Hq Hneq.
  assert (Ep : store_node_missing M (payload_keys p np ++ payload_keys q nq) p np =
    store_node_missing M (payload_keys p np) p np).
  { apply store_node_missing_ext; intro s; rewrite in_app_iff; split; intros Hin;
      [destruct Hin; [assumption|apply payload_keys_owner in H; congruence]|auto]. }
  assert (Eq : store_node_missing M (payload_keys p np ++ payload_keys q nq) q nq =
    store_node_missing M (payload_keys q nq) q nq).
  { apply store_node_missing_ext; intro s; rewrite in_app_iff; split; intros Hin;
      [destruct Hin; [apply payload_keys_owner in H; congruence|assumption]|auto]. }
  pose proof (store_world_missing_at_two M (payload_keys p np ++ payload_keys q nq)
    p np q nq Hp Hq Hneq ltac:(intros r s Hin; apply in_app_or in Hin;
      destruct Hin; [left|right]; eapply payload_keys_owner; eauto)) as Hv.
  setoid_rewrite Ep in Hv; setoid_rewrite Eq in Hv.
  unfold store_world_without_payloads2; split.
  - sep_apply (proj1 Hv).
    sep_apply (proj1 (store_node_missing_payload M p np)).
    sep_apply (proj1 (store_node_missing_payload M q nq)); cancel; reflexivity.
  - sep_apply_r_atomic (proj2 Hv).
    rewrite <- (proj2 (store_node_missing_payload M p np)).
    rewrite <- (proj2 (store_node_missing_payload M q nq)).
    sepcon_assoc_change; reflexivity.
Qed.

End TypeinferRCFrameCompat.
Import TypeinferRCFrameCompat.

Lemma decode_node__right_variable : forall M p tr,
  decode_type M p tr -> exists n, node_at M p n.
Proof.
  intros M p tr; destruct tr; cbn; intros H;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    eauto; destruct H as [H _]; eauto.
Qed.
Lemma decode_not_var__right_variable : forall M p tr n,
  decode_type M p tr -> node_at M p n -> node_tag n <> 3 -> not_var tr.
Proof.
  intros M p tr n Hd Hn Htag; destruct tr; cbn; try exact I.
  cbn in Hd; unfold node_at in Hn; rewrite Hd in Hn; inversion Hn; subst; contradiction.
Qed.
Lemma not_var_tag__right_variable : forall M p tr n,
  decode_type M p tr -> node_at M p n -> not_var tr -> node_tag n <> 3.
Proof.
  intros M p tr n Hd Hn Hnv; destruct tr; cbn in Hd,Hnv; try contradiction;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    unfold node_at in Hn;
    match goal with H : TypeRCMap.nodes _ _ = Some (Node _ _ _) |- _ =>
      rewrite H in Hn; inversion Hn; subst; cbn; discriminate
    end.
Qed.
Lemma decode_var__right_variable : forall M p tr n,
  decode_type M p tr -> node_at M p n -> node_tag n = 3 ->
  exists v, tr = TVar v /\ n = Node 3 v 0.
Proof.
  intros M p tr n Hd Hn Htag; destruct tr; cbn in Hd;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    unfold node_at in Hn;
    match goal with H : TypeRCMap.nodes _ _ = Some (Node _ _ _) |- _ => rewrite H in Hn end;
    inversion Hn; subst; cbn in Htag; try discriminate; eauto.
Qed.
Lemma live_nonzero__right_variable : forall M p n,
  rc_valid M -> node_at M p n -> p <> 0.
Proof.
  intros M p n [[_ [_ [_ [_ [Hl _]]]]] _] Hn.
  exact (proj1 (Hl p n Hn)).
Qed.
Lemma retain_eq__right_variable : forall M p M',
  retain_rel M p M' -> M' = RCMap.retain M p.
Proof.
  unfold retain_rel, RCMap.retain_program; cbn.
  intros M p M' [u [st [Ha [He Hs]]]]; congruence.
Qed.
Lemma retain_nodes__right_variable : forall (M : RcState) p,
  TypeRCMap.nodes (RCMap.retain M p) = TypeRCMap.nodes M.
Proof. intros; unfold RCMap.retain; destruct (Z.eq_dec p 0); reflexivity. Qed.
Lemma retain_decode__right_variable : forall M p q tr,
  decode_type (RCMap.retain M p) q tr <-> decode_type M q tr.
Proof.
  intros M p q tr; revert q; induction tr; cbn; intro q;
    rewrite retain_nodes__right_variable; try reflexivity;
    setoid_rewrite IHtr1; setoid_rewrite IHtr2; reflexivity.
Qed.
Lemma retained_reserved__right_variable : forall M p,
  rc_valid M -> p <> 0 -> 0 < rc_reserved (RCMap.retain M p) p.
Proof.
  intros M p [[_ [_ [_ [_ [_ [_ Hr]]]]]] _] Hp.
  specialize (Hr p).
  change (0 <= RCMap.reserved M p <= RCMap.roots M p) in Hr.
  change (0 < RCMap.reserved (RCMap.retain M p) p).
  unfold RCMap.retain;
    destruct (Z.eq_dec p 0); [contradiction|].
  cbn; unfold RCMap.put_count; destruct (Z.eq_dec p p);
    cbv beta iota zeta delta [TypePayload.node] in *; lia.
Qed.
Lemma repr_variable_empty__right_variable : forall s n tr,
  repr_rel_id s n tr -> forall v, tr = TVar v -> s v = None.
Proof.
  intros s n tr H; induction H; intros v He.
  - inversion He; subst; assumption.
  - subst; contradiction.
  - eauto.
Qed.
Lemma repr_self_empty__right_variable : forall s v,
  repr_rel_node s (TVar v) (TVar v) -> s v = None.
Proof.
  intros s v H; inversion H; subst.
  - eapply repr_variable_empty__right_variable; eauto.
  - contradiction.
Qed.
Lemma infer_nrm_unfold__right_variable : forall stage p q M s out,
  MonadErr.nrm (infer stage p q M s) tt out tt <->
  MonadErr.nrm (infer_rec infer stage p q M s) tt out tt.
Proof.
  intros stage p q M s out; pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H stage p q M s) as [Hn He]; apply Hn.
Qed.
Lemma right_retain_capacity__right_variable : forall M s p q v tr,
  rc_valid M -> decode_type M p tr -> not_var tr ->
  node_at M q (Node 3 v 0) -> not_occur_final s v tr ->
  rc_capacity 2 M s p q -> RCMap.counts M p < 2147483647.
Proof.
  intros M s p q v tr Hv Hd Hnv Hq Hocc Hcap.
  destruct (decode_node__right_variable M p tr Hd) as [n Hn].
  pose proof (not_var_tag__right_variable M p tr n Hd Hn Hnv) as Htag.
  pose proof (live_nonzero__right_variable M p n Hv Hn) as Hp.
  unfold rc_capacity in Hcap; rewrite infer_err_unfold in Hcap.
  unfold infer_rec in Hcap; unfold node_at in Hn,Hq; rewrite Hn,Hq in Hcap.
  cbn -[Z.eq_dec] in Hcap.
  destruct (Z.eq_dec 2 0); [lia|]; destruct (Z.eq_dec 2 1); [lia|].
  destruct (Z.eq_dec (node_tag n) 3); [contradiction|].
  destruct (Z.eq_dec 3 3); [|contradiction].
  unfold RCMap.retain_program in Hcap; cbn in Hcap.
  destruct (Z_lt_ge_dec (RCMap.counts M p) 2147483647); [assumption|].
  exfalso; apply Hcap; right; right.
  exists tr,tt; split; [reflexivity|].
  right; exists tt,tt; split; [repeat split; auto|].
  left; left; intros [Hz|Hlt]; [contradiction|].
  cbv beta iota zeta delta [TypePayload.node] in *; lia.
Qed.
Lemma right_infer_success__right_variable : forall M s p q v tr M',
  decode_type M p tr -> not_var tr -> node_at M q (Node 3 v 0) ->
  not_occur_final s v tr -> retain_rel M p M' ->
  infer_result 2 M s p q 0 (rc_publish M' p) (sol_update s v tr).
Proof.
  intros M s p q v tr M' Hd Hnv Hq Hocc Hr.
  destruct (decode_node__right_variable M p tr Hd) as [n Hn].
  pose proof (not_var_tag__right_variable M p tr n Hd Hn Hnv) as Htag.
  unfold infer_result; rewrite infer_nrm_unfold__right_variable.
  unfold infer_rec; unfold node_at in Hn,Hq; rewrite Hn,Hq.
  cbn -[Z.eq_dec].
  destruct (Z.eq_dec 2 0); [lia|]; destruct (Z.eq_dec 2 1); [lia|].
  destruct (Z.eq_dec (node_tag n) 3); [contradiction|].
  destruct (Z.eq_dec 3 3); [|contradiction].
  right; exists tr,tt; split; [reflexivity|].
  exists tt,tt; split; [repeat split; auto|].
  exists M',tt; split; [exact Hr|]; split; reflexivity.
Qed.
Lemma close_first_of_two__right_variable : forall M p q n,
  node_at M p n -> p <> q ->
  store_node M p n ** store_world_except2 M p q |-- store_world_except M q.
Proof.
  intros M p q n Hn Hpq.
  unfold store_world_except2, store_world_except, store_map_missing_i.
  Intros l.
  match goal with H : forall a, In a l <-> _ |- _ => rename H into Hl end.
  match goal with H : NoDup l |- _ => rename H into Hnd end.
  assert (Hnotp : ~ In p l).
  { intro Hp; apply Hl in Hp; destruct Hp as [[b Hb] _].
    destruct (Z.eq_dec p p); discriminate || contradiction. }
  assert (Hmap : map (fun a => match (if Z.eq_dec p a then None else RCMap.nodes M a) with
                    | Some b => store_node M a b | None => emp end) l =
                 map (fun a => match RCMap.nodes M a with
                    | Some b => store_node M a b | None => emp end) l).
  { apply map_ext_in; intros a Ha.
    destruct (Z.eq_dec p a); [subst; contradiction|reflexivity]. }
  Exists (p :: l).
  setoid_rewrite Hmap.
  split_pure_spatial.
  - cbn [map]; unfold node_at in Hn; rewrite Hn.
    rewrite logic_equiv_iter_sepcon_cons.
    cancel; reflexivity.
  - split_pures; dump_pre_spatial.
    + intro a; cbn; rewrite Hl.
      destruct (Z.eq_dec p a) as [He|He].
      * subst; split; [intros; split; [eauto|assumption]|auto].
      * split.
        -- intros [Heq|[[b Hb] Hneq]]; [contradiction|split; eauto].
        -- intros [[b Hb] Hneq]; right; split; eauto.
    + constructor; assumption.
Qed.
Lemma retain_result__representative_cleanup : forall M p M',
  retain_rel M p M' -> M' = RCMap.retain M p.
Proof.
  unfold retain_rel, RCMap.retain_program; cbn.
  intros M p M' [u [st [Ha [Hr Hst]]]]. exact Hr.
Qed.
Lemma decode_live__representative_cleanup : forall M p tr,
  decode_type M p tr -> exists n, RCMap.nodes M p = Some n.
Proof.
  intros M p tr; destruct tr; cbn; intros H;
    repeat match type of H with ex _ => destruct H as [? H] end;
    eauto; destruct H as [H _]; eauto.
Qed.
Lemma retained_credit__representative_cleanup : forall B M1 M p,
  rc_valid B -> rc_valid M -> retain_rel B p M1 ->
  rc_reservations_same M1 M -> p <> 0 ->
  rc_reserved M p > 0 /\ exists n, node_at M p n.
Proof.
  intros B M1 M p [HB HBp] [HM HMp] Hret Hsame Hp.
  apply retain_result__representative_cleanup in Hret; subst M1.
  destruct HB as [_ [_ [_ [_ [_ [_ HBres]]]]]].
  destruct HM as [_ [_ [_ [_ [_ [HMdead HMres]]]]]].
  specialize (HBres p). specialize (HMres p).
  specialize (Hsame p). unfold RCMap.retain in Hsame.
  destruct (Z.eq_dec p 0); [contradiction|].
  cbn in Hsame. unfold RCMap.put_count in Hsame.
  destruct (Z.eq_dec p p); [|contradiction].
  unfold rc_reserved; type_rcmap_reduce.
  split; [lia|].
  unfold node_at. destruct (RCMap.nodes M p) as [nd|] eqn:Hnode; [eauto|].
  specialize (HMdead p Hnode); lia.
Qed.
Lemma incoming_app__representative_cleanup : forall es fs p,
  RCMap.incoming node_children (es ++ fs) p =
  RCMap.incoming node_children es p + RCMap.incoming node_children fs p.
Proof.
  intros; unfold RCMap.incoming.
  rewrite map_app, concat_app, count_occ_app, Nat2Z.inj_add. reflexivity.
Qed.
Lemma incoming_cons__representative_cleanup : forall e es p,
  RCMap.incoming node_children (e :: es) p =
  Z.of_nat (count_occ Z.eq_dec (node_children (snd e)) p) +
  RCMap.incoming node_children es p.
Proof.
  intros; unfold RCMap.incoming; cbn [map List.concat].
  rewrite count_occ_app, Nat2Z.inj_add. reflexivity.
Qed.
Lemma incoming_incl__representative_cleanup : forall es fs p,
  NoDup (map fst es) -> incl es fs ->
  RCMap.incoming node_children es p <= RCMap.incoming node_children fs p.
Proof.
  induction es as [|[k n] es IH]; intros fs p Hnd Hin.
  - unfold RCMap.incoming; cbn; lia.
  - inversion Hnd as [|? ? Hnot Htail]; subst.
    destruct (in_split (k,n) fs (Hin (k,n) (or_introl eq_refl))) as [l [r ->]].
    assert (Hincl : incl es (l ++ r)).
    { intros e He. specialize (Hin e (or_intror He)).
      apply in_app_or in Hin; apply in_or_app.
      destruct Hin as [Hin|[Heq|Hin]]; auto.
      subst e. exfalso; apply Hnot. apply in_map with (f:=fst) in He; exact He. }
    specialize (IH (l ++ r) p Htail Hincl).
    rewrite incoming_cons__representative_cleanup.
    rewrite incoming_app__representative_cleanup, incoming_cons__representative_cleanup.
    rewrite incoming_app__representative_cleanup in IH. cbn [snd]; lia.
Qed.
Lemma exact_count_monotone__representative_cleanup : forall B M p,
  rc_valid B -> rc_valid M -> rc_preserves B M ->
  RCMap.counts B p <= RCMap.counts M p.
Proof.
  intros B M p [[HB _] _] [[HM _] _] [Hnodes Hroots].
  destruct HB as [eb [[Hndb Heb] Hcb]].
  destruct HM as [em [[Hndm Hem] Hcm]].
  type_rcmap_reduce.
  assert (Hi : incl eb em).
  { intros [k n] H. apply Hem, Hnodes, Heb, H. }
  pose proof (incoming_incl__representative_cleanup eb em p Hndb Hi).
  rewrite Hcb, Hcm. specialize (Hroots p); lia.
Qed.
Lemma decode_decrement__representative_cleanup : forall M q tr p,
  decode_type (RCMap.decrement M q) p tr = decode_type M p tr.
Proof.
  intros M q tr; induction tr; intros p; cbn; try reflexivity;
    apply f_equal; apply functional_extensionality; intro pl;
    apply f_equal; apply functional_extensionality; intro pr;
    rewrite IHtr1, IHtr2; reflexivity.
Qed.
Lemma solution_cleanup__representative_cleanup : forall M p base s,
  store_solution M base s |-- store_solution (RCMap.decrement M p) base s.
Proof.
  intros M p base s. unfold store_solution.
  assert (He : solution_entry (RCMap.decrement M p) s = solution_entry M s).
  { unfold solution_entry. repeat (apply functional_extensionality; intro).
    destruct (s x0); [rewrite decode_decrement__representative_cleanup|]; reflexivity. }
  rewrite He. Intros l. Exists l.
  split_pure_spatial; [cancel|]. split_pures; dump_pre_spatial; auto.
  apply solution_roots_decrement; assumption.
Qed.
Lemma temporary_release__representative_cleanup : forall B M1 M M' p tr,
  rc_valid B -> rc_valid M1 -> rc_valid M ->
  decode_type B p tr -> retain_rel B p M1 ->
  rc_preserves M1 M -> rc_reservations_same M1 M -> release_rel M p M' ->
  M' = RCMap.decrement M p /\ rc_preserves B M' /\ rc_reservations_same B M'.
Proof.
  intros B M1 M M' p tr HB H1 HM Hdecode Hret Hpres Hsame Hrel.
  unfold rc_preserves, rc_reservations_same in *; type_rcmap_reduce.
  destruct (decode_live__representative_cleanup B p tr Hdecode) as [n Hnode].
  pose proof HB as [[_ [_ [_ [_ [Hlive _]]]]] _].
  specialize (Hlive p n Hnode); destruct Hlive as [Hp Hcount].
  pose proof (exact_count_monotone__representative_cleanup M1 M p H1 HM Hpres) as Hmono.
  type_rcmap_reduce.
  apply retain_result__representative_cleanup in Hret; subst M1.
  assert (Hhigh : 2 <= RCMap.counts M p).
  { unfold RCMap.retain in Hmono; destruct (Z.eq_dec p 0); [contradiction|].
    cbn in Hmono. type_rcmap_reduce. unfold RCMap.put_count in Hmono.
    destruct (Z.eq_dec p p); [lia|contradiction]. }
  assert (HnodeM : RCMap.nodes M p = Some n).
  { apply (proj1 Hpres). unfold RCMap.retain; destruct (Z.eq_dec p 0); exact Hnode. }
  assert (Heq : M' = RCMap.decrement M p).
  { unfold release_rel in Hrel; rewrite type_release_program_eq in Hrel.
    unfold RCMap.release_program in Hrel.
    apply RCMap.release_nrm_unfold in Hrel.
    cbn [RCMap.release_rec] in Hrel.
    type_rcmap_reduce.
    destruct (Z.eq_dec p 0); [contradiction|]. rewrite HnodeM in Hrel.
    destruct (Z.eq_dec (RCMap.counts M p) 1); [lia|].
    apply RCMap.release_nrm_unfold in Hrel.
    cbn [RCMap.release_rec] in Hrel. exact (proj1 Hrel). }
  subst M'; split; [reflexivity|]. split.
  - destruct Hpres as [Hnodes Hroots]. split.
    + intros q nq Hq. apply Hnodes. unfold RCMap.retain;
        destruct (Z.eq_dec p 0); exact Hq.
    + intro q. specialize (Hroots q).
      unfold RCMap.retain in Hroots; destruct (Z.eq_dec p 0); [contradiction|].
      cbn in Hroots |- *. type_rcmap_reduce. unfold RCMap.put_count in *.
      destruct (Z.eq_dec p q); subst; lia.
  - intro q. specialize (Hsame q). unfold RCMap.retain in Hsame.
    destruct (Z.eq_dec p 0); [contradiction|]. cbn in Hsame |- *. type_rcmap_reduce.
    unfold RCMap.put_count in *. destruct (Z.eq_dec p q); subst; lia.
Qed.
Lemma repr_id_compose__representative_cleanup : forall s v tr tr',
  repr_rel_id s v tr -> repr_rel_node s tr tr' -> repr_rel_id s v tr'.
Proof.
  intros s v tr tr' H; revert tr'; induction H; intros tr' Hr.
  - inversion Hr; subst; [assumption|contradiction].
  - inversion Hr; subst; try contradiction.
    apply repr_rel_not_var; assumption.
  - eapply repr_rel_rec; eauto.
Qed.
Lemma repr_compose__representative_cleanup : forall s a b c,
  repr_rel_node s a b -> repr_rel_node s b c -> repr_rel_node s a c.
Proof.
  intros s a b c H1 H2; inversion H1; subst; auto.
  apply repr_rel_node_var. eapply repr_id_compose__representative_cleanup; eauto.
Qed.
Lemma unify_repr_left__representative_cleanup : forall s s' a b c,
  repr_rel_node s a b -> unify_rel b c s s' -> unify_rel a c s s'.
Proof.
  intros s s' a b c Hr Hu. inversion Hu; subst;
    [eapply unify_rel_left_var | eapply unify_rel_right_var |
     eapply unify_rel_apply | eapply unify_rel_arrow | eapply unify_rel_atom];
    eauto using repr_compose__representative_cleanup.
Qed.
Lemma unify_repr_right__representative_cleanup : forall s s' a b c,
  repr_rel_node s b c -> unify_rel a c s s' -> unify_rel a b s s'.
Proof.
  intros s s' a b c Hr Hu. inversion Hu; subst;
    [eapply unify_rel_left_var | eapply unify_rel_right_var |
     eapply unify_rel_apply | eapply unify_rel_arrow | eapply unify_rel_atom];
    eauto using repr_compose__representative_cleanup.
Qed.
Lemma repr_decode__representative_cleanup : forall M s v p M',
  repr_result M s v p M' -> exists tr, decode_type M p tr.
Proof.
  unfold repr_result, repr_choice; cbn.
  intros M s v p M' [q [st1 [H1 [tr [st2 [H2 [u [st3 [Ht [N [st4 [Hret Hr]]]]]]]]]]]].
  destruct Hr as [Heq _]. inversion Heq; subst q N.
  exists tr. cbn in Ht. tauto.
Qed.
Lemma infer_nrm_unfold__representative_cleanup : forall stage p q M s out,
  MonadErr.nrm (infer stage p q M s) tt out tt <->
  MonadErr.nrm (infer_rec infer stage p q M s) tt out tt.
Proof.
  intros stage p q M s out. pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H stage p q M s) as [Hn He]. apply Hn.
Qed.
Lemma infer_repr_left__representative_cleanup : forall B s p q v tr nq pp M1 r M2 s2 M3,
  node_at B p (Node 3 v 0) -> node_at B q nq -> solution_at s v tr ->
  repr_result B s v pp M1 -> infer_result 1 M1 s pp q r M2 s2 ->
  release_rel M2 pp M3 -> infer_result 0 B s p q r M3 s2.
Proof.
  intros B s p q v tr nq pp M1 r M2 s2 M3 Hp Hq Hs Hr Hi Hl.
  unfold infer_result. rewrite infer_nrm_unfold__representative_cleanup.
  unfold infer_rec. unfold node_at in Hp,Hq. rewrite Hp,Hq. cbn [node_tag node_a].
  unfold solution_at in Hs. rewrite Hs. cbn.
  exists (pp,M1),tt; split; [exact Hr|].
  exists (r,M2,s2),tt; split; [exact Hi|].
  exists M3,tt; split; [exact Hl|]. split; reflexivity.
Qed.
Lemma infer_repr_right__representative_cleanup : forall B s p q v tr np pp M1 r M2 s2 M3,
  node_at B q (Node 3 v 0) -> node_at B p np -> solution_at s v tr ->
  repr_result B s v pp M1 -> infer_result 2 M1 s p pp r M2 s2 ->
  release_rel M2 pp M3 -> infer_result 1 B s p q r M3 s2.
Proof.
  intros B s p q v tr np pp M1 r M2 s2 M3 Hq Hp Hs Hr Hi Hl.
  unfold infer_result. rewrite infer_nrm_unfold__representative_cleanup.
  unfold infer_rec. unfold node_at in Hp,Hq. rewrite Hp,Hq. cbn [node_tag node_a].
  unfold solution_at in Hs. rewrite Hs. cbn.
  exists (pp,M1),tt; split; [exact Hr|].
  exists (r,M2,s2),tt; split; [exact Hi|].
  exists M3,tt; split; [exact Hl|]. split; reflexivity.
Qed.
Lemma child_not_parent__release_children : forall M p n q,
  rc_valid M -> node_at M p n -> In q (node_children n) -> p <> q.
Proof.
  intros M p n q [[Hex [Hcl [[rank [Hrank Hedge]] Hrest]]] Hpay] Hn Hq Heq.
  specialize (Hedge p n q Hn Hq). subst; lia.
Qed.
Lemma delete_child_credit__release_children : forall M p n q,
  rc_valid M -> node_at M p n -> In q (node_children n) ->
  0 < rc_reserved (rc_delete M p n) q /\
  exists nq, node_at (rc_delete M p n) q nq.
Proof.
  intros M p n q Hv Hn Hq.
  pose proof (child_not_parent__release_children M p n q Hv Hn Hq) as Hne.
  destruct Hv as [[Hex [Hcl [Hac [Hr [Hl [Hd Hres]]]]]] Hpay].
  destruct (Hcl p n q Hn Hq) as [nq Hnq].
  specialize (Hres q).
  apply (count_occ_In Z.eq_dec) in Hq.
  unfold rc_reserved, rc_delete, node_at, RCMap.delete; cbn.
  type_rcmap_reduce.
  destruct (Z.eq_dec p q); [contradiction|]. split; [lia|eauto].
Qed.
Lemma node_children_binary__release_children : forall n,
  node_tag n = 1 \/ node_tag n = 2 ->
  node_children n = [node_a n; node_b n].
Proof.
  intros n [H|H]; unfold node_children; rewrite H; reflexivity.
Qed.
Lemma release_iter_ind__release_children : forall
    (P : list addr -> RcState -> RcState -> Prop),
  (forall M, P [] M M) ->
  (forall p xs M Mf, p = 0 -> P xs M Mf -> P (p::xs) M Mf) ->
  (forall p xs M Mf, p <> 0 -> RCMap.nodes M p = None ->
    P xs M Mf -> P (p::xs) M Mf) ->
  (forall p xs M n Mf, p <> 0 -> RCMap.nodes M p = Some n ->
    RCMap.counts M p = 1 ->
    P (node_children n ++ xs) (rc_delete M p n) Mf -> P (p::xs) M Mf) ->
  (forall p xs M n Mf, p <> 0 -> RCMap.nodes M p = Some n ->
    RCMap.counts M p <> 1 ->
    P xs (rc_decrement M p) Mf -> P (p::xs) M Mf) ->
  forall xs M Mf, MonadErr.nrm (Rec (RCMap.release_rec node_children) (xs,M)) tt Mf tt ->
    P xs M Mf.
Proof.
  intros P Hnil Hzero Hnone Hdel Hdec.
  assert (Hi : forall k xs M Mf,
    MonadErr.nrm (Init.Nat.iter k (RCMap.release_rec node_children) bot (xs,M)) tt Mf tt ->
    P xs M Mf).
  { induction k as [|k IH]; intros xs M Mf Hrun; [contradiction|].
    change (MonadErr.nrm (RCMap.release_rec node_children
      (Init.Nat.iter k (RCMap.release_rec node_children) bot) (xs,M)) tt Mf tt) in Hrun.
    unfold RCMap.release_rec in Hrun; type_rcmap_reduce.
    destruct xs as [|p xs].
    - destruct Hrun as [-> _]; apply Hnil.
    - destruct (Z.eq_dec p 0) as [Hz|Hz]; [eapply Hzero; eauto|].
      destruct (RCMap.nodes M p) as [n|] eqn:Hn; [|eapply Hnone; eauto].
      destruct (Z.eq_dec (RCMap.counts M p) 1) as [Hc|Hc].
      + eapply Hdel; eauto.
      + eapply Hdec; eauto. }
  intros xs M Mf Hrun.
  destruct Hrun as [k Hk]. eapply Hi; eauto.
Qed.
Lemma release_append__release_children : forall xs M Mid,
  MonadErr.nrm (Rec (RCMap.release_rec node_children) (xs,M)) tt Mid tt ->
  forall ys Mf,
  MonadErr.nrm (Rec (RCMap.release_rec node_children) (ys,Mid)) tt Mf tt ->
  MonadErr.nrm (Rec (RCMap.release_rec node_children) (xs++ys,M)) tt Mf tt.
Proof.
  apply (release_iter_ind__release_children
    (fun xs M Mid => forall ys Mf,
      MonadErr.nrm (Rec (RCMap.release_rec node_children) (ys,Mid)) tt Mf tt ->
      MonadErr.nrm (Rec (RCMap.release_rec node_children) (xs++ys,M)) tt Mf tt)).
  - intros; exact H.
  - intros p xs M Mid Hz IH ys Mf Hrun.
    rewrite RCMap.release_nrm_unfold. cbn [RCMap.release_rec List.app].
    type_rcmap_reduce.
    destruct (Z.eq_dec p 0); [apply IH; exact Hrun|contradiction].
  - intros p xs M Mid Hz Hn IH ys Mf Hrun.
    rewrite RCMap.release_nrm_unfold. cbn [RCMap.release_rec List.app].
    type_rcmap_reduce.
    destruct (Z.eq_dec p 0); [contradiction|]. rewrite Hn. apply IH; exact Hrun.
  - intros p xs M n Mid Hz Hn Hc IH ys Mf Hrun.
    rewrite RCMap.release_nrm_unfold. cbn [RCMap.release_rec List.app].
    type_rcmap_reduce.
    destruct (Z.eq_dec p 0); [contradiction|]. rewrite Hn,Hc.
    destruct (Z.eq_dec 1 1); [|contradiction]. rewrite app_assoc.
    apply IH; exact Hrun.
  - intros p xs M n Mid Hz Hn Hc IH ys Mf Hrun.
    rewrite RCMap.release_nrm_unfold. cbn [RCMap.release_rec List.app].
    type_rcmap_reduce.
    destruct (Z.eq_dec p 0); [contradiction|]. rewrite Hn.
    destruct (Z.eq_dec (RCMap.counts M p) 1); [contradiction|].
    apply IH; exact Hrun.
Qed.
Lemma erase_entries__release_children : forall M es p n,
  RCMap.entries M es -> RCMap.nodes M p = Some n ->
  exists es',
    RCMap.entries (rc_delete M p n) es' /\
    forall q, RCMap.incoming node_children es q =
      RCMap.incoming node_children es' q +
      Z.of_nat (count_occ Z.eq_dec (node_children n) q).
Proof.
  intros M es p n [Hnd Hentries] Hn.
  apply Hentries in Hn. apply in_split in Hn as [xs [ys ->]].
  exists (xs++ys); split.
  - split.
    + rewrite map_app in *. cbn in Hnd.
      eapply NoDup_remove_1; exact Hnd.
    + intros q nq. unfold rc_delete, RCMap.delete; cbn; type_rcmap_reduce.
      destruct (Z.eq_dec p q) as [->|Hne].
      * split; [|discriminate]. intro Hin.
        assert (Hkey : In q (map fst xs ++ map fst ys)).
        { rewrite <- map_app. apply in_map with (f:=@fst addr TypeNode) in Hin.
          exact Hin. }
        rewrite map_app in Hnd; cbn in Hnd.
        exfalso. exact (NoDup_remove_2 _ _ _ Hnd Hkey).
      * rewrite <- Hentries. repeat rewrite in_app_iff. cbn.
        split; intros Hin.
        -- tauto.
        -- destruct Hin as [Hin|[Heq|Hin]]; auto.
           inversion Heq; contradiction.
  - intro q. unfold RCMap.incoming.
    repeat rewrite map_app. cbn [map snd].
    repeat rewrite concat_app. rewrite List.concat_cons.
    repeat rewrite count_occ_app.
    repeat rewrite Nat2Z.inj_add.
    rewrite <- Z.add_assoc. f_equal. apply Z.add_comm.
Qed.
Lemma reserved_budget__release_children : forall M,
  rc_valid M ->
  exists es, RCMap.entries M es /\
    forall q, 0 <= RCMap.reserved M q /\
      RCMap.reserved M q + RCMap.incoming node_children es q <= RCMap.counts M q.
Proof.
  intros M [[ [es [Hentries Hcount]] [Hcl [Hac [Hr [Hl [Hd Hres]]]]]] Hpay].
  exists es; split; [exact Hentries|]. intro q.
  specialize (Hcount q); specialize (Hres q); type_rcmap_reduce; lia.
Qed.
Lemma release_pending_frame__release_children : forall xs M Mf,
  MonadErr.nrm (Rec (RCMap.release_rec node_children) (xs,M)) tt Mf tt ->
  forall protected : addr -> Z,
  (forall q, 0 <= protected q) ->
  (exists es, RCMap.entries M es /\
    forall q, 0 <= RCMap.reserved M q /\
      RCMap.reserved M q + RCMap.incoming node_children es q <= RCMap.counts M q) ->
  (forall q, Z.of_nat (count_occ Z.eq_dec xs q) + protected q <= RCMap.reserved M q) ->
  forall q, protected q <= RCMap.reserved Mf q.
Proof.
  apply (release_iter_ind__release_children
    (fun xs M Mf => forall protected : addr -> Z,
      (forall q, 0 <= protected q) ->
      (exists es, RCMap.entries M es /\
        forall q, 0 <= RCMap.reserved M q /\
          RCMap.reserved M q + RCMap.incoming node_children es q <= RCMap.counts M q) ->
      (forall q, Z.of_nat (count_occ Z.eq_dec xs q) + protected q <= RCMap.reserved M q) ->
      forall q, protected q <= RCMap.reserved Mf q)).
  all: type_rcmap_reduce.
  - intros M protected Hprot Hbudget Hjobs q. specialize (Hjobs q); cbn in Hjobs; lia.
  - intros p xs M Mf Hz IH protected Hprot Hbudget Hjobs.
    apply IH; auto. intro q. specialize (Hjobs q).
    cbn -[Z.eq_dec] in Hjobs. destruct (Z.eq_dec p q); lia.
  - intros p xs M Mf Hz Hn IH protected Hprot Hbudget Hjobs.
    apply IH; auto. intro q. specialize (Hjobs q).
    cbn -[Z.eq_dec] in Hjobs. destruct (Z.eq_dec p q); lia.
  - intros p xs M n Mf Hz Hn Hc IH protected Hprot [es [Hes Hb]] Hjobs.
    destruct (erase_entries__release_children M es p n Hes Hn) as [es' [Hes' Hinc]].
    assert (Hzero : RCMap.incoming node_children es p = 0 /\
      count_occ Z.eq_dec (node_children n) p = 0%nat /\
      count_occ Z.eq_dec xs p = 0%nat /\ protected p = 0).
    { specialize (Hb p); specialize (Hjobs p); specialize (Hprot p).
      pose proof (Hinc p). unfold RCMap.incoming in *.
      cbn -[Z.eq_dec] in Hjobs. destruct (Z.eq_dec p p); [|contradiction]. lia. }
    apply IH with (protected:=protected); [exact Hprot| |].
    + exists es'; split; [exact Hes'|]. intro q.
      specialize (Hb q); specialize (Hinc q).
      unfold rc_delete, RCMap.delete; cbn; unfold RCMap.put_count; type_rcmap_reduce.
      destruct (Z.eq_dec p q) as [<-|Hne].
      * destruct Hzero as [Hzero [Hchild [Htail Hp]]].
        unfold RCMap.incoming in *; lia.
      * lia.
    + intro q. specialize (Hjobs q).
      rewrite count_occ_app, Nat2Z.inj_add.
      unfold rc_delete, RCMap.delete; cbn -[node_children count_occ]; type_rcmap_reduce;
        destruct (Z.eq_dec p q) as [<-|Hne].
      * destruct Hzero as [Hzero [Hchild [Htail Hp]]].
        change (Z.of_nat (count_occ Z.eq_dec (node_children n) p) +
          Z.of_nat (count_occ Z.eq_dec xs p) + protected p <= 0).
        rewrite Hchild, Htail, Hp. lia.
      * rewrite count_occ_cons_neq in Hjobs by exact Hne.
        change (Z.of_nat (count_occ Z.eq_dec (node_children n) q) +
          Z.of_nat (count_occ Z.eq_dec xs q) + protected q <=
          RCMap.reserved M q + Z.of_nat (count_occ Z.eq_dec (node_children n) q)). lia.
  - intros p xs M n Mf Hz Hn Hc IH protected Hprot [es [Hes Hb]] Hjobs.
    apply IH with (protected:=protected); [exact Hprot| |].
    + exists es; split; [exact Hes|]. intro q.
      specialize (Hb q); specialize (Hjobs q); specialize (Hprot q).
      unfold rc_decrement, RCMap.decrement; cbn; unfold RCMap.put_count; type_rcmap_reduce.
      cbn -[Z.eq_dec] in Hjobs. destruct (Z.eq_dec p q); subst; lia.
    + intro q. specialize (Hjobs q).
      unfold rc_decrement, RCMap.decrement; cbn; unfold RCMap.put_count; type_rcmap_reduce.
      cbn -[Z.eq_dec] in Hjobs. destruct (Z.eq_dec p q); subst; lia.
Qed.
Lemma delete_reserves_children__release_children : forall M p n,
  rc_valid M -> node_at M p n ->
  forall q, Z.of_nat (count_occ Z.eq_dec (node_children n) q) <=
    RCMap.reserved (rc_delete M p n) q.
Proof.
  intros M p n Hv Hn q.
  assert (Hself : count_occ Z.eq_dec (node_children n) p = 0%nat).
  { apply (count_occ_not_In Z.eq_dec). intro Hin.
    exact (child_not_parent__release_children M p n p Hv Hn Hin eq_refl). }
  destruct Hv as [[Hex [Hcl [Hac [Hr [Hl [Hd Hres]]]]]] Hpay].
  specialize (Hres q). unfold rc_delete, RCMap.delete; cbn -[node_children count_occ].
  type_rcmap_reduce.
  destruct (Z.eq_dec p q) as [<-|Hne]; [rewrite Hself; lia|lia].
Qed.
Lemma release_second_child__release_children : forall M p n Mf,
  rc_valid M -> node_at M p n -> node_tag n = 1 \/ node_tag n = 2 ->
  rc_valid (rc_delete M p n) ->
  release_rel (rc_delete M p n) (node_a n) Mf -> rc_valid Mf ->
  0 < rc_reserved Mf (node_b n) /\ exists nq, node_at Mf (node_b n) nq.
Proof.
  intros M p n Mf Hv Hn Htag Hd Hrun Hf.
  pose proof (node_children_binary__release_children n Htag) as Hchildren.
  pose proof (delete_reserves_children__release_children M p n Hv Hn) as Hcredit.
  rewrite Hchildren in Hcredit.
  pose proof (release_pending_frame__release_children [node_a n]
    (rc_delete M p n) Mf Hrun
    (fun q => Z.of_nat (count_occ Z.eq_dec [node_b n] q))) as Hframe.
  assert (Hbound : 1 <= RCMap.reserved Mf (node_b n)).
  { specialize (Hframe ltac:(intro q; apply Nat2Z.is_nonneg)
      (reserved_budget__release_children _ Hd)).
    assert (Hjobs : forall q,
      Z.of_nat (count_occ Z.eq_dec [node_a n] q) +
      Z.of_nat (count_occ Z.eq_dec [node_b n] q) <=
      RCMap.reserved (rc_delete M p n) q).
    { intro q. specialize (Hcredit q).
      change ([node_a n;node_b n]) with ([node_a n]++[node_b n]) in Hcredit.
      rewrite count_occ_app, Nat2Z.inj_add in Hcredit. exact Hcredit. }
    specialize (Hframe Hjobs (node_b n)).
    cbn -[Z.eq_dec] in Hframe. destruct (Z.eq_dec (node_b n) (node_b n)); [exact Hframe|contradiction]. }
  unfold rc_reserved; type_rcmap_reduce.
  split; [lia|].
  destruct (RCMap.nodes Mf (node_b n)) as [nq|] eqn:Hq; [exists nq; exact Hq|].
  destruct Hf as [[Hex [Hcl [Hac [Hr [Hl [Hdead Hres]]]]]] Hpay].
  specialize (Hdead _ Hq); specialize (Hres (node_b n)).
  type_rcmap_reduce; lia.
Qed.
Lemma release_binary__release_children : forall M p n M1 M2,
  p <> 0 -> node_at M p n -> rc_count M p - 1 = 0 ->
  node_tag n = 1 \/ node_tag n = 2 ->
  release_rel (rc_delete M p n) (node_a n) M1 ->
  release_rel M1 (node_b n) M2 -> release_rel M p M2.
Proof.
  intros M p n M1 M2 Hp Hn Hc Htag H1 H2.
  unfold release_rel in *; rewrite !type_release_program_eq in *.
  unfold RCMap.release_program in *.
  unfold node_at in Hn; unfold rc_count in Hc; type_rcmap_reduce.
  rewrite RCMap.release_nrm_unfold. cbn [RCMap.release_rec].
  destruct (Z.eq_dec p 0); [contradiction|]. unfold node_at in Hn; rewrite Hn.
  assert (Hc' : RCMap.counts M p = 1) by (unfold rc_count in Hc; lia).
  rewrite Hc'. destruct (Z.eq_dec 1 1); [|contradiction].
  rewrite (node_children_binary__release_children n Htag), app_nil_r.
  exact (release_append__release_children [node_a n] (rc_delete M p n) M1 H1
    [node_b n] M2 H2).
Qed.
Lemma delete_entries__release_delete : forall (N : Type) (ch : N -> list addr)
  (M : @RCMap.t N) p n es,
  RCMap.entries M es -> RCMap.nodes M p = Some n ->
  exists ds, RCMap.entries (RCMap.delete ch M p n) ds /\
    forall q, RCMap.incoming ch es q = RCMap.incoming ch ds q +
      Z.of_nat (count_occ Z.eq_dec (ch n) q).
Proof.
  intros N ch M p n es [Hnd He] Hp.
  assert (Hin : In (p,n) es) by (apply He; exact Hp).
  apply in_split in Hin. destruct Hin as [l [r ->]].
  exists (l ++ r).
  assert (Hnd' : NoDup (map fst l ++ map fst r)).
  { rewrite map_app in Hnd. cbn in Hnd. apply NoDup_remove in Hnd. tauto. }
  assert (Hnot : ~ In p (map fst l ++ map fst r)).
  { rewrite map_app in Hnd. cbn in Hnd. apply NoDup_remove in Hnd. tauto. }
  split.
  - split; [rewrite map_app; exact Hnd'|].
    intros q nq; cbn. destruct (Z.eq_dec p q) as [->|Hneq].
    + split; [|discriminate]. intro H.
      exfalso. apply Hnot. rewrite <- map_app. apply in_map with (f:=fst) in H. exact H.
    + rewrite <- He. rewrite !in_app_iff. cbn.
      split; [tauto|]. intros [Hl|[Heq|Hr]]; [auto| |auto].
      inversion Heq; contradiction.
  - intro q. unfold RCMap.incoming. rewrite !map_app, !concat_app.
    cbn [map List.concat snd]. rewrite !count_occ_app. rewrite !Nat2Z.inj_add.
    rewrite <- Z.add_assoc. f_equal. apply Z.add_comm.
Qed.
Lemma incoming_edge_positive__release_delete : forall (N : Type)
  (ch : N -> list addr) es p n q,
  In (p,n) es -> In q (ch n) -> 0 < RCMap.incoming ch es q.
Proof.
  intros N ch es p n q Hp Hq. unfold RCMap.incoming.
  assert (Hin : In q (List.concat (map (fun e => ch (snd e)) es))).
  { apply in_concat. exists (ch n). split; [|exact Hq].
    apply in_map_iff. exists (p,n); auto. }
  apply (proj1 (count_occ_In Z.eq_dec _ _)) in Hin. lia.
Qed.
Lemma delete_valid__release_delete : forall (N : Type) (ch : N -> list addr)
  (M : @RCMap.t N) p n,
  RCMap.valid ch M -> RCMap.nodes M p = Some n ->
  RCMap.counts M p = 1 -> 0 < RCMap.reserved M p ->
  RCMap.valid ch (RCMap.delete ch M p n).
Proof.
  intros N ch M p n [Hex [Hcl [Hac [Hr [Hl [Hd Hres]]]]]] Hp Hc Hrp.
  destruct Hex as [es [Hes Hcount]].
  assert (Hip : RCMap.incoming ch es p = 0).
  { specialize (Hcount p). specialize (Hres p).
    unfold RCMap.incoming in Hcount |- *. lia. }
  assert (Hnone : forall x nx, RCMap.nodes M x = Some nx -> ~ In p (ch nx)).
  { intros x nx Hx Hin.
    pose proof (incoming_edge_positive__release_delete N ch es x nx p
      (proj2 (proj2 Hes x nx) Hx) Hin). lia. }
  destruct (delete_entries__release_delete N ch M p n es Hes Hp) as [ds [Hds Hi]].
  split.
  - exists ds; split; [exact Hds|].
    intro q; cbn; unfold RCMap.put_count.
    destruct (Z.eq_dec p q) as [->|Hneq].
    + specialize (Hi q). unfold RCMap.incoming in *. lia.
    + specialize (Hi q); specialize (Hcount q); lia.
  - split.
    + intros q nq x Hq Hx. cbn in Hq |- *.
      destruct (Z.eq_dec p q); [discriminate|].
      destruct (Hcl q nq x Hq Hx) as [nx Hnx]. exists nx.
      destruct (Z.eq_dec p x) as [->|Hne]; [exfalso; exact (Hnone q nq Hq Hx)|exact Hnx].
    + split.
      * destruct Hac as [rank [Hnon Hrank]]. exists rank; split.
        -- intros q nq Hq. cbn in Hq. destruct (Z.eq_dec p q); [discriminate|eauto].
        -- intros q nq x Hq Hx. cbn in Hq. destruct (Z.eq_dec p q); [discriminate|eauto].
      * split.
        -- intro q; cbn. destruct (Z.eq_dec p q); [lia|]. specialize (Hr q). lia.
        -- split.
           ++ intros q nq Hq. cbn in Hq |- *. unfold RCMap.put_count.
              destruct (Z.eq_dec p q); [discriminate|eauto].
           ++ split.
              ** intros q Hq; cbn in Hq |- *; unfold RCMap.put_count.
                 destruct (Z.eq_dec p q) as [Heq|Hneq]; [auto|].
                 destruct (Hd q Hq) as [Hcq Hrq]. rewrite Hcq, Hrq.
                 assert (Hnin : ~ In q (ch n)).
                 { intro Hin. destruct (Hcl p n q Hp Hin) as [nq Hnq]. congruence. }
                 apply (proj1 (count_occ_not_In Z.eq_dec _ _)) in Hnin.
                 rewrite Hnin. cbn; auto.
              ** intro q; cbn. destruct (Z.eq_dec p q); [lia|].
                 specialize (Hres q). lia.
Qed.
Lemma rc_delete_valid__release_delete : forall M p n,
  rc_valid M -> node_at M p n -> rc_count M p = 1 -> 0 < rc_reserved M p ->
  rc_valid (rc_delete M p n).
Proof.
  intros M p n [Hv Hpay] Hp Hc Hr. split.
  - apply delete_valid__release_delete; assumption.
  - intros q nq Hq. cbn in Hq. destruct (Z.eq_dec p q); [discriminate|eauto].
Qed.
Lemma delete_world__release_delete : forall M p n,
  store_world_except M p |-- store_world (rc_delete M p n).
Proof.
  intros M p n. unfold store_world_except, store_world, store_map_missing_i, store_map.
  type_rcmap_reduce.
  Intros l. Exists l.
  assert (Heq : map (fun q => match RCMap.nodes M q with
      Some nq => store_node M q nq | None => emp end) l =
    map (fun q => match RCMap.nodes (rc_delete M p n) q with
      Some nq => store_node (rc_delete M p n) q nq | None => emp end) l).
  { apply map_ext_in. intros q Hq. apply H in Hq. destruct Hq as [[nq Hnq] Hneq].
    unfold rc_delete, RCMap.delete, store_node; cbn; unfold RCMap.put_count.
    destruct (Z.eq_dec p q); [congruence|reflexivity]. }
  type_rcmap_reduce.
  split_pure_spatial.
  - rewrite <- Heq. cancel.
  - split_pures; dump_pre_spatial; [|assumption].
    intro q. rewrite H. cbn. destruct (Z.eq_dec p q) as [->|Hneq].
    + split; [intros [_ Hbad]; contradiction|intros [? Hbad]; discriminate].
    + split; [tauto|intro Hq; split; [exact Hq|congruence]].
Qed.
Lemma release_leaf__release_delete : forall M p n,
  p <> 0 -> node_at M p n -> rc_count M p = 1 ->
  node_tag n <> 1 -> node_tag n <> 2 -> release_rel M p (rc_delete M p n).
Proof.
  intros M p n Hp Hn Hc H1 H2.
  assert (Hch : node_children n = []).
  { unfold node_children. apply Z.eqb_neq in H1. apply Z.eqb_neq in H2.
    rewrite H1, H2. reflexivity. }
  unfold release_rel; rewrite type_release_program_eq; unfold RCMap.release_program.
  apply RCMap.release_nrm_unfold. cbn [RCMap.release_rec].
  unfold node_at in Hn; unfold rc_count in Hc; type_rcmap_reduce.
  destruct (Z.eq_dec p 0); [contradiction|].
  unfold node_at in Hn. rewrite Hn. unfold rc_count in Hc. rewrite Hc.
  destruct (Z.eq_dec 1 1); [|contradiction]. rewrite Hch. cbn [app].
  apply RCMap.release_nrm_unfold. cbn [RCMap.release_rec].
  unfold Monad.ret. cbn. split; reflexivity.
Qed.
Lemma same_return_final_bridge__final_compression :
  forall M Mpost p q tr1 tr2 raw compressed_pre rawpost res r,
  store_type M p tr1 -> store_type M q tr2 ->
  sol_compress_to raw compressed_pre -> sol_no_loop raw ->
  sol_finite compressed_pre -> rc_valid Mpost -> rc_preserves M Mpost ->
  (r = 0 -> forall t1 t2,
    store_type M p t1 /\ store_type M q t2 ->
    unify_rel t1 t2 raw rawpost) ->
  store_world Mpost ** store_solution Mpost res rawpost |--
  (EX compressed_post : sol,
    “ r = 0 ” &&
    “ sol_correct_iter tr1 tr2 compressed_pre compressed_post ” &&
    “ rc_valid Mpost ” && “ rc_preserves M Mpost ” &&
    “ store_type Mpost p tr1 ” && “ store_type Mpost q tr2 ” &&
    store_world Mpost ** store_compressed_solution Mpost res compressed_post)
  ||
  (“ r <> 0 ” && “ rc_valid Mpost ” &&
    “ rc_preserves M Mpost ” &&
    “ store_type Mpost p tr1 ” && “ store_type Mpost q tr2 ” &&
    store_world Mpost ** store_solution Mpost res rawpost).
Proof.
  intros M Mpost p q tr1 tr2 raw compressed_pre rawpost res r
    Hp Hq Hcomp Hloop Hfinite Hvalid Hpres Hmath.
  assert (Hp' : store_type Mpost p tr1).
  { eapply decode_type_preserves; eauto. }
  assert (Hq' : store_type Mpost q tr2).
  { eapply decode_type_preserves; eauto. }
  destruct (Z.eq_dec r 0) as [Hz|Hnz].
  - pose proof (Hmath Hz tr1 tr2 (conj Hp Hq)) as Hu.
    destruct (unify_soundness tr1 tr2 raw rawpost compressed_pre
      Hcomp Hloop Hfinite Hu) as [sc [Hc [Hl [Hf Hcorrect]]]].
    Left. Exists sc.
    unfold store_compressed_solution. Exists rawpost.
    split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; tauto.
  - Right. split_pure_spatial.
    + cancel.
    + repeat split_pures; dump_pre_spatial; tauto.
Qed.
Lemma preserves_trans__app_success : forall A B C,
  rc_preserves A B -> rc_preserves B C -> rc_preserves A C.
Proof.
  unfold rc_preserves, RCMap.preserves; intros A B C [H1 R1] [H2 R2].
  split; [eauto | intro p; specialize (R1 p); specialize (R2 p); lia].
Qed.
Lemma node_stable__app_success : forall M Mc p n nc,
  rc_preserves M Mc -> node_at M p n -> node_at Mc p nc -> n = nc.
Proof.
  unfold rc_preserves, RCMap.preserves, node_at.
  intros M Mc p n nc [H _] Hn Hnc. specialize (H p n Hn);
    type_rcmap_reduce; congruence.
Qed.
Lemma decode_app__app_success : forall M p n tr,
  node_at M p n -> node_tag n = 2 -> store_type M p tr ->
  exists a b, tr = TApply a b /\
    store_type M (node_a n) a /\ store_type M (node_b n) b.
Proof.
  intros M p n tr Hn Htag Htr.
  unfold store_type in *; destruct tr; cbn in Htr;
    unfold node_at in Hn.
  - rewrite Hn in Htr; inversion Htr; subst; discriminate.
  - rewrite Hn in Htr; inversion Htr; subst; discriminate.
  - destruct Htr as [pl [pr [H [Hl Hr]]]].
    rewrite Hn in H; inversion H; subst.
    eexists; eexists; cbn; repeat split; eauto.
  - destruct Htr as [pl [pr [H [Hl Hr]]]].
    rewrite Hn in H; inversion H; subst; discriminate.
Qed.
Lemma binary_math_composition__app_success : forall M Mc s sc sf p q n m t u,
  rc_preserves M Mc -> node_at M p n -> node_at M q m ->
  node_tag n = 2 -> node_tag m = 2 ->
  store_type M p t -> store_type M q u ->
  (forall a b, store_type M (node_a n) a /\ store_type M (node_a m) b ->
     unify_rel a b s sc) ->
  (forall a b, store_type Mc (node_b n) a /\ store_type Mc (node_b m) b ->
     unify_rel a b sc sf) ->
  unify_rel t u s sf.
Proof.
  intros M Mc s sc sf p q n m t u HP Hn Hm Htn Htm Ht Hu Hfirst Hsecond.
  destruct (decode_app__app_success M p n t Hn Htn Ht) as [a [b [-> [Ha Hb]]]].
  destruct (decode_app__app_success M q m u Hm Htm Hu) as [c [d [-> [Hc Hd]]]].
  eapply unify_rel_apply with (s1:=sc).
  - apply repr_rel_node_not_var; exact I.
  - apply repr_rel_node_not_var; exact I.
  - apply Hfirst; auto.
  - apply Hsecond; split; eapply decode_type_preserves; eauto.
Qed.
Lemma infer_binary_normal__app_success : forall M Mc Mf s sc sf p q n m r,
  node_at M p n -> node_at M q m -> node_tag n = 2 -> node_tag m = 2 ->
  infer_result 0 M s (node_a n) (node_a m) 0 Mc sc ->
  infer_result 0 Mc sc (node_b n) (node_b m) r Mf sf ->
  infer_result 2 M s p q r Mf sf.
Proof.
  intros M Mc Mf s sc sf p q n m r Hn Hm Htn Htm Hfirst Hsecond.
  unfold infer_result in *.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H 2 p q M s) as [Hnormal Herr].
  apply Hnormal. unfold infer_rec; unfold node_at in Hn,Hm.
  rewrite Hn,Hm,Htn,Htm; cbn.
  exists (0,Mc,sc), tt; split; assumption.
Qed.
Lemma node_preserved_unique__arrow_success : forall M Mc p n nc,
  rc_preserves M Mc -> node_at M p n -> node_at Mc p nc -> n = nc.
Proof.
  intros M Mc p n nc [Hp Hr] Hn Hc.
  unfold node_at in *; specialize (Hp p n Hn); type_rcmap_reduce; congruence.
Qed.
Lemma decode_arrow__arrow_success : forall M p n t,
  node_at M p n -> node_tag n = 1 -> store_type M p t ->
  exists a b, t = TArrow a b /\ store_type M (node_a n) a /\
    store_type M (node_b n) b.
Proof.
  intros M p n t Hn Htag Ht.
  unfold node_at in Hn; unfold store_type in *.
  destruct t; cbn in Ht;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H as [? H]
    | H : _ /\ _ |- _ => destruct H
    end;
    match goal with H : TypeRCMap.nodes M p = Some _ |- _ =>
      rewrite Hn in H; inversion H; subst
    end; cbn in *; try discriminate.
  do 2 eexists; repeat split; eauto.
Qed.
Lemma binary_math_composition__arrow_success : forall M Mc p q n1 n2 s sc sf a b,
  rc_preserves M Mc -> node_at M p n1 -> node_at M q n2 ->
  node_tag n1 = 1 -> node_tag n2 = 1 ->
  store_type M p a -> store_type M q b ->
  (forall x y, store_type M (node_a n1) x /\ store_type M (node_a n2) y ->
    unify_rel x y s sc) ->
  (forall x y, store_type Mc (node_b n1) x /\ store_type Mc (node_b n2) y ->
    unify_rel x y sc sf) -> unify_rel a b s sf.
Proof.
  intros M Mc p q n1 n2 s sc sf a b Hp Hn1 Hn2 Htag1 Htag2 Ha Hb Hfirst Hsecond.
  destruct (decode_arrow__arrow_success M p n1 a Hn1 Htag1 Ha) as [a1 [a2 [-> [Ha1 Ha2]]]].
  destruct (decode_arrow__arrow_success M q n2 b Hn2 Htag2 Hb) as [b1 [b2 [-> [Hb1 Hb2]]]].
  eapply unify_rel_arrow with (s1 := sc).
  - apply repr_rel_node_not_var; cbn; auto.
  - apply repr_rel_node_not_var; cbn; auto.
  - apply Hfirst; auto.
  - apply Hsecond; split; eapply decode_type_preserves; eauto.
Qed.
Lemma infer_normal_unfold__arrow_success : forall stage p q M s r Mf sf,
  infer_result stage M s p q r Mf sf <->
  MonadErr.nrm (infer_rec infer stage p q M s) tt (r,Mf,sf) tt.
Proof.
  intros stage p q M s r Mf sf. unfold infer_result.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H stage p q M s) as [Hn He].
  apply Hn.
Qed.
Lemma infer_binary_normal__arrow_success : forall M Mc Mf p q n1 n2 s sc sf r,
  node_at M p n1 -> node_at M q n2 -> node_tag n1 = 1 -> node_tag n2 = 1 ->
  infer_result 0 M s (node_a n1) (node_a n2) 0 Mc sc ->
  infer_result 0 Mc sc (node_b n1) (node_b n2) r Mf sf ->
  infer_result 2 M s p q r Mf sf.
Proof.
  intros M Mc Mf p q n1 n2 s sc sf r H1 H2 T1 T2 U1 U2.
  rewrite infer_normal_unfold__arrow_success.
  unfold infer_rec; unfold node_at in H1,H2; rewrite H1,H2,T1,T2.
  cbn.
  exists (0,Mc,sc), tt; split; [exact U1 | exact U2].
Qed.
Lemma infer_nrm_unfold__binary_failure : forall stage p q M s out,
  MonadErr.nrm (infer stage p q M s) tt out tt <->
  MonadErr.nrm (infer_rec infer stage p q M s) tt out tt.
Proof.
  intros stage p q M s out.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H stage p q M s) as [Hn He].
  apply Hn.
Qed.
Lemma infer_binary_failure__binary_failure : forall M s p q np nq r M' s',
  node_at M p np -> node_at M q nq ->
  node_tag np = node_tag nq ->
  (node_tag np = 1 \/ node_tag np = 2) ->
  r <> 0 ->
  infer_result 0 M s (node_a np) (node_a nq) r M' s' ->
  infer_result 2 M s p q r M' s'.
Proof.
  intros M s p q np nq r M' s' Hp Hq Htag Hbin Hr Hchild.
  unfold node_at in Hp,Hq.
  unfold infer_result in *.
  rewrite infer_nrm_unfold__binary_failure.
  unfold infer_rec; rewrite Hp,Hq.
  destruct Hbin as [Ht|Ht]; rewrite <- Htag,Ht; cbn.
  all: exists (r,M',s'), tt; split; [exact Hchild|].
  all: destruct (Z.eq_dec r 0); [contradiction|]; cbn; split; reflexivity.
Qed.
Lemma live_preserved_node__binary_checkpoints :
  forall M p n, rc_valid M -> node_at M p n -> rc_count M p > 0.
Proof.
  intros M p n [[He [Hc [Ha [Hr [Hl Hrest]]]]] Hn] Hnode.
  specialize (Hl p n Hnode).
  unfold rc_count; type_rcmap_reduce; lia.
Qed.
Lemma decode_binary_children__binary_first_call : forall M p tr n,
  store_type M p tr -> node_at M p n ->
  (node_tag n = 1 \/ node_tag n = 2) ->
  exists l r, store_type M (node_a n) l /\ store_type M (node_b n) r.
Proof.
  intros M p tr [tag a b] Hd Hn Htag.
  unfold store_type in *; unfold node_at in Hn; simpl in Htag.
  destruct tr; simpl in Hd.
  - rewrite Hn in Hd; inversion Hd; subst; lia.
  - rewrite Hn in Hd; inversion Hd; subst; lia.
  - destruct Hd as [pl [pr [He [Hl Hr]]]].
    rewrite Hn in He; inversion He; subst.
    exists tr1, tr2; exact (conj Hl Hr).
  - destruct Hd as [pl [pr [He [Hl Hr]]]].
    rewrite Hn in He; inversion He; subst.
    exists tr1, tr2; exact (conj Hl Hr).
Qed.
Lemma binary_first_capacity__binary_first_call : forall M s p q n1 n2,
  node_at M p n1 -> node_at M q n2 ->
  node_tag n1 = node_tag n2 ->
  (node_tag n1 = 1 \/ node_tag n1 = 2) ->
  rc_capacity 2 M s p q ->
  rc_capacity 0 M s (node_a n1) (node_a n2).
Proof.
  intros M s p q [tag a b] [tag' c d] Hp Hq He Htag Hcap.
  simpl in He, Htag; subst tag'.
  unfold node_at in Hp, Hq.
  unfold rc_capacity in *.
  rewrite infer_err_unfold in Hcap.
  unfold infer_rec in Hcap; rewrite Hp, Hq in Hcap.
  destruct Htag as [Ht|Ht]; subst tag; cbn in Hcap;
    intro Herr; apply Hcap; left; exact Herr.
Qed.
Lemma binary_second_capacity__binary_second_call :
  forall M s p q np nq Mc sc,
  node_at M p np -> node_at M q nq ->
  node_tag np = node_tag nq ->
  (node_tag np = 1 \/ node_tag np = 2) ->
  rc_capacity 2 M s p q ->
  infer_result 0 M s (node_a np) (node_a nq) 0 Mc sc ->
  rc_capacity 0 Mc sc (node_b np) (node_b nq).
Proof.
  intros M s p q np nq Mc sc Hp Hq Htag Hbinary Hcap Hfirst Herr.
  apply Hcap. apply infer_err_unfold.
  unfold infer_rec; unfold node_at in Hp,Hq; rewrite Hp,Hq.
  destruct Hbinary as [Hbinary|Hbinary];
    rewrite <- Htag, Hbinary; cbn;
    right; exists (0,Mc,sc), tt; split; assumption.
Qed.
Lemma preserved_node__binary_second_call : forall M Mc p n nc,
  rc_preserves M Mc -> node_at M p n -> node_at Mc p nc -> n = nc.
Proof.
  intros M Mc p n nc [Hnodes Hroots] Hn Hnc.
  unfold node_at in *; specialize (Hnodes p n Hn);
    type_rcmap_reduce; congruence.
Qed.
Lemma preserved_children__binary_second_call : forall M Mc p n nc tr,
  rc_preserves M Mc -> node_at M p n -> node_at Mc p nc ->
  (node_tag n = 1 \/ node_tag n = 2) -> store_type M p tr ->
  exists a b, store_type Mc (node_a nc) a /\ store_type Mc (node_b nc) b.
Proof.
  intros M Mc p n nc tr Hpres Hnode Hcurrent Htag Htype.
  assert (n = nc) by (eapply preserved_node__binary_second_call; eauto).
  subst nc. unfold store_type in *.
  destruct tr; cbn in Htype;
    try (unfold node_at in Hnode; rewrite Hnode in Htype;
      inversion Htype; subst n; cbn in Htag; lia).
  all: destruct Htype as [pa [pb [Htree [Ha Hb]]]];
    unfold node_at in Hnode; rewrite Hnode in Htree;
    inversion Htree; subst n; cbn;
    eexists; eexists; split; eapply decode_type_preserves; eauto.
Qed.
Lemma second_call_ready__binary_second_call :
  forall M Mc p q np nq cp cq tr1 tr2 s sc,
  rc_preserves M Mc ->
  node_at M p np -> node_at M q nq ->
  node_at Mc p cp -> node_at Mc q cq ->
  node_tag np = node_tag nq ->
  (node_tag np = 1 \/ node_tag np = 2) ->
  store_type M p tr1 -> store_type M q tr2 ->
  rc_capacity 2 M s p q ->
  infer_result 0 M s (node_a np) (node_a nq) 0 Mc sc ->
  exists a b,
    rc_capacity 0 Mc sc (node_b cp) (node_b cq) /\
    store_type Mc (node_b cq) b /\ store_type Mc (node_b cp) a.
Proof.
  intros M Mc p q np nq cp cq tr1 tr2 s sc
    Hpres Hp Hq Hcp Hcq Htag Hbinary Htr1 Htr2 Hcap Hfirst.
  assert (Hbinq : node_tag nq = 1 \/ node_tag nq = 2) by lia.
  destruct (preserved_children__binary_second_call M Mc p np cp tr1
    Hpres Hp Hcp Hbinary Htr1) as [al [a [Hal Ha]]].
  destruct (preserved_children__binary_second_call M Mc q nq cq tr2
    Hpres Hq Hcq Hbinq Htr2) as [bl [b [Hbl Hb]]].
  exists a,b; split; [|auto].
  assert (np = cp) by (eapply preserved_node__binary_second_call; eauto).
  assert (nq = cq) by (eapply preserved_node__binary_second_call; eauto).
  subst cp cq.
  exact (binary_second_capacity__binary_second_call M s p q np nq Mc sc
    Hp Hq Htag Hbinary Hcap Hfirst).
Qed.
Lemma retain_normal__copy_update : forall M p M',
  retain_rel M p M' <->
  (p = 0 \/ RCMap.counts M p < 2147483647) /\ M' = RCMap.retain M p.
Proof.
  intros M p M'; unfold retain_rel, RCMap.retain_program; cbn.
  split.
  - intros [x [u [[Hcap Hu] [HM Htt]]]]. split; auto.
  - intros [Hcap ->]. exists tt, tt; repeat split; auto.
Qed.
Lemma retain_valid__copy_update : forall M p n,
  rc_valid M -> node_at M p n -> RCMap.counts M p < 2147483647 ->
  rc_valid (RCMap.retain M p).
Proof.
  intros M p n [Hv Hp] Hn Hcap. split.
  - apply RCMap.retain_valid; [exact Hv|right; split; [exists n; exact Hn|exact Hcap]].
  - unfold RCMap.retain; destruct (Z.eq_dec p 0); exact Hp.
Qed.
Lemma retain_except__copy_update : forall M p,
  store_world_except M p |-- store_world_except (RCMap.retain M p) p.
Proof.
  intros M p; unfold RCMap.retain; destruct (Z.eq_dec p 0); [cancel|].
  unfold store_world_except, store_map_missing_i. Intros l.
  Exists l. split_pure_spatial.
  - assert (Heq :
      map (fun q => match RCMap.nodes M q with Some n => store_node M q n | None => emp end) l =
      map (fun q => match RCMap.nodes M q with Some n =>
        store_node (RCMap.make (RCMap.nodes M)
          (RCMap.put_count (RCMap.roots M) p (RCMap.roots M p + 1))
          (RCMap.put_count (RCMap.counts M) p (RCMap.counts M p + 1))
          (RCMap.put_count (RCMap.reserved M) p (RCMap.reserved M p + 1))) q n
        | None => emp end) l).
    { apply map_ext_in; intros q Hq. apply H in Hq. destruct Hq as [Hq Hneq].
      destruct (RCMap.nodes M q); [|reflexivity].
      unfold store_node; cbn; unfold RCMap.put_count.
      destruct (Z.eq_dec p q); [congruence|reflexivity]. }
    type_rcmap_reduce; cbn [RCMap.nodes]. rewrite <- Heq. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.
Lemma retain_world_count__copy_update : forall M p,
  p <> 0 ->
  (&(p # "atype" ->ₛ "refcnt") # Int |-> (RCMap.counts M p + 1)) **
  store_world_without_count M p |-- store_world (RCMap.retain M p).
Proof.
  intros M p Hp. unfold store_world_without_count. Intros n.
  sep_apply (retain_except__copy_update M p).
  assert (Hnode : RCMap.nodes (RCMap.retain M p) p = Some n).
  { unfold RCMap.retain; destruct (Z.eq_dec p 0); auto. }
  unfold store_world.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node (RCMap.retain M p)) p n
    (RCMap.nodes (RCMap.retain M p)) Hnode).
  unfold store_world_except, store_node.
  type_rcmap_reduce.
  unfold RCMap.retain; destruct (Z.eq_dec p 0); [contradiction|].
  cbn [RCMap.counts]. unfold RCMap.put_count; destruct (Z.eq_dec p p); [cancel|contradiction].
Qed.
Lemma var_world_close__copy_update : forall M p v,
  node_at M p (Node 3 v 0) ->
  (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> v) **
  store_world_without_payload M p (Node 3 v 0) |-- store_world M.
Proof.
  intros M p v Hn. unfold store_world, store_world_without_payload, store_world_except.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node M) p (Node 3 v 0) (RCMap.nodes M) Hn).
  unfold store_node, store_node_payload; type_rcmap_reduce; cbn; cancel; reflexivity.
Qed.
Lemma var_world_open__copy_update : forall M p v,
  node_at M p (Node 3 v 0) ->
  store_world M |--
  (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> v) **
  store_world_without_payload M p (Node 3 v 0).
Proof.
  intros M p v Hn. sep_apply (store_world_open M p (Node 3 v 0) Hn).
  unfold store_world_without_payload, store_node, store_node_payload; cbn; repeat cancel; reflexivity.
Qed.
Lemma release_null__release_scalar : forall M : RcState, release_rel M 0 M.
Proof.
  intro M. unfold release_rel; rewrite type_release_program_eq; unfold RCMap.release_program.
  type_rcmap_reduce.
  rewrite RCMap.release_nrm_unfold.
  change (MonadErr.nrm (Rec (RCMap.release_rec node_children) (nil, M)) tt M tt).
  rewrite RCMap.release_nrm_unfold. cbn. split; reflexivity.
Qed.
Lemma decrement_valid__release_decrement_open : forall {N : Type}
    (children : N -> list addr) (M : @RCMap.t N) p n,
  RCMap.valid children M -> RCMap.nodes M p = Some n ->
  0 < RCMap.reserved M p -> 1 < RCMap.counts M p ->
  RCMap.valid children (RCMap.decrement M p).
Proof.
  intros N children M p n Hv Hnode Hres Hcount.
  destruct Hv as [Hex [Hcl [Hac [Hr [Hl [Hd Hrs]]]]]].
  split.
  - destruct Hex as [es [He Hc]]. exists es; split; [exact He|].
    intro q; cbn; unfold RCMap.put_count.
    destruct (Z.eq_dec p q); subst; specialize (Hc q); lia.
  - split; [exact Hcl|]. split; [exact Hac|]. split.
    + intro q; cbn; unfold RCMap.put_count.
      destruct (Z.eq_dec p q); subst; specialize (Hr q); specialize (Hrs q); lia.
    + split.
      * intros q nq Hq; cbn in Hq |- *; unfold RCMap.put_count.
        destruct (Z.eq_dec p q); subst; specialize (Hl q nq Hq); lia.
      * split.
        -- intros q Hq; cbn in Hq |- *; unfold RCMap.put_count.
           destruct (Z.eq_dec p q); subst; [congruence|auto].
        -- intro q; cbn; unfold RCMap.put_count.
           destruct (Z.eq_dec p q); subst; specialize (Hrs q); lia.
Qed.
Lemma rc_decrement_valid__release_decrement_open : forall M p n,
  rc_valid M -> node_at M p n -> 0 < rc_reserved M p ->
  1 < rc_count M p -> rc_valid (rc_decrement M p).
Proof.
  intros M p n [Hv Hp] Hn Hr Hc; split.
  - eapply decrement_valid__release_decrement_open; eauto.
  - exact Hp.
Qed.
Lemma reserved_live__release_decrement_open : forall M p,
  rc_valid M -> 0 < rc_reserved M p -> exists n, node_at M p n.
Proof.
  intros M p [[Hex [Hcl [Hac [Hr [Hl [Hd Hrs]]]]]] Hp] Hres.
  destruct (RCMap.nodes M p) as [n|] eqn:Hn; [exists n; exact Hn|].
  specialize (Hd p Hn); specialize (Hrs p); unfold rc_reserved in Hres;
    type_rcmap_reduce; lia.
Qed.
Lemma missing_decrement__release_decrement_open : forall M p,
  store_world_except M p |-- store_world_except (RCMap.decrement M p) p.
Proof.
  intros M p; unfold store_world_except, store_map_missing_i.
  Intros l. Exists l.
  assert (Heq :
    map (fun q => match RCMap.nodes M q with
      | Some n => store_node M q n | None => emp end) l =
    map (fun q => match RCMap.nodes (RCMap.decrement M p) q with
      | Some n => store_node (RCMap.decrement M p) q n | None => emp end) l).
  { apply map_ext_in. intros q Hq.
    assert (Hneq : q <> p) by (apply H in Hq; tauto).
    unfold store_node; cbn; unfold RCMap.put_count.
    destruct (Z.eq_dec p q); [congruence|reflexivity]. }
  type_rcmap_reduce; rewrite Heq. split_pure_spatial; [cancel|].
  split_pures; dump_pre_spatial; assumption.
Qed.
Lemma decrement_world__release_decrement_open : forall M p n,
  node_at M p n ->
  (&(p # "atype" ->ₛ "refcnt") # Int |-> (rc_count M p - 1)) **
  store_node_payload p n ** store_world_except M p |--
  store_world (rc_decrement M p).
Proof.
  intros M p n Hn.
  sep_apply (missing_decrement__release_decrement_open M p).
  unfold store_world, rc_decrement.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node (RCMap.decrement M p)) p n
    (RCMap.nodes (RCMap.decrement M p)) Hn).
  unfold store_node, rc_count; type_rcmap_reduce; cbn; unfold RCMap.put_count.
  destruct (Z.eq_dec p p); [cancel|contradiction].
  change (store_world_except (RCMap.decrement M p) p |--
    store_world_except (RCMap.decrement M p) p). cancel; reflexivity.
Qed.
Lemma release_decrement_rel__release_decrement_open : forall M p n,
  p <> 0 -> node_at M p n -> rc_count M p <> 1 ->
  release_rel M p (rc_decrement M p).
Proof.
  intros M p n Hp Hn Hc.
  unfold release_rel; rewrite type_release_program_eq; unfold RCMap.release_program.
  unfold node_at in Hn; unfold rc_count in Hc; type_rcmap_reduce.
  rewrite RCMap.release_nrm_unfold.
  cbn [RCMap.release_rec].
  destruct (Z.eq_dec p 0); [contradiction|].
  rewrite Hn.
  destruct (Z.eq_dec (RCMap.counts M p) 1); [contradiction|].
  rewrite RCMap.release_nrm_unfold; cbn; split; reflexivity.
Qed.
Lemma decode_live__left_variable : forall M p tr,
  decode_type M p tr -> exists n, RCMap.nodes M p = Some n.
Proof.
  intros M p tr H; destruct tr; cbn in H; firstorder.
Qed.
Lemma decode_var__left_variable : forall M p tr n,
  decode_type M p tr -> RCMap.nodes M p = Some n -> node_tag n = 3 ->
  exists v, tr = TVar v /\ n = Node 3 v 0.
Proof.
  intros M p tr n Hd Hn Htag.
  change (TypeRCMap.nodes M p = Some n) in Hn.
  destruct tr; cbn in Hd;
  repeat match goal with H : exists _, _ |- _ => destruct H as [? H]
  | H : _ /\ _ |- _ => destruct H end;
  match goal with H : TypeRCMap.nodes M p = Some _ |- _ =>
    first [constr_eq H Hn; fail 1 | rewrite Hn in H; inversion H; subst]
  end; cbn in *; try discriminate; eauto.
Qed.
Lemma retain_identify__left_variable : forall M p M',
  retain_rel M p M' -> M' = RCMap.retain M p.
Proof.
  unfold retain_rel, RCMap.retain_program; cbn.
  intros M p M' [u [st [Ha Hr]]]; destruct Hr; congruence.
Qed.
Lemma variable_repr_empty__left_variable : forall s n v,
  repr_rel_id s n (TVar v) -> s v = None.
Proof.
  intros s n v H; remember (TVar v) as t eqn:Ht.
  induction H; inversion Ht; subst; auto; contradiction.
Qed.
Lemma variable_self_empty__left_variable : forall s v,
  repr_rel_node s (TVar v) (TVar v) -> s v = None.
Proof.
  intros s v H; inversion H; subst.
  - eapply variable_repr_empty__left_variable; eauto.
  - contradiction.
Qed.
Lemma left_retain_capacity__left_variable : forall M s p q v tr,
  rc_valid M -> RCMap.nodes M p = Some (Node 3 v 0) ->
  decode_type M q tr -> not_occur_final s v tr ->
  rc_capacity 2 M s p q -> RCMap.counts M q < 2147483647.
Proof.
  intros M s p q v tr Hv Hp Hd Ho Hcap.
  destruct (decode_live__left_variable M q tr Hd) as [n Hn].
  assert (Hq : q <> 0).
  { destruct Hv as [[_ [_ [_ [_ [Hl _]]]]] _]. exact (proj1 (Hl q n Hn)). }
  destruct (Z_lt_ge_dec (RCMap.counts M q) 2147483647); [assumption|].
  exfalso; apply Hcap; apply infer_err_unfold.
  unfold infer_rec; type_rcmap_reduce; rewrite Hp,Hn; cbn [node_tag node_a].
  cbn -[RCMap.retain_program]. right; right.
  exists tr,tt; split; [reflexivity|].
  right; exists tt,tt; split; [split; [reflexivity|auto]|].
  left; cbn; left; intro H; destruct H; type_rcmap_reduce; contradiction || lia.
Qed.
Lemma left_variable_normal__left_variable : forall M s p q v tr M',
  RCMap.nodes M p = Some (Node 3 v 0) -> decode_type M q tr ->
  not_occur_final s v tr -> retain_rel M q M' ->
  infer_result 2 M s p q 0 (rc_publish M' q) (sol_update s v tr).
Proof.
  intros M s p q v tr M' Hp Hd Ho Hr.
  destruct (decode_live__left_variable M q tr Hd) as [n Hn].
  unfold infer_result.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as Hu.
  destruct (Hu 2 p q M s) as [Hnormal Herr].
  apply Hnormal; unfold infer_rec; type_rcmap_reduce; rewrite Hp,Hn; cbn [node_tag node_a].
  cbn -[RCMap.retain_program]. right.
  exists tr,tt; split; [reflexivity|].
  exists tt,tt; split; [split; [reflexivity|auto]|].
  exists M',tt; split; [exact Hr|split; reflexivity].
Qed.
Lemma close_second__left_variable : forall M p q n,
  p <> q -> RCMap.nodes M q = Some n ->
  store_node M q n ** store_world_except2 M p q |-- store_world_except M p.
Proof.
  intros M p q n Hpq Hn.
  unfold store_world_except2, store_world_except.
  set (m := fun r => if Z.eq_dec p r then None else RCMap.nodes M r).
  assert (Hm : m q = Some n) by (unfold m; destruct (Z.eq_dec p q); congruence).
  assert (Hp : m p = None) by (unfold m; destruct (Z.eq_dec p p); congruence).
  change (store_node M q n ** store_map_missing_i (store_node M) m q |--
    store_map_missing_i (store_node M) (RCMap.nodes M) p).
  sep_apply_l_atomic (store_map_merge (store_node M) q n m Hm).
  sep_apply (store_map_equiv_store_map_missing (store_node M) m p Hp).
  rewrite (store_map_missing_i_equiv (store_node M) m (RCMap.nodes M) p).
  - cancel.
  - intros a Ha; unfold m; destruct (Z.eq_dec p a); congruence.
Qed.
Lemma decoded_node__variable_failure : forall M p tr,
  store_type M p tr -> exists n, RCMap.nodes M p = Some n.
Proof.
  intros M p tr H; destruct tr; cbn in H;
    unfold store_type in H; cbn in H;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    eauto; intuition eauto.
Qed.
Lemma decoded_not_var__variable_failure : forall M p tr,
  store_type M p tr -> not_var tr ->
  exists n, RCMap.nodes M p = Some n /\ node_tag n <> 3.
Proof.
  intros M p tr H Hnv; destruct tr; cbn in Hnv; try contradiction;
    unfold store_type in H; cbn in H.
  - eexists; split; [exact H|cbn; lia].
  - destruct H as [a [b [H _]]]; eexists; split; [exact H|cbn; lia].
  - destruct H as [a [b [H _]]]; eexists; split; [exact H|cbn; lia].
Qed.
Lemma infer_normal_unfold__variable_failure : forall stage p q M s out,
  MonadErr.nrm (infer stage p q M s) tt out tt <->
  MonadErr.nrm (infer_rec infer stage p q M s) tt out tt.
Proof.
  intros stage p q M s out.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H stage p q M s) as [Hn He]. apply Hn.
Qed.
Lemma variable_failure_right__variable_failure : forall M s p q v tr,
  store_type M p tr -> not_var tr -> node_at M q (Node 3 v 0) ->
  infer_result 2 M s p q 1 M s.
Proof.
  intros M s p q v tr Htr Hnv Hq.
  destruct (decoded_not_var__variable_failure M p tr Htr Hnv) as [np [Hp Htag]].
  unfold infer_result; rewrite infer_normal_unfold__variable_failure.
  unfold infer_rec; unfold node_at in Hq; type_rcmap_reduce; rewrite Hp, Hq.
  cbn -[Z.eq_dec].
  destruct (Z.eq_dec 2 0), (Z.eq_dec 2 1); try lia.
  destruct (Z.eq_dec (node_tag np) 3); [contradiction|].
  destruct (Z.eq_dec 3 3); [|contradiction].
  left; split; reflexivity.
Qed.
Lemma variable_failure_left__variable_failure : forall M s p q v tr,
  store_type M q tr -> node_at M p (Node 3 v 0) ->
  infer_result 2 M s p q 1 M s.
Proof.
  intros M s p q v tr Htr Hp.
  destruct (decoded_node__variable_failure M q tr Htr) as [nq Hq].
  unfold infer_result; rewrite infer_normal_unfold__variable_failure.
  unfold infer_rec; unfold node_at in Hp; type_rcmap_reduce; rewrite Hp, Hq.
  cbn -[Z.eq_dec].
  destruct (Z.eq_dec 2 0), (Z.eq_dec 2 1); try lia.
  destruct (Z.eq_dec 3 3); [|contradiction].
  left; split; reflexivity.
Qed.
Lemma close_variable_payload__variable_failure : forall M p v,
  node_at M p (Node 3 v 0) ->
  (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> v) **
  store_world_without_payload M p (Node 3 v 0) |-- store_world M.
Proof.
  intros M p v H.
  unfold store_world_without_payload, store_world, store_world_except.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node M) p (Node 3 v 0) (RCMap.nodes M) H).
  unfold store_node, store_node_payload; type_rcmap_reduce; cbn; cancel; reflexivity.
Qed.
Lemma decoded_node__stage0_direct : forall M p tr,
  store_type M p tr -> exists n, node_at M p n.
Proof.
  intros M p tr H; destruct tr; cbn in H;
    unfold store_type in H; cbn in H;
    unfold node_at; eauto.
  - destruct H as [l [r [H _]]]; eauto.
  - destruct H as [l [r [H _]]]; eauto.
Qed.
Lemma empty_slot__stage0_direct : forall s v,
  (forall tr, ~ solution_at s v tr) -> s v = None.
Proof.
  intros s v H; destruct (s v) eqn:Hs; [|reflexivity].
  exfalso; apply (H t); exact Hs.
Qed.
Lemma direct_stage_body__stage0_direct : forall M s p q np nq,
  node_at M p np -> node_at M q nq ->
  (node_tag np <> 3 \/ s (node_a np) = None) ->
  infer_rec infer 0 p q M s = infer 1 p q M s.
Proof.
  intros M s p q np nq Hp Hq Hbranch.
  unfold node_at in Hp,Hq; unfold infer_rec; rewrite Hp,Hq.
  destruct (Z.eq_dec 0 0); [|contradiction].
  destruct (Z.eq_dec (node_tag np) 3); [|reflexivity].
  destruct Hbranch as [Hne|Hnone]; [contradiction|rewrite Hnone; reflexivity].
Qed.
Lemma direct_stage_result__stage0_direct : forall M s p q np tr r M' s',
  node_at M p np -> store_type M q tr ->
  (node_tag np <> 3 \/ s (node_a np) = None) ->
  infer_result 1 M s p q r M' s' -> infer_result 0 M s p q r M' s'.
Proof.
  intros M s p q np tr r M' s' Hp Hq Hb Hr.
  destruct (decoded_node__stage0_direct M q tr Hq) as [nq Hnq].
  unfold infer_result in *.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as Hunfold.
  destruct (Hunfold 0 p q M s) as [Hn He].
  apply (proj2 (Hn tt (r,M',s') tt)).
  change (MonadErr.nrm (infer_rec infer 0 p q M s) tt (r,M',s') tt).
  rewrite (direct_stage_body__stage0_direct M s p q np nq Hp Hnq Hb).
  exact Hr.
Qed.
Lemma direct_stage_capacity__stage0_direct : forall M s p q np tr,
  node_at M p np -> store_type M q tr ->
  (node_tag np <> 3 \/ s (node_a np) = None) ->
  rc_capacity 0 M s p q -> rc_capacity 1 M s p q.
Proof.
  intros M s p q np tr Hp Hq Hb Hcap.
  destruct (decoded_node__stage0_direct M q tr Hq) as [nq Hnq].
  unfold rc_capacity in *; rewrite infer_err_unfold in Hcap.
  rewrite (direct_stage_body__stage0_direct M s p q np nq Hp Hnq Hb) in Hcap.
  exact Hcap.
Qed.
Lemma decoded_nonvariable__stage0_direct : forall M p np tr,
  node_at M p np -> store_type M p tr -> node_tag np <> 3 -> not_var tr.
Proof.
  intros M p np tr Hp Htr Htag.
  destruct tr; cbn; auto.
  unfold store_type in Htr; cbn in Htr; unfold node_at in Hp.
  rewrite Hp in Htr; inversion Htr; subst; cbn in Htag; contradiction.
Qed.
Lemma decode_live__stage1_direct : forall M p tr,
  store_type M p tr -> exists n, RCMap.nodes M p = Some n.
Proof.
  intros M p tr H; destruct tr; cbn [store_type decode_type] in H.
  - eauto.
  - eauto.
  - destruct H as [a [b [H _]]]; eauto.
  - destruct H as [a [b [H _]]]; eauto.
Qed.
Lemma direct_stage_step__stage1_direct : forall M s p q tr nq,
  store_type M p tr -> node_at M q nq ->
  (node_tag nq <> 3 \/ s (node_a nq) = None) ->
  infer_rec infer 1 p q M s = infer 2 p q M s.
Proof.
  intros M s p q tr nq Hp Hq Hg.
  destruct (decode_live__stage1_direct M p tr Hp) as [np Hnp].
  unfold node_at in Hq; unfold infer_rec; type_rcmap_reduce; rewrite Hnp, Hq.
  cbn; destruct (Z.eq_dec (node_tag nq) 3) as [Ht|Ht]; [|reflexivity].
  destruct Hg as [Hg|Hg]; [contradiction|rewrite Hg; reflexivity].
Qed.
Lemma direct_result__stage1_direct : forall M s p q tr nq r M' s',
  store_type M p tr -> node_at M q nq ->
  (node_tag nq <> 3 \/ s (node_a nq) = None) ->
  infer_result 2 M s p q r M' s' -> infer_result 1 M s p q r M' s'.
Proof.
  intros M s p q tr nq r M' s' Hp Hq Hg Hr.
  unfold infer_result in *.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H 1 p q M s) as [Hn He].
  apply (proj2 (Hn tt (r,M',s') tt)).
  change (MonadErr.nrm (infer_rec infer 1 p q M s) tt (r,M',s') tt).
  rewrite (direct_stage_step__stage1_direct M s p q tr nq Hp Hq Hg).
  exact Hr.
Qed.
Lemma direct_capacity__stage1_direct : forall M s p q tr nq,
  store_type M p tr -> node_at M q nq ->
  (node_tag nq <> 3 \/ s (node_a nq) = None) ->
  rc_capacity 1 M s p q -> rc_capacity 2 M s p q.
Proof.
  intros M s p q tr nq Hp Hq Hg Hcap.
  unfold rc_capacity in *; intro He; apply Hcap.
  apply (proj2 (infer_err_unfold 1 p q M s)).
  rewrite (direct_stage_step__stage1_direct M s p q tr nq Hp Hq Hg).
  exact He.
Qed.
Lemma empty_slot__stage1_direct : forall s v,
  (forall tr, ~ solution_at s v tr) -> s v = None.
Proof.
  intros s v H; destruct (s v) eqn:Hs; [|reflexivity].
  exfalso; apply (H t); exact Hs.
Qed.
Lemma repr_nonvar__stage1_direct : forall M p tr n s,
  store_type M p tr -> node_at M p n -> node_tag n <> 3 ->
  repr_rel_node s tr tr.
Proof.
  intros M p tr n s Hd Hn Htag; apply repr_rel_node_not_var.
  destruct tr; cbn [not_var]; try exact I.
  unfold store_type in Hd; cbn [decode_type] in Hd.
  unfold node_at in Hn; rewrite Hd in Hn; inversion Hn; subst.
  cbn in Htag; contradiction.
Qed.
Lemma repr_empty__stage1_direct : forall M p tr v s,
  store_type M p tr -> node_at M p (Node 3 v 0) -> s v = None ->
  repr_rel_node s tr tr.
Proof.
  intros M p tr v s Hd Hn Hs.
  unfold store_type in Hd; unfold node_at in Hn.
  destruct tr; cbn [decode_type] in Hd.
  - rewrite Hd in Hn; inversion Hn; subst.
    apply repr_rel_node_var; apply repr_rel_var; exact Hs.
  - congruence.
  - destruct Hd as [a [b [Hd _]]]; congruence.
  - destruct Hd as [a [b [Hd _]]]; congruence.
Qed.
Lemma decode_node__representative_entry : forall M p tr,
  store_type M p tr -> exists n, RCMap.nodes M p = Some n.
Proof.
  intros M p tr H; destruct tr; cbn in H; unfold store_type in H; cbn in H;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    eauto; intuition eauto.
Qed.
Lemma repr_terminal_self__representative_entry : forall s t u,
  repr_rel_node s t u -> repr_rel_node s u u.
Proof.
  intros s t u H; destruct H.
  - induction H.
    + apply repr_rel_node_var; constructor; assumption.
    + apply repr_rel_node_not_var; assumption.
    + exact IHrepr_rel_id.
  - apply repr_rel_node_not_var; assumption.
Qed.
Lemma repr_headroom__representative_entry : forall M s v,
  rc_valid M -> ~ MonadErr.err (repr_choice M s v) tt ->
  forall p tr, store_type M p tr -> repr_rel_node s (TVar v) tr ->
  rc_count M p < 2147483647.
Proof.
  intros M s v Hv Hsafe p tr Hd Hr.
  destruct (decode_node__representative_entry M p tr Hd) as [n Hn].
  assert (Hp : p <> 0).
  { destruct Hv as [[_ [_ [_ [_ [Hlive _]]]]] _].
    exact (proj1 (Hlive p n Hn)). }
  destruct (Z_lt_ge_dec (rc_count M p) 2147483647); [assumption|].
  exfalso; apply Hsafe; unfold repr_choice; cbn.
  right; exists p,tt; split; [reflexivity|].
  right; exists tr,tt; split; [reflexivity|].
  right; exists tt,tt; split; [split; [reflexivity|auto]|].
  left; unfold RCMap.retain_program; cbn; left.
  change (~ (p = 0 \/ RCMap.counts M p < 2147483647)).
  unfold rc_count in *; type_rcmap_reduce; lia.
Qed.
Lemma repr_entry_left__representative_entry : forall M s p q v tr,
  node_at M p (Node 3 v 0) -> store_type M q tr ->
  s v <> None -> rc_capacity 0 M s p q ->
  ~ MonadErr.err (repr_choice M s v) tt /\
  forall p' M', repr_result M s v p' M' -> rc_capacity 1 M' s p' q.
Proof.
  intros M s p q v tr Hp Hq Hslot Hcap.
  destruct (decode_node__representative_entry M q tr Hq) as [nq Hnq].
  unfold rc_capacity in Hcap; rewrite infer_err_unfold in Hcap.
  unfold infer_rec in Hcap; unfold node_at in Hp;
    type_rcmap_reduce; rewrite Hp,Hnq in Hcap.
  cbn -[Z.eq_dec Monad.bind] in Hcap.
  destruct (Z.eq_dec 0 0); [|contradiction].
  destruct (Z.eq_dec 3 3); [|contradiction].
  destruct (s v); [|contradiction].
  split.
  - intro He; apply Hcap; left; exact He.
  - intros p' M' Hrepr He; apply Hcap; right.
    exists (p',M'),tt; split; [exact Hrepr|].
    left; exact He.
Qed.
Lemma repr_entry_right__representative_entry : forall M s p q v tr,
  node_at M q (Node 3 v 0) -> store_type M p tr ->
  s v <> None -> rc_capacity 1 M s p q ->
  ~ MonadErr.err (repr_choice M s v) tt /\
  forall q' M', repr_result M s v q' M' -> rc_capacity 2 M' s p q'.
Proof.
  intros M s p q v tr Hq Hp Hslot Hcap.
  destruct (decode_node__representative_entry M p tr Hp) as [np Hnp].
  unfold rc_capacity in Hcap; rewrite infer_err_unfold in Hcap.
  unfold infer_rec in Hcap; unfold node_at in Hq;
    type_rcmap_reduce; rewrite Hnp,Hq in Hcap.
  cbn -[Z.eq_dec Monad.bind] in Hcap.
  destruct (Z.eq_dec 1 0); [lia|].
  destruct (Z.eq_dec 1 1); [|contradiction].
  destruct (Z.eq_dec 3 3); [|contradiction].
  destruct (s v); [|contradiction].
  split.
  - intro He; apply Hcap; left; exact He.
  - intros q' M' Hrepr He; apply Hcap; right.
    exists (q',M'),tt; split; [exact Hrepr|].
    left; exact He.
Qed.
Lemma decoded_node_exists__stage0_world : forall M p tr,
  store_type M p tr -> exists n, node_at M p n.
Proof.
  intros M p tr H; destruct tr; cbn in H;
    unfold store_type in H; cbn in H;
    try (eexists; exact H);
    destruct H as [a [b [H _]]]; eexists; exact H.
Qed.
Lemma decoded_variable_shape__stage0_world : forall M p tr n,
  store_type M p tr -> node_at M p n -> node_tag n = 3 ->
  exists v, n = Node 3 v 0.
Proof.
  intros M p tr n Hd Hn Htag.
  unfold store_type in Hd; unfold node_at in Hn.
  destruct tr; cbn in Hd.
  - rewrite Hd in Hn; inversion Hn; subst; eauto.
  - rewrite Hd in Hn; inversion Hn; subst; discriminate.
  - destruct Hd as [a [b [Hd _]]].
    rewrite Hd in Hn; inversion Hn; subst; discriminate.
  - destruct Hd as [a [b [Hd _]]].
    rewrite Hd in Hn; inversion Hn; subst; discriminate.
Qed.
Lemma world_close__stage0_world : forall M p n,
  node_at M p n ->
  store_node M p n ** store_world_except M p |-- store_world M.
Proof.
  intros M p n H.
  unfold store_world, store_world_except.
  type_rcmap_reduce.
  sep_apply (store_map_merge (store_node M) p n (RCMap.nodes M) H).
  cancel; reflexivity.
Qed.
Lemma tag_close__stage0_world : forall M p n,
  node_at M p n ->
  (&(p # "atype" ->ₛ "t") # Int |-> node_tag n) **
    store_world_without_tag M p n |-- store_world M.
Proof.
  intros M p n H.
  sep_apply_r_atomic (world_close__stage0_world M p n H).
  unfold store_world_without_tag, store_node, store_node_payload.
  type_rcmap_reduce.
  fold (store_payload_aux p n).
  cancel (&(p # "atype" ->ₛ "t") # Int |-> node_tag n).
  cancel (&(p # "atype" ->ₛ "refcnt") # Int |-> RCMap.counts M p).
  cancel (store_world_except M p).
  change (store_payload_aux p n |-- store_payload_aux p n).
  cancel; reflexivity.
Qed.
Lemma var_close__stage0_world : forall M p v,
  node_at M p (Node 3 v 0) ->
  (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> v) **
    store_world_without_payload M p (Node 3 v 0) |-- store_world M.
Proof.
  intros M p v H.
  sep_apply_r_atomic (world_close__stage0_world M p (Node 3 v 0) H).
  unfold store_world_without_payload, store_node, store_node_payload; cbn.
  type_rcmap_reduce.
  cancel (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> v).
  cancel (&(p # "atype" ->ₛ "t") # Int |-> 3).
  cancel (&(p # "atype" ->ₛ "refcnt") # Int |-> RCMap.counts M p).
  cancel; reflexivity.
Qed.
Lemma tag_open__stage0_world : forall M p n,
  node_at M p n -> store_world M |--
  (&(p # "atype" ->ₛ "t") # Int |-> node_tag n) **
    store_world_without_tag M p n.
Proof.
  intros M p n H; sep_apply (store_world_open M p n H).
  unfold store_node, store_node_payload, store_world_without_tag.
  type_rcmap_reduce.
  cancel (&(p # "atype" ->ₛ "t") # Int |-> node_tag n).
  cancel (&(p # "atype" ->ₛ "refcnt") # Int |-> RCMap.counts M p).
  cancel (store_world_except M p).
  change (store_payload_aux p n |-- store_payload_aux p n).
  cancel; reflexivity.
Qed.
Lemma decoded_node__stage1_world : forall M p tr,
  store_type M p tr -> exists n, node_at M p n.
Proof.
  intros M p tr H; destruct tr as [z|z|a b|a b]; cbn in H.
  - exists (Node 3 z 0); exact H.
  - exists (Node 0 z 0); exact H.
  - destruct H as [l [r [H _]]]; exists (Node 2 l r); exact H.
  - destruct H as [l [r [H _]]]; exists (Node 1 l r); exact H.
Qed.
Lemma variable_node__stage1_world : forall M p tr n,
  rc_valid M -> store_type M p tr -> node_at M p n -> node_tag n = 3 ->
  exists v, n = Node 3 v 0 /\ 0 <= v /\ v < 100.
Proof.
  intros M p tr n [_ Hv] Hd Hn Ht.
  unfold node_at in Hn; unfold store_type in Hd.
  destruct tr as [z|z|a b|a b]; cbn in Hd.
  - rewrite Hd in Hn; inversion Hn; subst n.
    specialize (Hv p (Node 3 z 0) Hd).
    unfold payload_valid in Hv; cbn in Hv.
    exists z; split; [reflexivity | tauto].
  - rewrite Hd in Hn; inversion Hn; subst n; discriminate Ht.
  - destruct Hd as [l [r [Hd _]]].
    rewrite Hd in Hn; inversion Hn; subst n; discriminate Ht.
  - destruct Hd as [l [r [Hd _]]].
    rewrite Hd in Hn; inversion Hn; subst n; discriminate Ht.
Qed.
Lemma world_tag_close__stage1_world : forall M p n,
  node_at M p n ->
  (&(p # "atype" ->ₛ "t") # Int |-> node_tag n) **
  store_world_without_tag M p n |-- store_world M.
Proof.
  intros M p n H.
  unfold store_world, store_world_without_tag, store_world_except.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node M) p n (RCMap.nodes M) H).
  unfold store_node, store_node_payload, store_payload_aux.
  type_rcmap_reduce.
  cancel; reflexivity.
Qed.
Lemma world_var_close__stage1_world : forall M p v,
  node_at M p (Node 3 v 0) ->
  (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> v) **
  store_world_without_payload M p (Node 3 v 0) |-- store_world M.
Proof.
  intros M p v H.
  unfold store_world, store_world_without_payload, store_world_except.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node M) p (Node 3 v 0) (RCMap.nodes M) H).
  unfold store_node, store_node_payload; type_rcmap_reduce; cbn; cancel; reflexivity.
Qed.
Lemma decoded_node__world_reopen : forall M p tr,
  store_type M p tr -> exists n, node_at M p n.
Proof.
  intros M p tr H; destruct tr; cbn in H.
  - eexists; exact H.
  - eexists; exact H.
  - destruct H as [a [b [H _]]]; eexists; exact H.
  - destruct H as [a [b [H _]]]; eexists; exact H.
Qed.
Lemma positive_old_node__world_reopen : forall M p,
  rc_valid M -> rc_count M p > 0 -> exists n, node_at M p n.
Proof.
  intros M p [Hv Hp] Hpos.
  destruct (RCMap.nodes M p) as [n|] eqn:Hn.
  - exists n; exact Hn.
  - destruct Hv as [_ [_ [_ [_ [_ [Hd _]]]]]].
    specialize (Hd p Hn); unfold rc_count in Hpos; type_rcmap_reduce; lia.
Qed.
Lemma world_open_two__world_reopen : forall M p np q nq,
  node_at M p np -> node_at M q nq -> p <> q ->
  store_world M |--
  store_node M p np ** store_node M q nq ** store_world_except2 M p q.
Proof.
  intros M p np q nq Hp Hq Hneq.
  sep_apply (store_world_open M p np Hp).
  unfold store_world_except, store_world_except2.
  unfold node_at in Hp, Hq; type_rcmap_reduce.
  set (deleted := fun r => if Z.eq_dec p r then None else RCMap.nodes M r).
  assert (Heq : forall r, r <> p -> RCMap.nodes M r = deleted r).
  { intros r Hr; unfold deleted; destruct (Z.eq_dec p r); congruence. }
  sep_apply (proj1 (store_map_missing_i_equiv (store_node M)
    (RCMap.nodes M) deleted p Heq)).
  assert (Hdel : deleted p = None).
  { unfold deleted; destruct (Z.eq_dec p p); congruence. }
  sep_apply (store_map_missing_equiv_store_map (store_node M) deleted p Hdel).
  assert (Hqdel : deleted q = Some nq).
  { unfold deleted; destruct (Z.eq_dec p q); congruence. }
  sep_apply (store_map_split (store_node M) q nq deleted Hqdel).
  fold deleted; cancel.
  change (store_map_missing_i (store_node M) deleted q |--
    store_map_missing_i (store_node M) deleted q).
  cancel (store_map_missing_i (store_node M) deleted q).
Qed.
Lemma nodes_close_two__arrow_payload_close : forall M p np q nq,
  p <> q -> node_at M p np -> node_at M q nq ->
  store_node M p np ** store_node M q nq ** store_world_except2 M p q
  |-- store_world M.
Proof.
  intros M p np q nq Hneq Hp Hq.
  unfold node_at in Hp, Hq.
  unfold store_world_except2, store_world.
  type_rcmap_reduce.
  assert (Hq' : (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) q = Some nq).
  { destruct (Z.eq_dec p q); congruence. }
  assert (Hp' : (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) p = None).
  { destruct (Z.eq_dec p p); congruence. }
  assert (Heq : forall r, r <> p ->
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) r = RCMap.nodes M r).
  { intros r Hr; destruct (Z.eq_dec p r); congruence. }
  sep_apply (store_map_merge (store_node M) q nq
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) Hq').
  sep_apply (store_map_equiv_store_map_missing (store_node M)
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) p Hp').
  rewrite (store_map_missing_i_equiv (store_node M)
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r)
    (RCMap.nodes M) p Heq).
  sep_apply (store_map_merge (store_node M) p np (RCMap.nodes M) Hp).
  cancel; reflexivity.
Qed.
Lemma payload_close_one__arrow_payload_close : forall M p n,
  node_at M p n -> node_tag n = 1 ->
  (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> node_a n) **
  (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> node_b n) **
  store_world_without_payload M p n |-- store_world M.
Proof.
  intros M p n Hnode Htag.
  unfold store_world, store_world_without_payload, store_world_except.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node M) p n (RCMap.nodes M) Hnode).
  unfold store_node, store_node_payload; type_rcmap_reduce; rewrite Htag.
  cbn; sepcon_assoc_change; cancel; reflexivity.
Qed.
Lemma payload_close_two__arrow_payload_close : forall M p np q nq,
  p <> q -> node_at M p np -> node_at M q nq ->
  node_tag np = 1 -> node_tag nq = 1 ->
  (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> node_a np) **
  (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> node_b np) **
  (&(q # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> node_a nq) **
  (&(q # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> node_b nq) **
  store_world_without_payloads2 M p np q nq |-- store_world M.
Proof.
  intros M p np q nq Hneq Hp Hq Htp Htq.
  sep_apply_r_atomic (nodes_close_two__arrow_payload_close M p np q nq Hneq Hp Hq).
  unfold store_world_without_payloads2, store_node, store_node_payload.
  rewrite Htp, Htq; sepcon_assoc_change; cancel; reflexivity.
Qed.
Lemma nodes_close_two__app_payload_close : forall M p np q nq,
  p <> q -> node_at M p np -> node_at M q nq ->
  store_node M p np ** store_node M q nq ** store_world_except2 M p q
  |-- store_world M.
Proof.
  intros M p np q nq Hneq Hp Hq.
  unfold node_at in Hp, Hq.
  unfold store_world_except2, store_world.
  type_rcmap_reduce.
  assert (Hq' : (if Z.eq_dec p q then None else RCMap.nodes M q) = Some nq).
  { destruct (Z.eq_dec p q); congruence. }
  sep_apply (store_map_merge (store_node M) q nq
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) Hq').
  assert (Hp' : (if Z.eq_dec p p then None else RCMap.nodes M p) = None).
  { destruct (Z.eq_dec p p); congruence. }
  sep_apply (store_map_equiv_store_map_missing (store_node M)
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) p Hp').
  assert (Heq : forall r, r <> p ->
    (if Z.eq_dec p r then None else RCMap.nodes M r) = RCMap.nodes M r).
  { intros r Hr; destruct (Z.eq_dec p r); congruence. }
  rewrite (store_map_missing_i_equiv (store_node M)
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r)
    (RCMap.nodes M) p Heq).
  sep_apply (store_map_merge (store_node M) p np (RCMap.nodes M) Hp).
  cancel; reflexivity.
Qed.
Lemma payload_close_one__app_payload_close : forall M p n,
  node_at M p n -> node_tag n = 2 ->
  (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> node_a n) **
  (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> node_b n) **
  store_world_without_payload M p n |-- store_world M.
Proof.
  intros M p n Hp Htag.
  unfold store_world, store_world_without_payload, store_world_except.
  type_rcmap_reduce.
  sep_apply_r_atomic (store_map_merge (store_node M) p n (RCMap.nodes M) Hp).
  unfold store_node, store_node_payload; type_rcmap_reduce; rewrite Htag.
  cbn; sepcon_assoc_change; cancel; reflexivity.
Qed.
Lemma payload_close_two__app_payload_close : forall M p np q nq,
  p <> q -> node_at M p np -> node_at M q nq ->
  node_tag np = 2 -> node_tag nq = 2 ->
  (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> node_a np) **
  (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> node_b np) **
  (&(q # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> node_a nq) **
  (&(q # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> node_b nq) **
  store_world_without_payloads2 M p np q nq |-- store_world M.
Proof.
  intros M p np q nq Hneq Hp Hq Hpt Hqt.
  sep_apply_r_atomic (nodes_close_two__app_payload_close M p np q nq Hneq Hp Hq).
  unfold store_node, store_node_payload, store_world_without_payloads2.
  rewrite Hpt, Hqt; cbn; sepcon_right_assoc; cancel; reflexivity.
Qed.
Lemma infer_normal_unfold__atom_and_mismatch : forall st p q M s r M' s',
  infer_result st M s p q r M' s' <->
  MonadErr.nrm (infer_rec infer st p q M s) tt (r,M',s') tt.
Proof.
  intros st p q M s r M' s'; unfold infer_result, infer.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H st p q M s) as [Hn He]. apply Hn.
Qed.
Lemma atom_normal__atom_and_mismatch : forall M s p q np nq,
  node_at M p np -> node_at M q nq ->
  node_tag np = 0 -> node_tag nq = 0 ->
  infer_result 2 M s p q
    (if Z.eq_dec (node_a np) (node_a nq) then 0 else 2) M s.
Proof.
  intros M s p q np nq Hp Hq Htp Htq.
  apply infer_normal_unfold__atom_and_mismatch.
  unfold infer_rec; unfold node_at in Hp,Hq; rewrite Hp,Hq,Htp,Htq.
  cbn -[Z.eq_dec]. destruct (Z.eq_dec 2 0), (Z.eq_dec 2 1),
    (Z.eq_dec 0 3), (Z.eq_dec 0 0); try congruence.
  cbn. destruct (Z.eq_dec (node_a np) (node_a nq)); split; reflexivity.
Qed.
Lemma mismatch_normal__atom_and_mismatch : forall M s p q np nq,
  node_at M p np -> node_at M q nq ->
  node_tag np <> 3 -> node_tag nq <> 3 -> node_tag np <> node_tag nq ->
  infer_result 2 M s p q 2 M s.
Proof.
  intros M s p q np nq Hp Hq Htp Htq Hneq.
  apply infer_normal_unfold__atom_and_mismatch.
  unfold infer_rec; unfold node_at in Hp,Hq; rewrite Hp,Hq.
  destruct (Z.eq_dec 2 0), (Z.eq_dec 2 1),
    (Z.eq_dec (node_tag np) 3), (Z.eq_dec (node_tag nq) 3),
    (Z.eq_dec (node_tag np) (node_tag nq)); try congruence.
  split; reflexivity.
Qed.
Lemma decode_atom__atom_and_mismatch : forall M p n tr,
  node_at M p n -> node_tag n = 0 -> store_type M p tr -> tr = TAtom (node_a n).
Proof.
  intros M p n tr Hn Htag Htr.
  destruct tr; unfold store_type in Htr; cbn in Htr;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    unfold node_at in Hn;
    match goal with H : TypeRCMap.nodes M p = Some _ |- _ =>
      rewrite Hn in H; inversion H; subst end; cbn in *; congruence.
Qed.
Lemma erased_world_missing__atom_and_mismatch : forall M p,
  store_map (store_node M) (fun r => if Z.eq_dec p r then None else RCMap.nodes M r)
  |-- store_world_except M p.
Proof.
  intros M p; unfold store_map, store_world_except, store_map_missing_i.
  type_rcmap_reduce.
  Intros l. Exists l.
  split_pure_spatial.
  - match goal with |- iter_sepcon ?xs |-- iter_sepcon ?ys =>
      assert (Heq : xs = ys) end.
    { apply map_ext_in; intros r Hr. apply H in Hr. destruct Hr as [n Hn].
      destruct (Z.eq_dec p r); [discriminate|reflexivity]. }
    rewrite Heq. cancel.
  -
  split_pures; dump_pre_spatial; [|assumption].
  intro r; rewrite H. destruct (Z.eq_dec p r); subst; split; intros HH;
    try destruct HH as [n HH]; try discriminate; firstorder congruence.
Qed.
Lemma world_close__atom_and_mismatch : forall M p n,
  node_at M p n -> store_node M p n ** store_world_except M p |-- store_world M.
Proof.
  intros M p n Hn; unfold node_at in Hn; unfold store_world,store_world_except.
  type_rcmap_reduce.
  sep_apply (store_map_merge (store_node M) p n (RCMap.nodes M) Hn). cancel; reflexivity.
Qed.
Lemma world_close2__atom_and_mismatch : forall M p q np nq,
  node_at M p np -> node_at M q nq -> p <> q ->
  store_node M p np ** store_node M q nq ** store_world_except2 M p q |-- store_world M.
Proof.
  intros M p q np nq Hp Hq Hneq.
  assert (Hq': (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) q = Some nq).
  { destruct (Z.eq_dec p q); [contradiction|exact Hq]. }
  unfold store_world_except2.
  type_rcmap_reduce.
  sep_apply (store_map_merge (store_node M) q nq
    (fun r => if Z.eq_dec p r then None else RCMap.nodes M r) Hq').
  sep_apply (erased_world_missing__atom_and_mismatch M p).
  sep_apply (world_close__atom_and_mismatch M p np Hp). cancel; reflexivity.
Qed.
Lemma payload_aux_eq__atom_and_mismatch : forall p n,
  store_node_payload p n =
  ((&(p # "atype" ->ₛ "t") # Int |-> node_tag n) ** store_payload_aux p n).
Proof. intros; reflexivity. Qed.


Lemma decoded_atom_tag__atom_and_mismatch : forall M p n tr,
  node_at M p n -> store_type M p tr ->
  node_tag n <> 1 -> node_tag n <> 2 -> node_tag n <> 3 ->
  node_tag n = 0.
Proof.
  intros M p n tr Hn Htr H1 H2 H3.
  destruct tr; unfold store_type in Htr; cbn in Htr;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    unfold node_at in Hn;
    match goal with H : TypeRCMap.nodes M p = Some _ |- _ =>
      rewrite Hn in H; inversion H; subst end; cbn in *; congruence.
Qed.
